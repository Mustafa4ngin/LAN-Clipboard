/*
 * clipboard_watcher.cpp
 *
 * LAN Clipboard – shares text AND images across all devices on the same
 * network, including phones via a built-in HTTPS-compatible web interface.
 *
 * ── Architecture ────────────────────────────────────────────────────────────
 *
 *  Thread 1  localWatcher   polls the local clipboard every second via
 *                            xclip / wl-paste.  On change → stores in
 *                            ClipboardStore and broadcasts over UDP.
 *
 *  Thread 2  udpListener    receives UDP broadcast datagrams from other
 *                            desktop/laptop hosts (port 55765).
 *                            Reassembles fragments → ClipboardStore.
 *
 *  Thread 3  displayThread  every second picks the newest entry across ALL
 *                            devices, prints it, writes it back to the local
 *                            clipboard, and fans out SSE events to phones.
 *
 *  Thread 4  httpServer     bounded thread-pool TCP server on port 8765.
 *                            Caddy reverse-proxies this as HTTPS on :8444.
 *
 * ── HTTP Endpoints ──────────────────────────────────────────────────────────
 *
 *   GET  /            full phone web UI  (HTML + JS, zero external deps)
 *   GET  /clipboard   JSON  {"type":"text"|"image","text":"…","mime":"…",
 *                           "device":"…","ts":N}
 *   POST /clipboard   plain-text body → inject as text clip + UDP broadcast
 *   GET  /image       raw image bytes of the current clipboard image
 *   POST /image       (alias) raw image upload  (same as /image-post)
 *   POST /image-post  raw image bytes (Content-Type = MIME) → store + UDP
 *   GET  /events      SSE stream; pushes JSON on every clipboard change
 *   GET  /ca.crt      Caddy internal CA certificate (for phone trust install)
 *
 * ── UDP Fragment Wire Format ────────────────────────────────────────────────
 *
 *   LANCLIPF\n
 *   <transfer_id>\n     uint64, unique per transfer
 *   <type>\n            "TEXT" or "IMAGE"
 *   <mime>\n            MIME type string
 *   <device_id>\n
 *   <timestamp_ms>\n
 *   <frag_index>\n      0-based fragment number
 *   <frag_total>\n      total fragment count for this transfer
 *   <total_bytes>\n     total reassembled payload size
 *   <frag_len>\n        byte count of this fragment's payload
 *   <raw fragment bytes>  exactly frag_len bytes
 *
 * ── Caddy Setup (for HTTPS on mobile) ───────────────────────────────────────
 *
 *   /etc/caddy/Caddyfile:
 *     { auto_https disable_redirects }
 *     https://10.x.x.x:8444 {
 *       tls internal
 *       reverse_proxy localhost:8765
 *     }
 *
 *   Install the Caddy local CA on the phone:
 *     Visit  https://10.x.x.x:8444/ca.crt  and accept the certificate.
 *
 * ── Build ────────────────────────────────────────────────────────────────────
 *
 *   g++ -std=c++17 -O2 -pthread -Wall -Wextra \
 *       -o clipboard_watcher clipboard_watcher.cpp
 *
 * ── Runtime dependencies ─────────────────────────────────────────────────────
 *
 *   xclip  OR  wl-clipboard  (at least one must be installed)
 *   caddy  (optional, for HTTPS / camera on mobile)
 */

// ─── standard headers ────────────────────────────────────────────────────────
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <list>
#include <map>
#include <unordered_map>
#include <mutex>
#include <condition_variable>
#include <thread>
#include <atomic>
#include <chrono>
#include <random>
#include <functional>
#include <algorithm>
#include <optional>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cctype>
#include <array>
#include <stdexcept>
#include <queue>

// ─── POSIX / networking headers ──────────────────────────────────────────────
#include <unistd.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <signal.h>

// ─── constants ───────────────────────────────────────────────────────────────
static constexpr uint16_t UDP_PORT          = 55765;
static constexpr uint16_t HTTP_PORT         = 8765;
static constexpr size_t   MAX_PACKET        = 65507;   // max safe UDP payload
static constexpr size_t   FRAG_PAYLOAD      = 60000;   // bytes of data per UDP fragment
static constexpr size_t   MAX_IMAGE_BYTES   = 20 * 1024 * 1024; // 20 MB hard cap
static constexpr size_t   MAX_SESSIONS      = 256;     // max concurrent reassembly sessions
static constexpr int      FRAG_TIMEOUT_S    = 10;      // drop incomplete transfers after N s
static constexpr char     FRAG_MAGIC[]      = "LANCLIPF";
static constexpr int      HTTP_POOL_SIZE    = 24;      // max concurrent HTTP worker threads
static constexpr int      HTTP_QUEUE_MAX    = 64;      // max pending accepted connections
// Caddy internal CA – default path written by `caddy trust`
static constexpr char     CADDY_CA_PATH[]   =
    "/var/lib/caddy/.local/share/caddy/pki/authorities/local/root.crt";
// Fallback paths (distro-dependent)
static constexpr char     CADDY_CA_PATH2[]  =
    "/root/.local/share/caddy/pki/authorities/local/root.crt";
static constexpr char     CADDY_CA_PATH3[]  =
    "/home/caddy/.local/share/caddy/pki/authorities/local/root.crt";

// ─── global stop flag ────────────────────────────────────────────────────────
// Set by the SIGINT / SIGTERM handler; every thread loop checks this flag.
static std::atomic<bool> g_stop{false};

static void signalHandler(int /*sig*/) noexcept {
    g_stop.store(true, std::memory_order_relaxed);
}

// ─── helpers: time ───────────────────────────────────────────────────────────
using Clock     = std::chrono::system_clock;
using Ms        = std::chrono::milliseconds;
using TimePoint = Clock::time_point;

static uint64_t nowMs() {
    return static_cast<uint64_t>(
        std::chrono::duration_cast<Ms>(Clock::now().time_since_epoch()).count());
}

// ─── helpers: local clipboard (read) ─────────────────────────────────────────
static std::string runCommand(const std::string& cmd) {
    std::array<char, 4096> buffer{};
    std::string result;
    FILE* pipe = popen(cmd.c_str(), "r");
    if (!pipe) return "";
    while (fgets(buffer.data(), static_cast<int>(buffer.size()), pipe) != nullptr)
        result += buffer.data();
    if (pclose(pipe) == -1) return "";
    return result;
}

static std::string rtrimNewlines(std::string s) {
    while (!s.empty() && (s.back() == '\n' || s.back() == '\r'))
        s.pop_back();
    return s;
}

static std::string getLocalClipboard() {
    std::string data = runCommand("xclip -o -selection clipboard 2>/dev/null");
    if (!data.empty()) return rtrimNewlines(data);
    data = runCommand("wl-paste --no-newline 2>/dev/null");
    if (!data.empty()) return rtrimNewlines(data);
    return "";
}

// ─── helpers: local clipboard (write) ────────────────────────────────────────
/*
 * Writes text to the local clipboard so that remote content is immediately
 * available via Ctrl+V.  Tries xclip first, then wl-copy.
 * Returns true on success.
 */
static bool setLocalClipboard(const std::string& text) {
    // xclip: pipe text into stdin
    {
        FILE* p = popen("xclip -in -selection clipboard 2>/dev/null", "w");
        if (p) {
            fwrite(text.data(), 1, text.size(), p);
            if (pclose(p) == 0) return true;
        }
    }
    // wl-copy: pipe text into stdin
    {
        FILE* p = popen("wl-copy 2>/dev/null", "w");
        if (p) {
            fwrite(text.data(), 1, text.size(), p);
            if (pclose(p) == 0) return true;
        }
    }
    return false;
}

// ─── device identity ─────────────────────────────────────────────────────────
static std::string makeDeviceId() {
    char hostname[256] = "unknown";
    gethostname(hostname, sizeof(hostname));
    return std::string(hostname) + ":" + std::to_string(getpid());
}

// ─── unique transfer ID ───────────────────────────────────────────────────────
static uint64_t makeTransferId() {
    static std::mt19937_64 rng(std::random_device{}());
    return rng();
}

// ─── ClipEntry ────────────────────────────────────────────────────────────────
enum class ClipType { TEXT, IMAGE };

struct ClipEntry {
    ClipType    type        = ClipType::TEXT;
    std::string text;                 // for TEXT entries
    std::vector<uint8_t> imageData;   // for IMAGE entries (raw bytes)
    std::string mime;                 // e.g. "image/png", "image/jpeg"
    uint64_t    timestampMs = 0;
    std::string deviceId;
};

// ─── Base64 encode / decode ───────────────────────────────────────────────────
static const char B64_CHARS[] =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

[[maybe_unused]]
static std::string base64Encode(const uint8_t* data, size_t len) {
    std::string out;
    out.reserve(((len + 2) / 3) * 4);
    for (size_t i = 0; i < len; i += 3) {
        uint32_t b = static_cast<uint32_t>(data[i]) << 16;
        if (i + 1 < len) b |= static_cast<uint32_t>(data[i+1]) << 8;
        if (i + 2 < len) b |= static_cast<uint32_t>(data[i+2]);
        out += B64_CHARS[(b >> 18) & 0x3F];
        out += B64_CHARS[(b >> 12) & 0x3F];
        out += (i + 1 < len) ? B64_CHARS[(b >>  6) & 0x3F] : '=';
        out += (i + 2 < len) ? B64_CHARS[(b      ) & 0x3F] : '=';
    }
    return out;
}

[[maybe_unused]]
static std::vector<uint8_t> base64Decode(const std::string& s) {
    // Build reverse lookup
    static const auto tbl = [](){
        std::array<int,256> t; t.fill(-1);
        for (int i = 0; i < 64; ++i) t[static_cast<unsigned char>(B64_CHARS[i])] = i;
        return t;
    }();

    std::vector<uint8_t> out;
    out.reserve(s.size() * 3 / 4);
    uint32_t buf = 0; int bits = 0;
    for (unsigned char c : s) {
        if (c == '=') break;
        int v = tbl[c];
        if (v < 0) continue;
        buf = (buf << 6) | static_cast<uint32_t>(v);
        bits += 6;
        if (bits >= 8) {
            bits -= 8;
            out.push_back(static_cast<uint8_t>((buf >> bits) & 0xFF));
        }
    }
    return out;
}

// ─── ClipboardStore ──────────────────────────────────────────────────────────
/*
 * Thread-safe store that keeps the latest clipboard entry per device.
 * getNewest() returns the entry with the highest timestamp across all devices.
 */
class ClipboardStore {
public:
    void update(const ClipEntry& incoming) {
        std::lock_guard<std::mutex> lk(mutex_);
        auto& entry = entries_[incoming.deviceId];
        if (incoming.timestampMs >= entry.timestampMs)
            entry = incoming;
    }

    // Convenience overload for text-only updates
    void updateText(const std::string& deviceId, const std::string& text, uint64_t tsMs) {
        ClipEntry e;
        e.type        = ClipType::TEXT;
        e.text        = text;
        e.mime        = "text/plain";
        e.timestampMs = tsMs;
        e.deviceId    = deviceId;
        update(e);
    }

    // Returns the globally newest entry (empty if store is empty).
    ClipEntry getNewest() const {
        std::lock_guard<std::mutex> lk(mutex_);
        ClipEntry best;
        for (const auto& [id, entry] : entries_) {
            if (entry.timestampMs >= best.timestampMs)
                best = entry;
        }
        return best;
    }

private:
    mutable std::mutex                         mutex_;
    std::unordered_map<std::string, ClipEntry> entries_;
};

// ═══════════════════════════════════════════════════════════════════════════════
// ─── SSE broadcaster ─────────────────────────────────────────────────────────
// Keeps a list of open SSE client sockets and fans-out event strings to all.
// ═══════════════════════════════════════════════════════════════════════════════
class SseBroadcaster {
public:
    void addClient(int fd) {
        std::lock_guard<std::mutex> lk(mutex_);
        clients_.push_back(fd);
    }

    void broadcast(const std::string& data) {
        std::lock_guard<std::mutex> lk(mutex_);
        for (auto it = clients_.begin(); it != clients_.end(); ) {
            ssize_t n = ::send(*it, data.data(), data.size(), MSG_NOSIGNAL);
            if (n <= 0) {
                ::close(*it);
                it = clients_.erase(it);
            } else {
                ++it;
            }
        }
    }

    ~SseBroadcaster() {
        std::lock_guard<std::mutex> lk(mutex_);
        for (int fd : clients_) ::close(fd);
    }

private:
    std::mutex     mutex_;
    std::list<int> clients_;
};

// ─── JSON helpers ─────────────────────────────────────────────────────────────
static std::string jsonEscape(const std::string& s) {
    std::string out;
    out.reserve(s.size() + 16);
    for (unsigned char c : s) {
        switch (c) {
            case '"':  out += "\\\""; break;
            case '\\': out += "\\\\"; break;
            case '\n': out += "\\n";  break;
            case '\r': out += "\\r";  break;
            case '\t': out += "\\t";  break;
            default:
                if (c < 0x20) {
                    char buf[8];
                    snprintf(buf, sizeof(buf), "\\u%04x", c);
                    out += buf;
                } else {
                    out += static_cast<char>(c);
                }
        }
    }
    return out;
}

// Returns a compact JSON description of a ClipEntry.
// For images, the "imageData" field is omitted (too large for SSE);
// clients fetch /image separately.
static std::string clipEntryToJson(const ClipEntry& e) {
    std::ostringstream oss;
    oss << "{"
        << "\"type\":\""   << (e.type == ClipType::IMAGE ? "image" : "text") << "\","
        << "\"text\":\""   << jsonEscape(e.text) << "\","
        << "\"mime\":\""   << jsonEscape(e.mime) << "\","
        << "\"device\":\"" << jsonEscape(e.deviceId) << "\","
        << "\"ts\":"       << e.timestampMs
        << "}";
    return oss.str();
}

// ═══════════════════════════════════════════════════════════════════════════════
// ─── UDP fragmentation / reassembly ──────────────────────────────────────────
//
// Every clipboard payload (text or image) is split into FRAG_PAYLOAD-byte
// chunks.  Each chunk is sent as one UDP datagram with the header below.
// The receiver collects all fragments for a transfer_id and reassembles them
// once frag_total distinct fragments have arrived.
// ═══════════════════════════════════════════════════════════════════════════════

// ── Fragment packet (encoded as: header lines + raw binary payload) ───────────
struct Fragment {
    uint64_t    transferId  = 0;
    std::string type;          // "TEXT" or "IMAGE"
    std::string mime;
    std::string deviceId;
    uint64_t    timestampMs = 0;
    uint32_t    fragIndex   = 0;
    uint32_t    fragTotal   = 0;
    size_t      totalBytes  = 0;
    std::vector<uint8_t> payload;   // raw bytes of this fragment
    bool        valid       = false;
};

// Build one fragment datagram.
static std::string encodeFragment(uint64_t           transferId,
                                   const std::string& type,
                                   const std::string& mime,
                                   const std::string& deviceId,
                                   uint64_t           tsMs,
                                   uint32_t           fragIndex,
                                   uint32_t           fragTotal,
                                   size_t             totalBytes,
                                   const uint8_t*     fragData,
                                   size_t             fragLen) {
    std::ostringstream hdr;
    hdr << FRAG_MAGIC    << '\n'
        << transferId    << '\n'
        << type          << '\n'
        << mime          << '\n'
        << deviceId      << '\n'
        << tsMs          << '\n'
        << fragIndex     << '\n'
        << fragTotal     << '\n'
        << totalBytes    << '\n'
        << fragLen       << '\n';
    std::string h = hdr.str();
    std::string pkt;
    pkt.reserve(h.size() + fragLen);
    pkt += h;
    pkt.append(reinterpret_cast<const char*>(fragData), fragLen);
    return pkt;
}

static Fragment decodeFragment(const char* buf, size_t len) {
    Fragment f;
    const size_t magicLen = strlen(FRAG_MAGIC);
    if (len < magicLen + 1) return f;
    if (std::memcmp(buf, FRAG_MAGIC, magicLen) != 0 || buf[magicLen] != '\n') return f;

    // Parse newline-delimited header fields
    auto readLine = [&](size_t& pos) -> std::string {
        size_t nl = std::string::npos;
        for (size_t i = pos; i < len; ++i) if (buf[i] == '\n') { nl = i; break; }
        if (nl == std::string::npos) return {};
        std::string line(buf + pos, nl - pos);
        pos = nl + 1;
        return line;
    };

    size_t pos = 0;
    if (readLine(pos) != FRAG_MAGIC) return f;   // magic line

    f.transferId  = 0; try { f.transferId  = std::stoull(readLine(pos)); } catch (...) { return f; }
    f.type        = readLine(pos);
    f.mime        = readLine(pos);
    f.deviceId    = readLine(pos);
    if (f.deviceId.empty()) return f;
    f.timestampMs = 0; try { f.timestampMs = std::stoull(readLine(pos)); } catch (...) { return f; }
    f.fragIndex   = 0; try { f.fragIndex   = static_cast<uint32_t>(std::stoul(readLine(pos))); } catch (...) { return f; }
    f.fragTotal   = 0; try { f.fragTotal   = static_cast<uint32_t>(std::stoul(readLine(pos))); } catch (...) { return f; }
    f.totalBytes  = 0; try { f.totalBytes  = std::stoull(readLine(pos)); } catch (...) { return f; }
    size_t fragLen = 0; try { fragLen      = std::stoull(readLine(pos)); } catch (...) { return f; }

    if (f.fragTotal == 0 || f.fragIndex >= f.fragTotal) return f;
    if (pos + fragLen > len) return f;   // truncated

    f.payload.assign(reinterpret_cast<const uint8_t*>(buf + pos),
                     reinterpret_cast<const uint8_t*>(buf + pos + fragLen));
    f.valid = true;
    return f;
}

// ── Reassembly session ────────────────────────────────────────────────────────
struct ReassemblySession {
    std::string              type;
    std::string              mime;
    std::string              deviceId;
    uint64_t                 timestampMs = 0;
    uint32_t                 fragTotal   = 0;
    size_t                   totalBytes  = 0;
    std::map<uint32_t, std::vector<uint8_t>> fragments;  // index → bytes
    Clock::time_point        lastSeen;
};

// ── Reassembly table ──────────────────────────────────────────────────────────
class ReassemblyTable {
public:
    // Feed one fragment; returns a complete ClipEntry if reassembly finished,
    // or an entry with timestampMs==0 if not yet complete / rejected.
    ClipEntry feed(const Fragment& f) {
        std::lock_guard<std::mutex> lk(mutex_);
        evictStale();

        // ── Security guards ───────────────────────────────────────────────────
        // 1. Reject oversized transfers immediately — before allocating anything.
        if (f.totalBytes > MAX_IMAGE_BYTES) {
            std::cerr << "[UDP] Rejected transfer " << f.transferId
                      << ": totalBytes=" << f.totalBytes
                      << " exceeds MAX_IMAGE_BYTES=" << MAX_IMAGE_BYTES << "\n";
            return {};
        }
        // 2. Sanity-check fragment count (prevent map-bomb via fragTotal=UINT32_MAX).
        if (f.fragTotal == 0 || f.fragTotal > MAX_IMAGE_BYTES / 1024) return {};
        // 3. Cap number of concurrent sessions to prevent memory exhaustion.
        if (sessions_.size() >= MAX_SESSIONS &&
            sessions_.find(f.transferId) == sessions_.end()) {
            std::cerr << "[UDP] Session table full — dropping transfer "
                      << f.transferId << "\n";
            return {};
        }

        auto& sess = sessions_[f.transferId];
        if (sess.fragTotal == 0) {
            // New session: initialise metadata.
            sess.type        = f.type;
            sess.mime        = f.mime;
            sess.deviceId    = f.deviceId;
            sess.timestampMs = f.timestampMs;
            sess.fragTotal   = f.fragTotal;
            sess.totalBytes  = f.totalBytes;
        }
        sess.lastSeen = Clock::now();

        // 4. Ignore duplicate fragments (idempotent insert).
        sess.fragments.emplace(f.fragIndex, f.payload);

        if (sess.fragments.size() < static_cast<size_t>(sess.fragTotal))
            return {};   // not yet complete

        // ── Reassemble ────────────────────────────────────────────────────────
        std::vector<uint8_t> data;
        data.reserve(sess.totalBytes);
        for (auto& [idx, chunk] : sess.fragments)
            data.insert(data.end(), chunk.begin(), chunk.end());

        ClipEntry e;
        e.deviceId    = sess.deviceId;
        e.timestampMs = sess.timestampMs;
        e.mime        = sess.mime;

        if (sess.type == "IMAGE") {
            e.type      = ClipType::IMAGE;
            e.imageData = std::move(data);
        } else {
            e.type = ClipType::TEXT;
            e.text = std::string(data.begin(), data.end());
        }

        sessions_.erase(f.transferId);
        return e;
    }

private:
    // Evict sessions that have not received a fragment within FRAG_TIMEOUT_S.
    // Must be called with mutex_ held.
    void evictStale() {
        auto now = Clock::now();
        for (auto it = sessions_.begin(); it != sessions_.end(); ) {
            auto age = std::chrono::duration_cast<std::chrono::seconds>(
                           now - it->second.lastSeen).count();
            if (age > FRAG_TIMEOUT_S) {
                std::cerr << "[UDP] Evicting stale session " << it->first << "\n";
                it = sessions_.erase(it);
            } else {
                ++it;
            }
        }
    }

    std::mutex                                       mutex_;
    std::unordered_map<uint64_t, ReassemblySession>  sessions_;
};

// ── Fragmented sender helper ──────────────────────────────────────────────────
// Splits payload into FRAG_PAYLOAD-byte chunks and sends each as a datagram.
class UdpBroadcaster {
public:
    UdpBroadcaster() {
        fd_ = socket(AF_INET, SOCK_DGRAM, 0);
        if (fd_ < 0) throw std::runtime_error("socket() failed for broadcaster");
        int yes = 1;
        if (setsockopt(fd_, SOL_SOCKET, SO_BROADCAST, &yes, sizeof(yes)) < 0)
            throw std::runtime_error("setsockopt(SO_BROADCAST) failed");
        std::memset(&dest_, 0, sizeof(dest_));
        dest_.sin_family      = AF_INET;
        dest_.sin_port        = htons(UDP_PORT);
        dest_.sin_addr.s_addr = htonl(INADDR_BROADCAST);
    }
    ~UdpBroadcaster() { if (fd_ >= 0) close(fd_); }
    UdpBroadcaster(const UdpBroadcaster&)            = delete;
    UdpBroadcaster& operator=(const UdpBroadcaster&) = delete;

    // Send a complete ClipEntry, fragmenting as needed.
    void broadcastEntry(const ClipEntry& e) {
        const uint8_t* data = nullptr;
        size_t         dataLen = 0;
        std::string    typeStr;

        // For text, work directly on the string bytes
        const std::vector<uint8_t>* imgPtr = nullptr;
        if (e.type == ClipType::IMAGE) {
            typeStr = "IMAGE";
            imgPtr  = &e.imageData;
            data    = imgPtr->data();
            dataLen = imgPtr->size();
        } else {
            typeStr = "TEXT";
            data    = reinterpret_cast<const uint8_t*>(e.text.data());
            dataLen = e.text.size();
        }

        if (dataLen == 0) return;

        uint64_t tid      = makeTransferId();
        uint32_t total    = static_cast<uint32_t>((dataLen + FRAG_PAYLOAD - 1) / FRAG_PAYLOAD);
        size_t   offset   = 0;

        for (uint32_t idx = 0; idx < total; ++idx) {
            size_t chunk = std::min(FRAG_PAYLOAD, dataLen - offset);
            std::string pkt = encodeFragment(tid, typeStr, e.mime,
                                             e.deviceId, e.timestampMs,
                                             idx, total, dataLen,
                                             data + offset, chunk);
            sendRaw(pkt);
            offset += chunk;
            // Small inter-fragment delay to avoid flooding the receiver's
            // socket buffer (especially for large images)
            if (total > 1)
                std::this_thread::sleep_for(std::chrono::milliseconds(2));
        }
    }

private:
    void sendRaw(const std::string& data) {
        sendto(fd_, data.data(), data.size(), 0,
               reinterpret_cast<sockaddr*>(&dest_), sizeof(dest_));
    }
    int         fd_ = -1;
    sockaddr_in dest_{};
};

// ─── UDP listener ────────────────────────────────────────────────────────────
class UdpListener {
public:
    explicit UdpListener(uint16_t port) {
        fd_ = socket(AF_INET, SOCK_DGRAM, 0);
        if (fd_ < 0) throw std::runtime_error("socket() failed for listener");
        int yes = 1;
        setsockopt(fd_, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof(yes));
        setsockopt(fd_, SOL_SOCKET, SO_REUSEPORT, &yes, sizeof(yes));
        struct timeval tv { 1, 0 };
        setsockopt(fd_, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
        sockaddr_in addr{};
        addr.sin_family      = AF_INET;
        addr.sin_port        = htons(port);
        addr.sin_addr.s_addr = htonl(INADDR_ANY);
        if (bind(fd_, reinterpret_cast<sockaddr*>(&addr), sizeof(addr)) < 0)
            throw std::runtime_error("bind() failed for listener on port "
                                     + std::to_string(port));
    }
    ~UdpListener() { if (fd_ >= 0) close(fd_); }
    UdpListener(const UdpListener&)            = delete;
    UdpListener& operator=(const UdpListener&) = delete;

    // Returns a decoded Fragment (valid=false on timeout/error).
    Fragment recv() {
        static thread_local std::vector<char> buf(MAX_PACKET);
        sockaddr_in src{}; socklen_t srcLen = sizeof(src);
        ssize_t n = recvfrom(fd_, buf.data(), buf.size(), 0,
                             reinterpret_cast<sockaddr*>(&src), &srcLen);
        if (n <= 0) return {};
        return decodeFragment(buf.data(), static_cast<size_t>(n));
    }

private:
    int fd_ = -1;
};

// ─── thread: local clipboard watcher ─────────────────────────────────────────
static void localWatcherThread(ClipboardStore&    store,
                                UdpBroadcaster&    broadcaster,
                                const std::string& deviceId,
                                std::atomic<bool>& stop) {
    std::string last;
    while (!stop.load()) {
        std::this_thread::sleep_for(std::chrono::seconds(1));
        std::string current = getLocalClipboard();
        if (current != last) {
            last = current;
            uint64_t ts = nowMs();
            store.updateText(deviceId, current, ts);
            if (!current.empty()) {
                ClipEntry e;
                e.type        = ClipType::TEXT;
                e.text        = current;
                e.mime        = "text/plain";
                e.deviceId    = deviceId;
                e.timestampMs = ts;
                broadcaster.broadcastEntry(e);
            }
        }
    }
}

// ─── thread: UDP listener + reassembler ───────────────────────────────────────
static void udpListenerThread(ClipboardStore&    store,
                               UdpListener&       listener,
                               ReassemblyTable&   reassembly,
                               const std::string& ownDeviceId,
                               std::atomic<bool>& stop) {
    while (!stop.load()) {
        Fragment frag = listener.recv();
        if (!frag.valid) continue;
        if (frag.deviceId == ownDeviceId) continue;   // ignore own broadcasts

        ClipEntry assembled = reassembly.feed(frag);
        if (assembled.timestampMs != 0)               // complete
            store.update(assembled);
    }
}

// ─── thread: display / virtual clipboard ─────────────────────────────────────
static void displayThread(ClipboardStore&    store,
                           SseBroadcaster&    sseBroadcaster,
                           const std::string& ownDeviceId,
                           std::atomic<bool>& stop) {
    ClipEntry lastShown;
    while (!stop.load()) {
        std::this_thread::sleep_for(std::chrono::seconds(1));
        ClipEntry newest = store.getNewest();

        // Change detection: compare timestamp + device
        if (newest.timestampMs == lastShown.timestampMs &&
            newest.deviceId    == lastShown.deviceId)
            continue;

        lastShown = newest;

        // Push compact JSON to all SSE clients (image bytes NOT included here)
        std::string sseEvent = "data: " + clipEntryToJson(newest) + "\n\n";
        sseBroadcaster.broadcast(sseEvent);

        bool isRemote = !newest.deviceId.empty() && newest.deviceId != ownDeviceId;

        if (newest.type == ClipType::IMAGE) {
            std::cout << "[" << (isRemote ? "Remote" : "Local")
                      << " image from " << newest.deviceId
                      << " – " << newest.imageData.size() << " bytes, "
                      << newest.mime << "]\n\n";
            // Write image to local clipboard via xclip (if available)
            if (isRemote && !newest.imageData.empty()) {
                std::string cmd = "xclip -in -selection clipboard -t "
                                  + newest.mime + " 2>/dev/null";
                FILE* p = popen(cmd.c_str(), "w");
                if (p) {
                    fwrite(newest.imageData.data(), 1, newest.imageData.size(), p);
                    pclose(p);
                }
            }
        } else {
            if (newest.text.empty()) {
                std::cout << "[Clipboard empty across all devices]\n\n";
            } else {
                if (isRemote) {
                    std::cout << "[Remote clipboard from " << newest.deviceId << "]\n";
                    setLocalClipboard(newest.text);
                } else {
                    std::cout << "[Local clipboard changed]\n";
                }
                std::cout << newest.text << "\n\n";
            }
        }
        std::cout.flush();
    }
}

// ═══════════════════════════════════════════════════════════════════════════════
// ─── HTTP helpers ─────────────────────────────────────────────────────────────
// ═══════════════════════════════════════════════════════════════════════════════

static const char* httpStatusText(int code) {
    switch (code) {
        case 200: return "OK";
        case 204: return "No Content";
        case 400: return "Bad Request";
        case 404: return "Not Found";
        case 405: return "Method Not Allowed";
        case 413: return "Content Too Large";
        case 500: return "Internal Server Error";
        case 503: return "Service Unavailable";
        default:  return "Unknown";
    }
}

// Send a complete HTTP response (text/binary body) over a socket fd.
static void httpSend(int fd, int status, const std::string& contentType,
                     const std::string& body) {
    std::ostringstream hdr;
    hdr << "HTTP/1.1 " << status << " " << httpStatusText(status) << "\r\n"
        << "Content-Type: " << contentType << "\r\n"
        << "Content-Length: " << body.size() << "\r\n"
        << "Access-Control-Allow-Origin: *\r\n"
        << "X-Content-Type-Options: nosniff\r\n"
        << "Connection: close\r\n"
        << "\r\n";
    std::string h = hdr.str();
    ::send(fd, h.data(),    h.size(),    MSG_NOSIGNAL);
    ::send(fd, body.data(), body.size(), MSG_NOSIGNAL);
}

// Binary overload (for images and certificate files).
static void httpSendBinary(int fd, int status, const std::string& contentType,
                            const uint8_t* data, size_t len) {
    std::ostringstream hdr;
    hdr << "HTTP/1.1 " << status << " " << httpStatusText(status) << "\r\n"
        << "Content-Type: " << contentType << "\r\n"
        << "Content-Length: " << len << "\r\n"
        << "Access-Control-Allow-Origin: *\r\n"
        << "X-Content-Type-Options: nosniff\r\n"
        << "Connection: close\r\n"
        << "\r\n";
    std::string h = hdr.str();
    ::send(fd, h.data(), h.size(), MSG_NOSIGNAL);
    ::send(fd, data,     len,      MSG_NOSIGNAL);
}

// ─── Read a file from disk into a vector (for /ca.crt) ───────────────────────
static std::optional<std::vector<uint8_t>> readFileFully(const char* path) {
    FILE* f = fopen(path, "rb");
    if (!f) return std::nullopt;
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    rewind(f);
    if (sz <= 0 || sz > 1024 * 1024) { fclose(f); return std::nullopt; }
    std::vector<uint8_t> buf(static_cast<size_t>(sz));
    if (fread(buf.data(), 1, buf.size(), f) != buf.size()) {
        fclose(f); return std::nullopt;
    }
    fclose(f);
    return buf;
}

// ─── Thread pool for HTTP connections ────────────────────────────────────────
/*
 * A fixed-size pool of worker threads.  The accept() loop enqueues accepted
 * client fds; workers dequeue and call handleHttpClient().
 * When stop is set, the pool drains gracefully and all workers join.
 */
class HttpThreadPool {
public:
    using Task = std::function<void()>;

    explicit HttpThreadPool(int numWorkers) {
        workers_.reserve(static_cast<size_t>(numWorkers));
        for (int i = 0; i < numWorkers; ++i)
            workers_.emplace_back([this]() { workerLoop(); });
    }

    // Returns false if the queue is full (caller should close the fd).
    bool enqueue(Task t) {
        {
            std::lock_guard<std::mutex> lk(mutex_);
            if (shutdown_ || queue_.size() >= HTTP_QUEUE_MAX)
                return false;
            queue_.push(std::move(t));
        }
        cv_.notify_one();
        return true;
    }

    void shutdown() {
        {
            std::lock_guard<std::mutex> lk(mutex_);
            shutdown_ = true;
        }
        cv_.notify_all();
        for (auto& t : workers_)
            if (t.joinable()) t.join();
    }

    ~HttpThreadPool() { shutdown(); }

private:
    void workerLoop() {
        for (;;) {
            Task task;
            {
                std::unique_lock<std::mutex> lk(mutex_);
                cv_.wait(lk, [this]{ return shutdown_ || !queue_.empty(); });
                if (shutdown_ && queue_.empty()) return;
                task = std::move(queue_.front());
                queue_.pop();
            }
            task();
        }
    }

    std::vector<std::thread>    workers_;
    std::queue<Task>            queue_;
    std::mutex                  mutex_;
    std::condition_variable     cv_;
    bool                        shutdown_ = false;
};

// ═══════════════════════════════════════════════════════════════════════════════
// ─── Phone Web UI (self-contained HTML page) ──────────────────────────────────
// ═══════════════════════════════════════════════════════════════════════════════
static const char* PHONE_UI = R"HTML(<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>LAN Clipboard</title>
<style>
  :root {
    --bg:#0f172a;--surface:#1e293b;--border:#334155;
    --accent:#38bdf8;--accent2:#818cf8;--accent3:#34d399;
    --text:#e2e8f0;--sub:#94a3b8;--danger:#f87171;--success:#4ade80;
    --warn:#fb923c;
    --radius:14px;--font:'Segoe UI',system-ui,sans-serif;
  }
  *{box-sizing:border-box;margin:0;padding:0}
  body{background:var(--bg);color:var(--text);font-family:var(--font);
    min-height:100dvh;display:flex;flex-direction:column;
    align-items:center;padding:20px 14px 48px}
  header{width:100%;max-width:620px;display:flex;align-items:center;
    gap:12px;margin-bottom:24px}
  header h1{font-size:1.3rem;font-weight:700;letter-spacing:-.4px}
  header small{display:block;color:var(--sub);font-size:.78rem;margin-top:2px}
  .dot{width:9px;height:9px;border-radius:50%;background:var(--danger);
    flex-shrink:0;transition:background .4s}
  .dot.live{background:var(--success)}
  .card{width:100%;max-width:620px;background:var(--surface);
    border:1px solid var(--border);border-radius:var(--radius);
    padding:18px;margin-bottom:18px}
  .card-title{font-size:.72rem;font-weight:700;text-transform:uppercase;
    letter-spacing:.08em;color:var(--sub);margin-bottom:12px}
  /* ── Camera warning banner ── */
  #camera-warn{display:none;background:#1c1200;border:1px solid var(--warn);
    border-radius:10px;padding:12px 14px;margin-bottom:14px;
    font-size:.88rem;color:var(--warn);line-height:1.5}
  #camera-warn a{color:var(--accent);text-decoration:underline}
  /* ── Current clipboard display ── */
  #clip-content{min-height:120px;background:var(--bg);
    border:1px solid var(--border);border-radius:10px;
    padding:12px;font-size:.97rem;line-height:1.6;
    white-space:pre-wrap;word-break:break-word;user-select:text}
  #clip-img{display:none;max-width:100%;border-radius:10px;
    border:1px solid var(--border);cursor:pointer}
  #clip-meta{margin-top:8px;font-size:.75rem;color:var(--sub);
    display:flex;justify-content:space-between;flex-wrap:wrap;gap:4px}
  .btn{width:100%;padding:12px;border:none;border-radius:10px;
    font-size:.97rem;font-weight:700;cursor:pointer;
    transition:opacity .15s;margin-top:10px}
  .btn:active{opacity:.72} .btn:disabled{opacity:.4;cursor:default}
  .btn-blue{background:var(--accent);color:#0f172a}
  .btn-purple{background:var(--accent2);color:#fff}
  .btn-green{background:var(--accent3);color:#0f172a}
  /* ── Text send area ── */
  #send-input{width:100%;min-height:100px;resize:vertical;
    background:var(--bg);border:1px solid var(--border);
    border-radius:10px;padding:12px;font-size:.97rem;
    color:var(--text);font-family:var(--font);line-height:1.6;
    outline:none;transition:border-color .2s}
  #send-input:focus{border-color:var(--accent2)}
  /* ── Image send area ── */
  .img-drop{border:2px dashed var(--border);border-radius:10px;
    padding:24px 16px;text-align:center;color:var(--sub);
    font-size:.9rem;cursor:pointer;transition:border-color .2s;
    position:relative}
  .img-drop.over{border-color:var(--accent)}
  .img-drop input[type=file]{position:absolute;inset:0;opacity:0;cursor:pointer}
  #img-preview{display:none;max-width:100%;border-radius:8px;
    margin-top:12px;border:1px solid var(--border)}
  /* ── Progress bar ── */
  #progress-wrap{display:none;margin-top:10px}
  #progress-bar{height:6px;background:var(--border);border-radius:3px;overflow:hidden}
  #progress-fill{height:100%;width:0%;background:var(--accent);
    transition:width .2s;border-radius:3px}
  #progress-label{font-size:.75rem;color:var(--sub);margin-top:4px;text-align:center}
  /* ── Camera card ── */
  #camera-wrap{display:none;margin-top:12px}
  #camera-video{width:100%;border-radius:10px;background:#000}
  #camera-canvas{display:none}
  /* ── Toast ── */
  #toast{position:fixed;bottom:24px;left:50%;transform:translateX(-50%);
    background:#1e293b;border:1px solid var(--border);color:var(--text);
    padding:9px 20px;border-radius:999px;font-size:.88rem;
    opacity:0;pointer-events:none;transition:opacity .3s;
    white-space:nowrap;z-index:999}
  #toast.show{opacity:1}
</style>
</head>
<body>

<header>
  <svg width="34" height="34" viewBox="0 0 24 24" fill="none"
       stroke="var(--accent)" stroke-width="1.8"
       stroke-linecap="round" stroke-linejoin="round" style="flex-shrink:0">
    <rect x="9" y="2" width="6" height="4" rx="1"/>
    <path d="M16 4h2a2 2 0 0 1 2 2v14a2 2 0 0 1-2 2H6a2 2 0 0 1-2-2V6a2 2 0 0 1 2-2h2"/>
    <line x1="12" y1="11" x2="12" y2="17"/><line x1="9" y1="14" x2="15" y2="14"/>
  </svg>
  <div style="flex:1">
    <h1>LAN Clipboard</h1>
    <small id="status-text">Connecting…</small>
  </div>
  <div class="dot" id="dot"></div>
</header>

<!-- ── Camera / HTTPS availability warning ───────────────── -->
<div id="camera-warn" class="card" style="display:none">
  ⚠️ <strong>Camera unavailable</strong> — your browser requires a secure
  (HTTPS) connection to access the camera.<br>
  Please open this page via the HTTPS address instead:
  <a id="https-link" href="#">switch to HTTPS</a>.<br>
  <small style="color:var(--sub)">
    You may also need to install the local CA certificate:
    <a href="/ca.crt">download ca.crt</a> and trust it on your device.
  </small>
</div>

<!-- ── Current clipboard ─────────────────────────────────── -->
<div class="card">
  <div class="card-title">📋 Current clipboard</div>
  <div id="clip-content">(empty)</div>
  <img id="clip-img" alt="clipboard image" onclick="saveImage()">
  <div id="clip-meta">
    <span id="clip-device">—</span>
    <span id="clip-ts">—</span>
  </div>
  <button class="btn btn-blue" id="copy-btn" onclick="copyToPhone()">📋 Copy text to my phone</button>
  <button class="btn btn-green" id="save-img-btn" style="display:none"
          onclick="saveImage()">💾 Save image to phone</button>
</div>

<!-- ── Send text ─────────────────────────────────────────── -->
<div class="card">
  <div class="card-title">✏️ Send text to all devices</div>
  <textarea id="send-input" placeholder="Type something here…" rows="4"></textarea>
  <button class="btn btn-purple" id="send-btn" onclick="sendText()">
    ✉️ Send text
  </button>
</div>

<!-- ── Send image ─────────────────────────────────────────── -->
<div class="card">
  <div class="card-title">🖼️ Send image to all devices</div>

  <!-- File / gallery picker -->
  <div class="img-drop" id="drop-zone">
    <input type="file" id="file-input" accept="image/*"
           onchange="onFileChosen(this.files[0])">
    📂 Tap to pick from gallery or drag &amp; drop
  </div>
  <img id="img-preview" alt="preview">

  <!-- Camera capture -->
  <button class="btn btn-blue" id="camera-btn" style="margin-top:10px"
          onclick="toggleCamera()">📷 Take photo with camera</button>
  <div id="camera-wrap">
    <video id="camera-video" autoplay playsinline></video>
    <canvas id="camera-canvas"></canvas>
    <button class="btn btn-green" style="margin-top:8px"
            onclick="capturePhoto()">📸 Capture</button>
    <button class="btn" style="background:var(--border);margin-top:6px"
            onclick="stopCamera()">✖ Cancel</button>
  </div>

  <!-- Progress -->
  <div id="progress-wrap">
    <div id="progress-bar"><div id="progress-fill"></div></div>
    <div id="progress-label">Uploading…</div>
  </div>

  <button class="btn btn-purple" id="send-img-btn" onclick="sendImage()"
          style="display:none">🚀 Send image to LAN</button>
</div>

<!-- ── Certificate install helper ────────────────────────── -->
<div class="card">
  <div class="card-title">🔐 HTTPS / Certificate</div>
  <p style="font-size:.88rem;color:var(--sub);line-height:1.6">
    Camera capture requires HTTPS. If you haven't already, install the local
    CA certificate on your phone so the browser trusts this server.
  </p>
  <a href="/ca.crt" class="btn btn-blue"
     style="display:block;text-align:center;text-decoration:none;margin-top:10px">
    📥 Download &amp; install CA certificate
  </a>
</div>

<div id="toast"></div>

<script>
/* ═══════════════════════════════════════════════════════════
   getUserMedia polyfill / compatibility shim
   Normalises the older prefixed API onto navigator.mediaDevices
   for browsers that predate the standard (very old Android WebView).
   ═══════════════════════════════════════════════════════════ */
(function() {
  if (!navigator.mediaDevices) {
    navigator.mediaDevices = {};
  }
  if (!navigator.mediaDevices.getUserMedia) {
    const legacyGUM =
      navigator.getUserMedia       ||
      navigator.webkitGetUserMedia ||
      navigator.mozGetUserMedia    ||
      navigator.msGetUserMedia;

    if (legacyGUM) {
      navigator.mediaDevices.getUserMedia = function(constraints) {
        return new Promise(function(resolve, reject) {
          legacyGUM.call(navigator, constraints, resolve, reject);
        });
      };
    }
    // If no API exists at all, leave getUserMedia undefined so the
    // availability check below can detect it and show the warning.
  }
})();

/* ═══════════════════════════════════════════════════════════
   Camera / HTTPS availability check
   Runs once at page load.  Shows a warning banner and disables
   the camera button when getUserMedia is not available (which
   happens over plain HTTP on modern browsers).
   ═══════════════════════════════════════════════════════════ */
(function checkCameraAvailability() {
  const cameraAvailable =
    typeof navigator.mediaDevices !== 'undefined' &&
    typeof navigator.mediaDevices.getUserMedia === 'function';

  if (!cameraAvailable) {
    // Show warning banner
    const warn = document.getElementById('camera-warn');
    warn.style.display = 'block';

    // Build HTTPS link (replace http:// with https:// and port 8765→8444)
    const httpsUrl = window.location.href
      .replace(/^http:/, 'https:')
      .replace(/:8765/, ':8444');
    const link = document.getElementById('https-link');
    link.href = httpsUrl;
    link.textContent = httpsUrl;

    // Disable the camera button
    const btn = document.getElementById('camera-btn');
    if (btn) {
      btn.disabled = true;
      btn.title    = 'Camera requires HTTPS — see warning above';
    }
  }
})();

/* ═══════════════════════════════════════════════════════════
   State
   ═══════════════════════════════════════════════════════════ */
let currentText      = '';
let currentIsImg     = false;
let currentImgTs     = 0;    // timestamp of the image currently displayed
let pendingBlob      = null; // image blob waiting to be sent
let cameraStream     = null;
let autoDownload     = false; // set to true after first user gesture

/* ═══════════════════════════════════════════════════════════
   SSE – live clipboard updates
   ═══════════════════════════════════════════════════════════ */
function connectSSE() {
  const es = new EventSource('/events');
  es.onopen = () => {
    document.getElementById('dot').classList.add('live');
    document.getElementById('status-text').textContent = 'Live — updates instantly';
  };
  es.onmessage = e => {
    try { applyClip(JSON.parse(e.data), /*fromSSE=*/true); } catch(_) {}
  };
  es.onerror = () => {
    document.getElementById('dot').classList.remove('live');
    document.getElementById('status-text').textContent = 'Reconnecting…';
    es.close(); setTimeout(connectSSE, 3000);
  };
}

/* ═══════════════════════════════════════════════════════════
   Apply a clipboard entry to the UI.
   fromSSE=true  →  the update came from a live SSE push
                    (triggers auto-download for images).
   ═══════════════════════════════════════════════════════════ */
function applyClip(obj, fromSSE) {
  const content = document.getElementById('clip-content');
  const clipImg = document.getElementById('clip-img');
  const saveBtn = document.getElementById('save-img-btn');
  const copyBtn = document.getElementById('copy-btn');

  document.getElementById('clip-device').textContent = '📡 ' + (obj.device || '?');
  document.getElementById('clip-ts').textContent =
    new Date(obj.ts).toLocaleTimeString();

  if (obj.type === 'image') {
    currentIsImg = true;
    currentText  = '';

    // Only reload image if the timestamp changed (avoid flicker on reconnect)
    if (obj.ts !== currentImgTs) {
      currentImgTs = obj.ts;
      content.style.display = 'none';
      clipImg.style.display = 'block';
      saveBtn.style.display = 'block';
      clipImg.src = '/image?ts=' + obj.ts;  // cache-bust
      copyBtn.style.display = 'none';

      // ── Auto-download: when a NEW image arrives via SSE ──────────────────
      // We only auto-download if the user has already interacted with the
      // page (required by browser autoplay/download policies).
      if (fromSSE && autoDownload) {
        // Small delay so the image fetch completes before download starts.
        setTimeout(autoDownloadImage, 800);
      } else if (fromSSE) {
        toast('📥 New image received — tap Save to download');
      }
    }
  } else {
    currentIsImg = false;
    currentText  = obj.text || '';
    content.style.display = '';
    content.textContent   = currentText || '(empty)';
    clipImg.style.display = 'none';
    saveBtn.style.display = 'none';
    copyBtn.style.display = '';
  }
}

/* ═══════════════════════════════════════════════════════════
   Auto-download: silently trigger <a download> for new image
   ═══════════════════════════════════════════════════════════ */
function autoDownloadImage() {
  const a = document.createElement('a');
  a.href     = '/image?ts=' + currentImgTs;
  a.download = 'clipboard-' + currentImgTs + '.jpg';
  a.style.display = 'none';
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  toast('📥 Image auto-downloaded!');
}

/* ═══════════════════════════════════════════════════════════
   Copy text to phone clipboard
   ═══════════════════════════════════════════════════════════ */
function copyToPhone() {
  autoDownload = true;  // user interacted — enable auto-download from now on
  if (!currentText) { toast('Clipboard is empty'); return; }
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(currentText)
      .then(() => toast('✓ Copied to phone!'))
      .catch(() => fallbackCopy(currentText));
  } else { fallbackCopy(currentText); }
}
function fallbackCopy(text) {
  const ta = Object.assign(document.createElement('textarea'),
    {value: text});
  ta.style.cssText = 'position:fixed;opacity:0;top:0;left:0';
  document.body.appendChild(ta); ta.focus(); ta.select();
  try { document.execCommand('copy'); toast('✓ Copied!'); }
  catch(_) { toast('⚠ Could not copy automatically'); }
  document.body.removeChild(ta);
}

/* ═══════════════════════════════════════════════════════════
   Save / download image to phone (manual trigger)
   ═══════════════════════════════════════════════════════════ */
function saveImage() {
  autoDownload = true;  // user interacted
  autoDownloadImage();
}

/* ═══════════════════════════════════════════════════════════
   Send text
   ═══════════════════════════════════════════════════════════ */
async function sendText() {
  autoDownload = true;
  const text = document.getElementById('send-input').value.trim();
  if (!text) { toast('Nothing to send'); return; }
  const btn = document.getElementById('send-btn');
  btn.disabled = true;
  try {
    const r = await fetch('/clipboard', {
      method: 'POST',
      headers: {'Content-Type': 'text/plain;charset=utf-8'},
      body: text
    });
    if (r.ok) {
      toast('✓ Text sent!');
      document.getElementById('send-input').value = '';
    } else {
      toast('⚠ Server error ' + r.status);
    }
  } catch(_) { toast('⚠ Network error'); }
  finally { btn.disabled = false; }
}
document.getElementById('send-input').addEventListener('keydown', e => {
  if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) sendText();
});

/* ═══════════════════════════════════════════════════════════
   Image file picker + drag-and-drop
   ═══════════════════════════════════════════════════════════ */
function onFileChosen(file) {
  if (!file || !file.type.startsWith('image/')) {
    toast('Please pick an image'); return;
  }
  pendingBlob = file;
  showPreview(file);
}

function showPreview(blob) {
  const prev = document.getElementById('img-preview');
  prev.src = URL.createObjectURL(blob);
  prev.style.display = 'block';
  document.getElementById('send-img-btn').style.display = '';
}

// Drag-and-drop
const dropZone = document.getElementById('drop-zone');
dropZone.addEventListener('dragover', e => {
  e.preventDefault(); dropZone.classList.add('over');
});
dropZone.addEventListener('dragleave', () => dropZone.classList.remove('over'));
dropZone.addEventListener('drop', e => {
  e.preventDefault(); dropZone.classList.remove('over');
  const f = e.dataTransfer.files[0];
  if (f) onFileChosen(f);
});

/* ═══════════════════════════════════════════════════════════
   Camera
   ═══════════════════════════════════════════════════════════ */
async function toggleCamera() {
  autoDownload = true;
  const wrap = document.getElementById('camera-wrap');
  if (cameraStream) { stopCamera(); return; }

  // Check again at call time (polyfill may have filled it in after load)
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
    toast('⚠ Camera requires HTTPS — see warning at top of page');
    return;
  }

  try {
    cameraStream = await navigator.mediaDevices.getUserMedia(
      {video: {facingMode: 'environment', width: {ideal: 1920}}, audio: false});
    document.getElementById('camera-video').srcObject = cameraStream;
    wrap.style.display = 'block';
  } catch(err) {
    let msg = err.message || String(err);
    if (err.name === 'NotAllowedError')
      msg = 'Permission denied. Allow camera access in browser settings.';
    else if (err.name === 'NotFoundError')
      msg = 'No camera found on this device.';
    else if (err.name === 'NotReadableError')
      msg = 'Camera is already in use by another app.';
    toast('⚠ Camera: ' + msg);
  }
}

function stopCamera() {
  if (cameraStream) {
    cameraStream.getTracks().forEach(t => t.stop());
    cameraStream = null;
  }
  document.getElementById('camera-wrap').style.display = 'none';
}

function capturePhoto() {
  const video  = document.getElementById('camera-video');
  const canvas = document.getElementById('camera-canvas');
  canvas.width  = video.videoWidth;
  canvas.height = video.videoHeight;
  canvas.getContext('2d').drawImage(video, 0, 0);
  canvas.toBlob(blob => {
    if (!blob) { toast('Capture failed'); return; }
    pendingBlob = blob;
    showPreview(blob);
    stopCamera();
    toast('✓ Photo captured — press Send to share');
  }, 'image/jpeg', 0.92);
}

/* ═══════════════════════════════════════════════════════════
   Send image via XHR with upload progress bar
   Uses /image-post endpoint (POST).
   ═══════════════════════════════════════════════════════════ */
function sendImage() {
  autoDownload = true;
  if (!pendingBlob) { toast('No image selected'); return; }

  const btn   = document.getElementById('send-img-btn');
  const wrap  = document.getElementById('progress-wrap');
  const fill  = document.getElementById('progress-fill');
  const label = document.getElementById('progress-label');

  btn.disabled = true;
  wrap.style.display = '';
  fill.style.width   = '0%';
  label.textContent  = 'Uploading… 0%';

  const xhr = new XMLHttpRequest();
  xhr.open('POST', '/image-post');
  xhr.setRequestHeader('Content-Type', pendingBlob.type || 'image/jpeg');

  // ── Upload progress ──────────────────────────────────────────────────────
  xhr.upload.onprogress = e => {
    if (e.lengthComputable) {
      const pct = Math.round(e.loaded / e.total * 100);
      fill.style.width  = pct + '%';
      label.textContent = 'Uploading… ' + pct + '%';
    }
  };
  xhr.upload.onloadstart = () => {
    fill.style.width  = '0%';
    label.textContent = 'Starting upload…';
  };
  xhr.upload.onload = () => {
    fill.style.width  = '100%';
    label.textContent = 'Processing…';
  };

  xhr.onload = () => {
    wrap.style.display = 'none';
    fill.style.width   = '0%';
    btn.disabled = false;
    if (xhr.status === 200) {
      toast('✓ Image sent to all devices!');
      pendingBlob = null;
      document.getElementById('img-preview').style.display = 'none';
      document.getElementById('send-img-btn').style.display = 'none';
      document.getElementById('file-input').value = '';
    } else {
      toast('⚠ Server error ' + xhr.status);
    }
  };
  xhr.onerror = () => {
    wrap.style.display = 'none';
    btn.disabled = false;
    toast('⚠ Network error — upload failed');
  };
  xhr.ontimeout = () => {
    wrap.style.display = 'none';
    btn.disabled = false;
    toast('⚠ Upload timed out');
  };
  xhr.timeout = 120000;  // 2-minute timeout for large images
  xhr.send(pendingBlob);
}

/* ═══════════════════════════════════════════════════════════
   Toast notification
   ═══════════════════════════════════════════════════════════ */
let _toastTimer = null;
function toast(msg) {
  const el = document.getElementById('toast');
  el.textContent = msg;
  el.classList.add('show');
  clearTimeout(_toastTimer);
  _toastTimer = setTimeout(() => el.classList.remove('show'), 3000);
}

/* ═══════════════════════════════════════════════════════════
   Bootstrap
   ═══════════════════════════════════════════════════════════ */
fetch('/clipboard')
  .then(r => r.json())
  .then(d => applyClip(d, false))
  .catch(() => {});
connectSSE();
</script>
</body>
</html>
)HTML";

// ═══════════════════════════════════════════════════════════════════════════════
// ─── HTTP request parser ──────────────────────────────────────────────────────
// ═══════════════════════════════════════════════════════════════════════════════
struct HttpRequest {
    std::string method;        // "GET" / "POST"
    std::string path;          // "/", "/clipboard", "/image", "/events"
    std::string contentType;   // value of Content-Type header
    std::string body;          // raw body bytes (text or binary)
    bool        valid = false;
};

static HttpRequest parseHttpRequest(int fd) {
    HttpRequest req;
    std::string raw;
    raw.reserve(8192);

    char buf[8192];
    // Read until we have the full header block
    while (raw.find("\r\n\r\n") == std::string::npos) {
        ssize_t n = ::recv(fd, buf, sizeof(buf), 0);
        if (n <= 0) return req;
        raw.append(buf, static_cast<size_t>(n));
        if (raw.size() > 64 * 1024) return req;   // header safety cap
    }

    size_t lineEnd = raw.find("\r\n");
    if (lineEnd == std::string::npos) return req;
    std::string requestLine = raw.substr(0, lineEnd);

    size_t sp1 = requestLine.find(' ');
    if (sp1 == std::string::npos) return req;
    size_t sp2 = requestLine.find(' ', sp1 + 1);
    if (sp2 == std::string::npos) return req;

    req.method = requestLine.substr(0, sp1);
    req.path   = requestLine.substr(sp1 + 1, sp2 - sp1 - 1);
    size_t q = req.path.find('?');
    if (q != std::string::npos) req.path = req.path.substr(0, q);

    size_t headerEnd = raw.find("\r\n\r\n");
    std::string headers = raw.substr(0, headerEnd);
    size_t bodyStart = headerEnd + 4;

    // Lower-case header block for case-insensitive search
    std::string lc = headers;
    for (char& c : lc) c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));

    // Content-Length
    size_t cl = 0;
    {
        size_t pos = lc.find("content-length:");
        if (pos != std::string::npos) {
            pos += 15;
            while (pos < lc.size() && lc[pos] == ' ') ++pos;
            try { cl = std::stoull(lc.substr(pos)); } catch (...) {}
        }
    }
    // Content-Type
    {
        size_t pos = lc.find("content-type:");
        if (pos != std::string::npos) {
            pos += 13;
            while (pos < lc.size() && lc[pos] == ' ') ++pos;
            size_t end = lc.find("\r\n", pos);
            // Use original case for the value
            req.contentType = headers.substr(pos, end == std::string::npos
                                             ? std::string::npos : end - pos);
            // Strip params (e.g. "; charset=utf-8")
            size_t semi = req.contentType.find(';');
            if (semi != std::string::npos) req.contentType = req.contentType.substr(0, semi);
            // trim
            while (!req.contentType.empty() && req.contentType.back() == ' ')
                req.contentType.pop_back();
        }
    }

    // Read body
    if (cl > 0 && cl <= MAX_IMAGE_BYTES) {
        // Bytes already read past the header
        size_t already = (raw.size() > bodyStart) ? (raw.size() - bodyStart) : 0;
        if (already > 0)
            req.body = raw.substr(bodyStart, std::min(already, cl));

        // Read the rest in large chunks
        while (req.body.size() < cl) {
            size_t needed = cl - req.body.size();
            size_t chunk  = std::min(needed, sizeof(buf));
            ssize_t n = ::recv(fd, buf, chunk, 0);
            if (n <= 0) break;
            req.body.append(buf, static_cast<size_t>(n));
        }
    }

    req.valid = true;
    return req;
}

// ═══════════════════════════════════════════════════════════════════════════════
// ─── HTTP connection handler ──────────────────────────────────────────────────
// ═══════════════════════════════════════════════════════════════════════════════

// Shared image-upload logic used by both POST /image and POST /image-post.
static void handleImageUpload(int             clientFd,
                               const HttpRequest& req,
                               ClipboardStore& store,
                               SseBroadcaster& sseBroadcaster,
                               UdpBroadcaster* udpBroadcaster) {
    if (req.body.empty()) {
        httpSend(clientFd, 400, "text/plain", "Empty body");
        ::close(clientFd); return;
    }
    if (req.body.size() > MAX_IMAGE_BYTES) {
        httpSend(clientFd, 413, "text/plain", "Image exceeds size limit");
        ::close(clientFd); return;
    }

    // Validate MIME type — only accept image/* to prevent arbitrary uploads.
    std::string mime = req.contentType;
    if (mime.empty()) mime = "image/jpeg";
    if (mime.rfind("image/", 0) != 0) {
        httpSend(clientFd, 400, "text/plain", "Content-Type must be image/*");
        ::close(clientFd); return;
    }

    uint64_t    ts      = nowMs();
    std::string phoneId = "phone@web";

    ClipEntry e;
    e.type        = ClipType::IMAGE;
    e.mime        = mime;
    e.deviceId    = phoneId;
    e.timestampMs = ts;
    e.imageData.assign(
        reinterpret_cast<const uint8_t*>(req.body.data()),
        reinterpret_cast<const uint8_t*>(req.body.data() + req.body.size()));

    store.update(e);

    // Fan-out SSE event immediately (the image itself is fetched via /image).
    std::string sseEvent = "data: " + clipEntryToJson(e) + "\n\n";
    sseBroadcaster.broadcast(sseEvent);

    // Write to local desktop clipboard via xclip (best-effort).
    {
        std::string cmd = "xclip -in -selection clipboard -t "
                          + mime + " 2>/dev/null";
        FILE* p = popen(cmd.c_str(), "w");
        if (p) {
            fwrite(e.imageData.data(), 1, e.imageData.size(), p);
            pclose(p);
        }
    }

    // Broadcast to desktop peers over UDP (fragmented).
    if (udpBroadcaster)
        udpBroadcaster->broadcastEntry(e);

    httpSend(clientFd, 200, "text/plain", "ok");
    ::close(clientFd);
}

static void handleHttpClient(int             clientFd,
                              ClipboardStore& store,
                              SseBroadcaster& sseBroadcaster,
                              UdpBroadcaster* udpBroadcaster) {
    // 60-second receive timeout (large image uploads need time over slow Wi-Fi)
    struct timeval tv { 60, 0 };
    setsockopt(clientFd, SOL_SOCKET, SO_RCVTIMEO,
               reinterpret_cast<const char*>(&tv), sizeof(tv));

    HttpRequest req = parseHttpRequest(clientFd);
    if (!req.valid) { ::close(clientFd); return; }

    // ── GET / ────────────────────────────────────────────────────────────────
    if (req.method == "GET" && req.path == "/") {
        httpSend(clientFd, 200, "text/html; charset=utf-8", PHONE_UI);
        ::close(clientFd); return;
    }

    // ── GET /clipboard ───────────────────────────────────────────────────────
    if (req.method == "GET" && req.path == "/clipboard") {
        httpSend(clientFd, 200, "application/json",
                 clipEntryToJson(store.getNewest()));
        ::close(clientFd); return;
    }

    // ── GET /image ───────────────────────────────────────────────────────────
    if (req.method == "GET" && req.path == "/image") {
        ClipEntry e = store.getNewest();
        if (e.type == ClipType::IMAGE && !e.imageData.empty()) {
            httpSendBinary(clientFd, 200,
                           e.mime.empty() ? "image/jpeg" : e.mime,
                           e.imageData.data(), e.imageData.size());
        } else {
            httpSend(clientFd, 404, "text/plain", "No image in clipboard");
        }
        ::close(clientFd); return;
    }

    // ── GET /ca.crt ──────────────────────────────────────────────────────────
    // Serves the Caddy local CA root certificate so users can install it on
    // their phones and trust the HTTPS connection.
    if (req.method == "GET" && req.path == "/ca.crt") {
        // Try each known path in order.
        static const char* const caPaths[] = {
            CADDY_CA_PATH, CADDY_CA_PATH2, CADDY_CA_PATH3, nullptr
        };
        std::optional<std::vector<uint8_t>> cert;
        for (int i = 0; caPaths[i] != nullptr; ++i) {
            cert = readFileFully(caPaths[i]);
            if (cert) break;
        }
        if (cert) {
            // Content-Disposition: attachment prompts the browser to save/install.
            std::ostringstream hdr;
            hdr << "HTTP/1.1 200 OK\r\n"
                << "Content-Type: application/x-x509-ca-cert\r\n"
                << "Content-Disposition: attachment; filename=\"lan-clipboard-ca.crt\"\r\n"
                << "Content-Length: " << cert->size() << "\r\n"
                << "Access-Control-Allow-Origin: *\r\n"
                << "Connection: close\r\n"
                << "\r\n";
            std::string h = hdr.str();
            ::send(clientFd, h.data(), h.size(), MSG_NOSIGNAL);
            ::send(clientFd, cert->data(), cert->size(), MSG_NOSIGNAL);
        } else {
            httpSend(clientFd, 404, "text/plain",
                     "CA certificate not found.\n"
                     "Run: sudo caddy trust\n"
                     "Expected path: " + std::string(CADDY_CA_PATH));
        }
        ::close(clientFd); return;
    }

    // ── POST /clipboard (text) ────────────────────────────────────────────────
    if (req.method == "POST" && req.path == "/clipboard") {
        std::string text = req.body;
        while (!text.empty() && (text.back() == '\n' || text.back() == '\r'))
            text.pop_back();

        if (!text.empty()) {
            uint64_t    ts      = nowMs();
            std::string phoneId = "phone@web";
            store.updateText(phoneId, text, ts);
            setLocalClipboard(text);

            ClipEntry e;
            e.type = ClipType::TEXT; e.text = text;
            e.mime = "text/plain"; e.deviceId = phoneId; e.timestampMs = ts;

            // Fan-out SSE event.
            sseBroadcaster.broadcast("data: " + clipEntryToJson(e) + "\n\n");

            if (udpBroadcaster)
                udpBroadcaster->broadcastEntry(e);
        }
        httpSend(clientFd, 200, "text/plain", "ok");
        ::close(clientFd); return;
    }

    // ── POST /image  (legacy alias — same as /image-post) ────────────────────
    if (req.method == "POST" && req.path == "/image") {
        handleImageUpload(clientFd, req, store, sseBroadcaster, udpBroadcaster);
        return;
    }

    // ── POST /image-post ──────────────────────────────────────────────────────
    // Dedicated image upload endpoint (used by the phone UI).
    if (req.method == "POST" && req.path == "/image-post") {
        handleImageUpload(clientFd, req, store, sseBroadcaster, udpBroadcaster);
        return;
    }

    // ── GET /events ───────────────────────────────────────────────────────────
    if (req.method == "GET" && req.path == "/events") {
        const char* sseHeader =
            "HTTP/1.1 200 OK\r\n"
            "Content-Type: text/event-stream\r\n"
            "Cache-Control: no-cache\r\n"
            "Access-Control-Allow-Origin: *\r\n"
            "Connection: keep-alive\r\n"
            "\r\n";
        ::send(clientFd, sseHeader, strlen(sseHeader), MSG_NOSIGNAL);
        // Push the current state immediately so the phone doesn't wait.
        std::string first = "data: " + clipEntryToJson(store.getNewest()) + "\n\n";
        ::send(clientFd, first.data(), first.size(), MSG_NOSIGNAL);
        sseBroadcaster.addClient(clientFd);
        return;   // fd now owned by broadcaster — do NOT close here
    }

    // ── 404 ──────────────────────────────────────────────────────────────────
    httpSend(clientFd, 404, "text/plain", "Not found");
    ::close(clientFd);
}

// ═══════════════════════════════════════════════════════════════════════════════
// ─── thread: HTTP server ──────────────────────────────────────────────────────
// ═══════════════════════════════════════════════════════════════════════════════
static void httpServerThread(ClipboardStore&    store,
                              SseBroadcaster&    sseBroadcaster,
                              UdpBroadcaster*    udpBroadcaster,
                              std::atomic<bool>& stop) {
    int serverFd = ::socket(AF_INET, SOCK_STREAM, 0);
    if (serverFd < 0) { std::cerr << "[HTTP] socket() failed\n"; return; }

    int yes = 1;
    setsockopt(serverFd, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof(yes));
    setsockopt(serverFd, SOL_SOCKET, SO_REUSEPORT, &yes, sizeof(yes));

    struct timeval tv { 1, 0 };
    setsockopt(serverFd, SOL_SOCKET, SO_RCVTIMEO,
               reinterpret_cast<const char*>(&tv), sizeof(tv));

    sockaddr_in addr{};
    addr.sin_family      = AF_INET;
    addr.sin_port        = htons(HTTP_PORT);
    addr.sin_addr.s_addr = htonl(INADDR_ANY);

    if (::bind(serverFd, reinterpret_cast<sockaddr*>(&addr), sizeof(addr)) < 0) {
        std::cerr << "[HTTP] bind() failed on port " << HTTP_PORT << "\n";
        ::close(serverFd); return;
    }
    ::listen(serverFd, HTTP_QUEUE_MAX);
    std::cout << "[HTTP] Web UI ready → http://<this-ip>:" << HTTP_PORT << "/\n";
    std::cout << "[HTTP] HTTPS (via Caddy) → https://<this-ip>:8444/\n";

    // ── Bounded thread pool ───────────────────────────────────────────────────
    // All client connections are handled by a fixed pool of worker threads.
    // If the pool queue is full the connection is rejected with 503 rather than
    // spawning an unbounded number of threads.
    HttpThreadPool pool(HTTP_POOL_SIZE);

    while (!stop.load()) {
        sockaddr_in clientAddr{}; socklen_t clientLen = sizeof(clientAddr);
        int clientFd = ::accept(serverFd,
                                reinterpret_cast<sockaddr*>(&clientAddr),
                                &clientLen);
        if (clientFd < 0) continue;   // EAGAIN / timeout — loop and check stop

        bool ok = pool.enqueue([clientFd, &store, &sseBroadcaster, udpBroadcaster]() {
            handleHttpClient(clientFd, store, sseBroadcaster, udpBroadcaster);
        });

        if (!ok) {
            // Pool is full or shutting down — tell the client politely.
            httpSend(clientFd, 503, "text/plain", "Server busy — try again");
            ::close(clientFd);
        }
    }

    // Drain and join all pool workers before returning.
    pool.shutdown();
    ::close(serverFd);
}

// ═══════════════════════════════════════════════════════════════════════════════
// ─── main ─────────────────────────────────────────────────────────────────────
int main() {
    // ── Signal handling ───────────────────────────────────────────────────────
    // SIGPIPE: ignore — broken SSE/TCP connections must not kill the process.
    // SIGINT / SIGTERM: set g_stop so all threads exit their loops cleanly.
    signal(SIGPIPE, SIG_IGN);
    {
        struct sigaction sa{};
        sa.sa_handler = signalHandler;
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = SA_RESTART;
        sigaction(SIGINT,  &sa, nullptr);
        sigaction(SIGTERM, &sa, nullptr);
    }

    const std::string deviceId = makeDeviceId();

    // Discover the machine's primary LAN IP for the startup banner.
    // We do this by connecting a UDP socket (no data sent) and reading getsockname.
    std::string lanIp = "<this-machine-ip>";
    {
        int s = ::socket(AF_INET, SOCK_DGRAM, 0);
        if (s >= 0) {
            sockaddr_in dst{};
            dst.sin_family      = AF_INET;
            dst.sin_port        = htons(53);
            dst.sin_addr.s_addr = inet_addr("8.8.8.8");
            if (::connect(s, reinterpret_cast<sockaddr*>(&dst), sizeof(dst)) == 0) {
                sockaddr_in local{};
                socklen_t   len = sizeof(local);
                if (::getsockname(s, reinterpret_cast<sockaddr*>(&local), &len) == 0) {
                    char buf[INET_ADDRSTRLEN];
                    if (inet_ntop(AF_INET, &local.sin_addr, buf, sizeof(buf)))
                        lanIp = buf;
                }
            }
            ::close(s);
        }
    }

    std::cout << "╔══════════════════════════════════════════════════════╗\n";
    std::cout << "║          LAN Clipboard  (text + image)               ║\n";
    std::cout << "╠══════════════════════════════════════════════════════╣\n";
    std::cout << "  Device ID   : " << deviceId << "\n";
    std::cout << "  UDP port    : " << UDP_PORT  << "\n";
    std::cout << "  HTTP (plain): http://"  << lanIp << ":" << HTTP_PORT << "/\n";
    std::cout << "  HTTPS (Caddy): https://" << lanIp << ":8444/\n";
    std::cout << "  Install CA  : https://" << lanIp << ":8444/ca.crt\n";
    std::cout << "  Press Ctrl+C to stop.\n";
    std::cout << "╚══════════════════════════════════════════════════════╝\n\n";

    ClipboardStore   store;
    SseBroadcaster   sseBroadcaster;
    ReassemblyTable  reassembly;

    // All threads share the global g_stop flag.  We also pass it by reference
    // so the thread functions don't need to access a global directly.
    std::atomic<bool>& stop = g_stop;

    // Seed with current local clipboard
    {
        std::string initial = getLocalClipboard();
        store.updateText(deviceId, initial, nowMs());
        if (!initial.empty())
            std::cout << "[Initial local clipboard]\n" << initial << "\n\n";
        else
            std::cout << "[Local clipboard is currently empty]\n\n";
        std::cout.flush();
    }

    // UDP networking
    std::unique_ptr<UdpBroadcaster> udpBroadcaster;
    std::unique_ptr<UdpListener>    udpListener;
    try {
        udpBroadcaster = std::make_unique<UdpBroadcaster>();
        udpListener    = std::make_unique<UdpListener>(UDP_PORT);
    } catch (const std::exception& ex) {
        std::cerr << "[WARN] UDP setup failed: " << ex.what() << "\n"
                  << "       Desktop peer sync disabled; web UI still works.\n\n";
    }

    std::thread t1, t2, t3, t4;

    if (udpBroadcaster && udpListener) {
        t1 = std::thread(localWatcherThread,
                         std::ref(store), std::ref(*udpBroadcaster),
                         std::cref(deviceId), std::ref(stop));
        t2 = std::thread(udpListenerThread,
                         std::ref(store), std::ref(*udpListener),
                         std::ref(reassembly),
                         std::cref(deviceId), std::ref(stop));
    } else {
        // UDP unavailable — still poll local clipboard for web UI clients.
        t1 = std::thread([&]() {
            std::string last;
            while (!stop.load()) {
                std::this_thread::sleep_for(std::chrono::seconds(1));
                std::string cur = getLocalClipboard();
                if (cur != last) {
                    last = cur;
                    store.updateText(deviceId, cur, nowMs());
                }
            }
        });
    }

    t3 = std::thread(displayThread,
                     std::ref(store), std::ref(sseBroadcaster),
                     std::cref(deviceId), std::ref(stop));

    t4 = std::thread(httpServerThread,
                     std::ref(store), std::ref(sseBroadcaster),
                     udpBroadcaster.get(), std::ref(stop));

    // ── Clean shutdown ────────────────────────────────────────────────────────
    // Join all threads in reverse dependency order.  Each thread's loop exits
    // when stop becomes true (set by SIGINT/SIGTERM via signalHandler).
    if (t4.joinable()) t4.join();
    if (t3.joinable()) t3.join();
    if (t2.joinable()) t2.join();
    if (t1.joinable()) t1.join();

    std::cout << "\n[LAN Clipboard] Stopped cleanly.\n";
    return 0;
}