#include <iostream>
#include <string>
#include <thread>
#include <chrono>
#include <cstdio>
#include <memory>
#include <array>
#include <cstdlib>

std::string runCommand(const std::string& cmd) {
    std::array<char, 4096> buffer{};
    std::string result;

    FILE* pipe = popen(cmd.c_str(), "r");
    if (!pipe) {
        return "";
    }

    while (fgets(buffer.data(), buffer.size(), pipe) != nullptr) {
        result += buffer.data();
    }

    int rc = pclose(pipe);
    if (rc == -1) {
        return "";
    }

    return result;
}

std::string rtrimNewlines(std::string s) {
    while (!s.empty() && (s.back() == '\n' || s.back() == '\r')) {
        s.pop_back();
    }
    return s;
}

std::string getClipboard() {
    std::string data = runCommand("xclip -o -selection clipboard 2>/dev/null");
    if (!data.empty()) {
        return rtrimNewlines(data);
    }

    data = runCommand("wl-paste 2>/dev/null");
    if (!data.empty()) {
        return rtrimNewlines(data);
    }

    return "";
}

int main() {
    std::cout << "Clipboard monitoring started. Content will be printed on every change.\n";
    std::cout << "Press Ctrl+C to stop the program.\n\n";

    std::string lastContent = getClipboard();
    if (!lastContent.empty()) {
        std::cout << "[Initial content detected]\n" << lastContent << "\n\n";
    } else {
        std::cout << "Clipboard is currently empty" << std::endl;
    }

    while (true) {
        std::this_thread::sleep_for(std::chrono::seconds(1));

        std::string current = getClipboard();
        if (current != lastContent) {
            lastContent = current;
            std::cout << "[Clipboard changed]\n";
            if (!current.empty()) {
                std::cout << current << "\n\n";
            } else {
                std::cout << "(Clipboard empty)\n\n";
            }
            std::cout.flush();
        }
    }

    return 0;
}