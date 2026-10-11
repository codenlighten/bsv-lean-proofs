// Driver for the byte-shift comparison. Includes the mask tables, RShift and
// LShift exactly as they are in bitcoin-sv v1.2.3 src/script/interpreter.cpp
// (extracted by shift_compare.sh into shift_src.inc, not kept here).
// Reads "<hex or -> <count>" lines; prints "<LShift hex> <RShift hex>".
#include <array>
#include <cstdint>
#include <cstddef>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
typedef std::vector<uint8_t> valtype;
#include "shift_src.inc"

static std::string hex(const valtype& v) {
    if (v.empty()) return "-";
    static const char* d = "0123456789abcdef";
    std::string s;
    for (uint8_t b : v) { s += d[b >> 4]; s += d[b & 15]; }
    return s;
}

int main() {
    std::string line;
    while (std::getline(std::cin, line)) {
        std::istringstream in(line);
        std::string h; long n;
        in >> h >> n;
        valtype x;
        if (h != "-")
            for (size_t i = 0; i + 1 < h.size(); i += 2)
                x.push_back((uint8_t)std::stoi(h.substr(i, 2), nullptr, 16));
        std::cout << hex(LShift(x, (int)n)) << " " << hex(RShift(x, (int)n)) << "\n";
    }
}
