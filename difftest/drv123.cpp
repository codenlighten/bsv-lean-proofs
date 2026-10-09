// Differential driver: reads hex byte strings, one per line, and prints what
// bsv::deserialize<int64_t> (v1.2.3 header, unmodified) returns.
#include "v123/int_serialization.h"
#include <cstdio>
#include <iostream>
#include <string>
#include <vector>
int main() {
    std::string line;
    while (std::getline(std::cin, line)) {
        std::vector<uint8_t> v;
        for (size_t i = 0; i + 1 < line.size(); i += 2)
            v.push_back(static_cast<uint8_t>(std::stoi(line.substr(i, 2), nullptr, 16)));
        const auto r = bsv::deserialize<int64_t>(std::span<const uint8_t>{v});
        if (r) std::printf("%lld\n", static_cast<long long>(*r));
        else std::printf("none\n");
    }
}
