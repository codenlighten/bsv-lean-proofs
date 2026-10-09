// Driver for bsv::deserialize<int64_t> at v1.2.2 (unmodified header). Input:
// non-empty hex byte strings.
#include "v122/int_serialization.h"
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
        std::printf("%lld\n", static_cast<long long>(bsv::deserialize<int64_t>(v.begin(), v.end())));
    }
}
