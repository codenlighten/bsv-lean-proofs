// Driver for bsv::serialize<int64_t> (v1.2.3 header, unmodified). Input:
// signed decimal values; output: hex.
#include "v123/int_serialization.h"
#include <cstdio>
#include <iostream>
#include <iterator>
#include <string>
#include <vector>
int main() {
    std::string line;
    while (std::getline(std::cin, line)) {
        const int64_t n = std::stoll(line);
        std::vector<uint8_t> out;
        bsv::serialize(n, std::back_inserter(out));
        for (auto b : out) std::printf("%02x", b);
        std::printf("\n");
    }
}
