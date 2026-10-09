// Driver for the reference node's own ComputeMerkleRoot and ComputeMerkleBranch
// (bitcoin-sv src/consensus/merkle.cpp, linked from the reference build's
// libraries, not reimplemented). Input lines: `pos|s1 s2 ... sn`. The leaf for
// symbol k is the 32 bytes k (little-endian in the first four) then zeros.
// Output: root|mutated|branch entries, all as raw-byte hex.
#include "consensus/merkle.h"
#include "uint256.h"
#include "utilstrencodings.h"
#include <cstdio>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
static std::string hex(const uint256& h) { return HexStr(h.begin(), h.end()); }
int main() {
    std::string line;
    while (std::getline(std::cin, line)) {
        const auto bar = line.find('|');
        const uint32_t pos = std::stoul(line.substr(0, bar));
        std::istringstream in(line.substr(bar + 1));
        std::vector<uint256> leaves;
        unsigned long k;
        while (in >> k) {
            uint256 h;
            for (int i = 0; i < 4; i++) *(h.begin() + i) = static_cast<uint8_t>(k >> (8 * i));
            leaves.push_back(h);
        }
        bool mutated = false;
        const uint256 root = ComputeMerkleRoot(leaves, &mutated);
        const auto branch = ComputeMerkleBranch(leaves, pos);
        std::printf("%s|%d|", leaves.empty() ? "-" : hex(root).c_str(), mutated ? 1 : 0);
        for (size_t i = 0; i < branch.size(); i++) std::printf("%s%s", i ? ";" : "", hex(branch[i]).c_str());
        std::printf("\n");
    }
}
