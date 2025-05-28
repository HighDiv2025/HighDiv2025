#ifndef _INTERVAL_H
#define _INTERVAL_H
#include <iostream>
#include <random>
#include <vector>

namespace sampler {
struct Interval {
    int64_t start, end;
    Interval() : start(INT64_MIN), end(INT64_MAX) {}
    Interval(int64_t s, int64_t e) : start(s), end(e) {}
};
bool isIntersecting(const Interval& a, const Interval& b);
Interval random_intersect(const Interval& a, const Interval& b, std::mt19937& mt);
Interval random_unionInterval(const Interval& a, const Interval& b, std::mt19937& mt);
Interval random_complement(const Interval& a, std::mt19937& mt);
void printInterval(const Interval& interval);
void printIntervals(const std::vector<Interval>& intervals);

}  // namespace sampler
#endif 