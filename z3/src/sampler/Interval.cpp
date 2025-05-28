#include "Interval.h"
#include "util/debug.h"
#include <sstream>
#include <cstring>

namespace sampler {
    // 判断两个区间是否有交集
bool isIntersecting(const Interval& a, const Interval& b) {
    return !(a.end < b.start || b.end < a.start);
}

// 计算两个区间的交集，没有交集则随机返回一个区间
Interval random_intersect(const Interval& a, const Interval& b, std::mt19937& mt) {
    if (a.start > a.end || b.start > b.end){ // 空集的任何交集都为空集
        return Interval(1, 0);
    }
    if (!isIntersecting(a, b)) {
        std::uniform_int_distribution<> dis(0, 1);  // 定义生成0和1的均匀分布
        int random_bit = dis(mt);
        if (random_bit)
            return a;
        else
            return b;
    }
    return Interval(std::max(a.start, b.start), std::min(a.end, b.end));
}

// 计算两个区间的并集
Interval random_unionInterval(const Interval& a, const Interval& b, std::mt19937& mt) {
    if (a.start > a.end && b.start > b.end){ // 两个空集的并集为空集
        return Interval(1, 0);
    }else if (a.start > a.end){
        return b;
    }else if (b.start > b.end){
        return a;
    }
    // 如果两个区间相交或相邻，合并成一个区间
    if (isIntersecting(a, b)) {
        return Interval(std::min(a.start, b.start), std::max(a.end, b.end));
    } else {
        std::uniform_int_distribution<> dis(0, 1);  // 定义生成0和1的均匀分布
        int random_bit = dis(mt);
        if (random_bit)
            return a;
        else
            return b;
    }
}

// 计算区间补集（这里假设补集是计算区间 `a` 相对于 `b` 的补集，意味着 b 是全集）
Interval random_complement(const Interval& a, std::mt19937& mt) {
    if (a.start <= INT64_MIN && a.end >= INT64_MAX){
        return a;
    }
    std::vector<Interval> result;
    Interval b(INT64_MIN, INT64_MAX);

    if (a.start > a.end){ // 空集的补集为全集
        return b;
    }

    if (a.start > b.start) {
        result.push_back(Interval(b.start, a.start));
    }
    if (a.end < b.end) {
        result.push_back(Interval(a.end, b.end));
    }
    SASSERT(result.size() > 0);
    std::uniform_int_distribution<> dis(0, 0);
    int random_bit = dis(mt);
    SASSERT(random_bit >= 0);
    return result[random_bit];
}

// 打印区间
void printInterval(const Interval& interval) {
    std::cout << "[" << interval.start << ", " << interval.end << "]\n";
}

// 打印区间列表
void printIntervals(const std::vector<Interval>& intervals) {
    for (const auto& interval : intervals) {
        printInterval(interval);
        std::cout << " ";
    }
    std::cout << std::endl;
}

}