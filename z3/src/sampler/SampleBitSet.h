#ifndef _SAMPLE_BIT_SET_H
#define _SAMPLE_BIT_SET_H
#include <cstring>
#include <iostream>
#include <vector>
#include "util/debug.h"

const size_t bit_width = 128;

class SampleBitSet {
   private:
    __int128_t* arr;  // one var take 128 bit
    size_t siz;

    int countOnes(__uint128_t num) {
        int count = 0;
        while (num != 0) {
            count += num & 1;
            num >>= 1;  // Use logical right shift
        }
        return count;
    }

   public:
    SampleBitSet()
        : siz(0) {
        arr = nullptr;
    }
    SampleBitSet(const std::vector<__int128_t>& _arr, size_t _siz)
        : siz(_siz) {
        arr = new __int128_t[siz];
        for (size_t i = 0; i < siz; ++i) {
            arr[i] = _arr[i];
        }
    }
    SampleBitSet(size_t _siz)
        : siz(_siz) {
        arr = new __int128_t[siz]{0};
    }
    SampleBitSet(size_t _siz, __int128_t val)
        : siz(_siz) {
        arr = new __int128_t[siz];
        for (size_t i = 0; i < siz; ++i) {
            arr[i] = val;
        }
    }
    SampleBitSet(const SampleBitSet& bs)
        : siz(bs.siz) {
        arr = new __int128_t[bs.siz]{0};
        memcpy(arr, bs.arr, sizeof(__int128_t) * siz);
    }
    ~SampleBitSet() {
        delete[] arr;
    }
    SampleBitSet& operator=(const SampleBitSet& bs) {
        if (this == &bs)
            return *this;
        delete[] arr;
        siz = bs.siz;
        arr = new __int128_t[siz]{0};
        memcpy(arr, bs.arr, sizeof(__int128_t) * siz);
        return *this;
    }
    SampleBitSet operator^(const SampleBitSet& bs) const {
        SASSERT(this->siz == bs.siz);
        SampleBitSet res(this->siz);
        for (size_t i = 0; i < this->siz; ++i) {
            res.arr[i] = this->arr[i] ^ bs.arr[i];
        }
        return res;
    }
    bool update_arr(const std::vector<__int128_t>& _arr, size_t _siz) {
        delete[] arr;
        arr = new __int128_t[siz];
        for (size_t i = 0; i < siz; ++i) {
            arr[i] = _arr[i];
        }
    }
    bool set(size_t var_idx, size_t bit_idx) {
        __int128_t& t1 = arr[var_idx];
        __int128_t cg = (__int128_t(1) << bit_idx);
        if ((t1 & cg) == __int128_t(0)) {
            t1 |= cg;
            return true;
        }
        return false;
    }
    bool unset(size_t var_idx, size_t bit_idx) {
        __int128_t& t1 = arr[var_idx];
        __int128_t cg = (__int128_t(1) << bit_idx);
        if ((t1 & cg) != 0u) {
            t1 ^= cg;
            return true;
        }
        return false;
    }
    bool get(size_t var_idx, size_t bit_idx) {
        return (arr[var_idx] & (__int128_t(1) << bit_idx)) != __int128_t(0);
    }
    __int128_t get_var(size_t var_idx) const {
        return arr[var_idx];
    }
    int update_bit_change(const std::vector<__int128_t>& curr_solution, const SampleBitSet& last_sample, const SampleBitSet& mask, const int& num_vars) {
        SASSERT(siz == last_sample.siz && siz == mask.siz && siz == num_vars);
        int total_changed_bit = 0;
        for (size_t i = 0; i < siz; ++i) {
            arr[i] = (curr_solution[i] ^ last_sample.arr[i]) & mask.arr[i];
            total_changed_bit += countOnes(arr[i]);
        }
        return total_changed_bit;
    }
};
#endif