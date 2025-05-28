#pragma once

#include <map>
#include <random>
#include <string>
#include <unordered_set>
#include "sampler.h"

#define LS_MODE
#define CDCL_MODE
#define HYBRID_MODE
#define VERBOSE
#define DEBUG

namespace sampler {

typedef enum {
    LS,
    CDCL,
    HYBRID,
    LS_ITER
} SamplingMode;

struct Hash {
    std::size_t operator()(__int128_t x) const {
        return static_cast<std::size_t>(x ^ (x >> 64));
    }
};

class LiaSampler : public Sampler {
    std::chrono::steady_clock::time_point time_sampling_start;
    size_t num_samples = 0;
    size_t num_ls_samples = 0;
    size_t num_cdcl_samples = 0;
    SamplingMode mode = HYBRID;
    std::mt19937 mt;
    std::random_device rd;
    std::map<std::string, std::string> curr_sample;
    std::vector<__int128_t> curr_sample_val;
    std::unordered_set<__int128_t, Hash> unique_samples_hash_set;
    size_t cdcl_epoch = 1;
    double fixed_var_pct = 0.5;

    double TimeElapsed();
    void print_statistic();

   public:
    LiaSampler(z3::context* _c, std::string _smtFilePath, std::string _samplesFileDir, size_t _maxNumSamples, double _maxTimeLimit, SamplingMode _mode, unsigned seed, size_t _cdclEpoch, double _fixedVarsPct)
        : Sampler(_c, _smtFilePath, _samplesFileDir, _maxNumSamples, _maxTimeLimit), mode(_mode), cdcl_epoch(_cdclEpoch), fixed_var_pct(_fixedVarsPct) {
        mt.seed(seed);
    }


    z3::tactic mk_preamble_tactic(z3::context& ctx);

    void sampling() override;
    void print_unique_sample(std::ofstream& samplesFile);
    void ls_sampling(std::ofstream& samplesFile);
    void cdcl_sampling(std::ofstream& samplesFile);
    void hybrid_sampling(std::ofstream& samplesFile);
    void ls_iterative_sampling(std::ofstream& samplesFile);
    unsigned gen_random_seed();
    void ls_sampling_core(z3::solver& ls_solver, const z3::goal& subgoal);
};
};  // namespace sampler