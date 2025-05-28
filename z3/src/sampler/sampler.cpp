#include "sampler.h"

#include <queue>
#include <regex>
#include <sstream>

namespace sampler {

std::string processNegNumber(const std::string& input) {
    // 定义正则表达式以匹配类似 "(- 4294967281)" 的模式
    std::regex pattern(R"(\(\s*(-\s*\d+)\s*\))");
    std::string result;

    // 使用 std::sregex_iterator 进行匹配和替换
    std::sregex_iterator begin(input.begin(), input.end(), pattern);
    std::sregex_iterator end;

    size_t lastPos = 0;
    for (auto it = begin; it != end; ++it) {
        // 追加匹配前的部分
        result += input.substr(lastPos, it->position() - lastPos);
        // 去掉捕获组中的空格
        std::string number = (*it)[1].str();
        number.erase(std::remove_if(number.begin(), number.end(), ::isspace), number.end());
        // 追加处理后的部分
        result += number;
        // 更新位置
        lastPos = it->position() + it->length();
    }

    // 追加剩余部分
    result += input.substr(lastPos);

    return result;
}

bool startsWith(const std::string& str, const std::string& prefix) {
    // 检查前缀是否比字符串长
    if (prefix.size() > str.size())
        return false;

    // 使用 compare 比较前缀部分
    return str.compare(0, prefix.size(), prefix) == 0;
}

void removePrefix(std::string& str, const std::string& prefix) {
    if (startsWith(str, prefix)) {
        str.erase(0, prefix.size());
    }
}

// 将字符串转换为 __int128_t 的函数
__int128_t string_to_int128(const std::string& str) {
    __int128_t result = 0;
    bool negative = false;

    // 检查是否为负数
    size_t start = 0;
    if (str[0] == '-') {
        negative = true;
        start = 1;
    }
    // 转换字符串为数字
    for (size_t i = start; i < str.length(); ++i) {
        char c = str[i];
        if (c < '0' || c > '9') {
            throw std::invalid_argument("Input string is not a valid number");
        }

        // 将字符转为数字并累积
        result = result * 10 + (c - '0');
    }
    return negative ? -result : result;
}

__int128_t ceil_div(__int128_t numerator, __int128_t denominator, bool is_neg_lit) {
    // 计算商
    __int128_t quotient = numerator / denominator;  // 负数整数除法默认上取整

    // 如果有余数且符号相同，向上取整需要加 1
    if (numerator % denominator != 0 && ((numerator > 0) == (denominator > 0))) {
        quotient += 1;
    } else if (is_neg_lit && numerator % denominator == 0) {
        quotient += 1;
    }

    return quotient;
}

__int128_t floor_div(__int128_t numerator, __int128_t denominator, bool is_neg_lit) {
    // 普通除法
    __int128_t quotient = numerator / denominator;  // 正数整数除法默认下取整

    // 如果符号不同，且有余数，需要调整商向下取整
    if (numerator % denominator != 0 && ((numerator < 0) != (denominator < 0))) {
        quotient -= 1;
    } else if (is_neg_lit && numerator % denominator == 0) {
        quotient -= 1;
    }

    return quotient;
}

std::string extract_filename(const std::string& path) {
    // 找到最后一个 '/' 的位置
    size_t pos = path.find_last_of('/');
    if (pos != std::string::npos) {
        return path.substr(pos + 1);
    }
    return path;  // 如果没有 '/'，假设整个路径就是文件名
}

void ls_sampler::split_string(std::string& in_string, std::vector<std::string>& str_vec, std::string pattern = " ") {
    std::string::size_type pos;
    in_string += pattern;
    size_t size = in_string.size();
    for (size_t i = 0; i < size; i++) {
        pos = in_string.find(pattern, i);
        if (pos < size) {
            std::string s = in_string.substr(i, pos - i);
            str_vec.push_back(s);
            i = pos + pattern.size() - 1;
        }
    }
}

/*
    \brief Construct the corresponding internal variable from the variable name (x --> variable(x))
        and insert variable(x) in _resolution_vars
    Store boolean variables in '_bool_var_vec' and integer variables in '_lia_var_vec',
    so the same index value may be returned for boolean and integer variables
    \reutrn the index of variable(x)
*/

uint64_t ls_sampler::transfer_name_to_resolution_var(std::string& name, bool is_lia, bool in_equal) {
    if (_name2resolution_var.find(name) == _name2resolution_var.end()) {
        _name2resolution_var[name] = _resolution_vars.size();  // name --> idx
        variable var;
        var.clause_idxs.reserve(64);
        var.literals.reserve(64);
        var.literal_clause.reserve(64);
        var.literal_coff.reserve(64);
        var.var_name = name;
        if (var.is_in_equal == false) {
            var.is_in_equal = in_equal;
        }
        var.is_lia = is_lia;
        var.is_in_equal = in_equal;
        _resolution_vars.push_back(var);
        if (is_lia) {
            _lia_var_vec.push_back((int)_resolution_vars.size() - 1);
        } else {
            _bool_var_vec.push_back((int)_resolution_vars.size() - 1);
        }
        return _resolution_vars.size() - 1;
    } else
        return _name2resolution_var[name];
}

/*
   \brief Converting variable names to internal variables (x --> variable(x))
   \return the idx of 'x' in _tmp_vars
   tmp_var 里面存储的全是整数变量
*/
uint64_t ls_sampler::transfer_name_to_tmp_var(std::string& name, bool in_equal) {
    if (_name2tmp_var.find(name) == _name2tmp_var.end()) {
        _name2tmp_var[name] = _tmp_vars.size();
        variable var;
        var.is_lia = true;
        var.var_name = name;
        if (var.is_in_equal == false) {
            var.is_in_equal = in_equal;
        }
        _tmp_vars.push_back(var);
        return _tmp_vars.size() - 1;
    } else
        return _name2tmp_var[name];
}

// transfer the ">" or ">=" to "<="
// ">" It probably doesn't exist.
void ls_sampler::invert_lit(lit& l) {
    l.key = 1 - l.key;
    std::vector<int> tmp_coff_var_idx = l.pos_coff_var_idx;
    std::vector<__int128_t> tmp_coff = l.pos_coff;
    l.pos_coff_var_idx = l.neg_coff_var_idx;
    l.pos_coff = l.neg_coff;
    l.neg_coff_var_idx = tmp_coff_var_idx;
    l.neg_coff = tmp_coff;
}

/*
    \brief build lit to _lits[lit_index]; build var to _tmp_vars[]
*/
void ls_sampler::build_lits(std::string& in_string) {
    std::vector<std::string> vec;
    split_string(in_string, vec);
    if (vec[0] == "0") {
        _lits[0].lits_index = 0;
        return;
    }  // true literal
    int lit_index = std::atoi(vec[0].c_str());
    lit* l = &(_lits[lit_index]);
    if (vec[1] == "or" || vec[1] == "if") {
        l->delta = transfer_name_to_resolution_var(vec[2], false, false);
        l->key = 1;
        l->is_lia_lit = false;
        l->lits_index = lit_index;
        _num_opt++;
        return;
    }  // or term in the form: 1 or newvar_2
    if (vec.size() > 2) {
        l->is_lia_lit = true;
        if (vec.size() > 6) {
            l->lits_index = std::atoi(vec[0].c_str());
            int idx = 5;
            if (vec[2] == "=" && vec[3] != "(") {
                idx++;
                l->key = -std::atoll(vec[3].c_str());
            }
            l->is_equal = (vec[2] == "=");
            for (; idx < vec.size(); idx++) {
                if (vec[idx] == ")") {
                    break;
                }
                if (vec[idx] == "(") {
                    idx += 2;
                    __int128_t coff = std::atoll(vec[idx].c_str());
                    if (coff > 0) {
                        l->pos_coff.push_back(coff);
                        l->pos_coff_var_idx.push_back((int)transfer_name_to_tmp_var(vec[++idx], false));
                    } else {
                        l->neg_coff.push_back(-coff);
                        l->neg_coff_var_idx.push_back((int)transfer_name_to_tmp_var(vec[++idx], false));
                    }
                    idx++;
                } else {
                    l->pos_coff.push_back(1);
                    l->pos_coff_var_idx.push_back((int)transfer_name_to_tmp_var(vec[idx], false));
                }
                _num_opt += l->pos_coff.size();
                _num_opt += l->neg_coff.size();
            }
            if (vec[2] != "=" || vec[3] == "(") {
                l->key = -std::atoll(vec[++idx].c_str());
            }
            if (vec[2] == ">=") {
                l->key++;
                invert_lit(*l);
            }
        }  //( <= ( + x1 ( * -1 x2 ) x7 ( * -1 x8 ) ) 0 )
        else {
            l->lits_index = std::atoi(vec[0].c_str());
            __int128_t bound = std::atoll(vec[4].c_str());
            uint64_t var_idx = transfer_name_to_tmp_var(vec[3], false);
            if (vec[2] == ">=") {
                l->key = bound;
                l->neg_coff.push_back(1);
                l->neg_coff_var_idx.push_back((int)var_idx);
            } else {
                l->key = -bound;
                l->pos_coff.push_back(1);
                l->pos_coff_var_idx.push_back((int)var_idx);
            }
            l->is_equal = (vec[2] == "=");
            _num_opt += 2;
        }  //( >= x 0 )

    }  // lia lit
    else {
        l->delta = transfer_name_to_resolution_var(vec[1], false, false);
        l->key = 1;
        l->is_lia_lit = false;
        l->lits_index = lit_index;
        _num_opt++;
    }  // boolean lit
}

void ls_sampler::free_space() {
    delete _unsat_clauses;
    delete _lit_occur;
    delete _sat_clause_with_false_literal;
    delete _contain_bool_unsat_clauses;
    delete pair_x;
    delete pair_y;
}

void ls_sampler::make_space() {
    _solution.resize(_num_vars + _additional_len);
    _best_solutin.resize(_num_vars + _additional_len);
    // _final_solution.resize(_num_vars + _additional_len);
    _tabulist.resize(2 * _num_vars + _additional_len, 0);
    _CClist.resize(2 * _num_vars + _additional_len, 1);
    _operation_var_idx_vec.resize(_num_opt + _additional_len);
    _operation_var_idx_bool_vec.resize(_num_opt + _additional_len);
    _operation_lit_idx_vec.resize(_num_opt + _additional_len);
    _operation_change_value_vec.resize(_num_opt + _additional_len);
    _last_move.resize(2 * _num_vars + _additional_len, 0);
    _unsat_clauses = new Array((int)_num_clauses + (int)_additional_len);
    _sat_clause_with_false_literal = new Array((int)_num_clauses + (int)_additional_len);
    _lit_occur = new Array((int)_num_lits);
    _contain_bool_unsat_clauses = new Array((int)_num_clauses);
    _is_chosen_bool_var.resize(_num_vars + _additional_len, false);
}

void ls_sampler::calc_var_intervals() {
    _vars_initialization_intervals.resize(_vars.size());
    std::vector<__int128_t> cdcl_solution(_vars.size(), 0);
    __int128_t delta;
    __int128_t coff_val, term_val;
    std::string pair_x_name;
    std::string pair_y_name;
    variable* var_x;
    variable* var_y;
    int l_sign_idx, l_idx, c_idx;
    std::unordered_map<int, int> pair_x_to_y;

    for (size_t v_idx = 0; v_idx < _vars.size(); ++v_idx) {
        if (startsWith(_vars[v_idx].var_name, "_new_var_")) {
            pair_x_name = _vars[v_idx].var_name;
            removePrefix(pair_x_name, "_new_var_");

            pair_y_name = _tmp_vars[pair_y->element_at(pair_x->index_of(_name2tmp_var[pair_x_name]))].var_name;

            if (last_cdcl_model.find(pair_x_name) != last_cdcl_model.end() && last_cdcl_model.find(pair_y_name) != last_cdcl_model.end()) {
                cdcl_solution[v_idx] = string_to_int128(processNegNumber(last_cdcl_model[pair_x_name])) - string_to_int128(processNegNumber(last_cdcl_model[pair_y_name]));
            }
        } else if (last_cdcl_model.find(_vars[v_idx].var_name) != last_cdcl_model.end()) {
            cdcl_solution[v_idx] = string_to_int128(processNegNumber(last_cdcl_model[_vars[v_idx].var_name]));
        }
    }

    for (size_t v_idx = 0; v_idx < _vars.size(); ++v_idx) {
        std::vector<Interval> var_intervals;
        Interval interval;
        variable* var = &(_vars[v_idx]);
        if (!var->is_lia) {
            continue;
        }
        for (size_t i = 0; i < var->clause_idxs.size(); ++i) {
            c_idx = var->clause_idxs[i];  // maybe negative
            clause* cl = &_clauses[c_idx];
            Interval interval_cl(1, 0);  // 空集
            SASSERT(cl->literals.size() > 0);
            for (size_t j = 0; j < cl->literals.size(); ++j) {
                l_sign_idx = cl->literals[j];
                l_idx = std::abs(l_sign_idx);
                lit* l = &(_lits[l_idx]);
                if (l->lits_index == 0 || !l->is_lia_lit || l->is_equal || !_lit_appear[l_idx])
                    continue;
                SASSERT(l_sign_idx > 0);
                delta = delta_lit_by_cdcl_model(*l, cdcl_solution);
                if ((delta <= 0 && l_sign_idx > 0) || (delta > 0 && l_sign_idx < 0)) {
                    coff_val = var->literal_coff[i];
                    term_val = coff_val * cdcl_solution[v_idx];
                    // 计算区间上界
                    if ((l_sign_idx > 0 && coff_val > 0) || (l_sign_idx < 0 && coff_val < 0)) {  // coff * x + delta' <= 0 --> x <= (val(x) - delta) / coff
                        __int128_t tmp_upper_bound = floor_div((term_val - delta), coff_val, (l_sign_idx < 0));
                        interval = Interval(neg_inf_64, tmp_upper_bound);
                    }
                    // 计算区间下界
                    if ((l_sign_idx > 0 && coff_val < 0) || (l_sign_idx < 0 && coff_val > 0)) {  // coff * x + delta' <= 0 --> x >= (val(x) - delta) / coff
                        __int128_t tmp_lower_bound = ceil_div((term_val - delta), coff_val, (l_sign_idx < 0));
                        interval = Interval(tmp_lower_bound, pos_inf_64);
                    }
                }
                interval_cl = random_unionInterval(interval, interval_cl, mt);
            }
            // SASSERT(interval_cl.start <= interval_cl.end);
            if (interval_cl.start <= interval_cl.end) {
                var_intervals.push_back(interval_cl);
            }
        }

        Interval res_interval(neg_inf_64, pos_inf_64);

#if !defined(INIT_VAR_V2) && !defined(INIT_VAR_V3)
        for (auto interval : var_intervals) {
            if (var->in_occs_closure) {  // 收敛
                res_interval = random_intersect(res_interval, interval, mt);
            }
        }
        if (!var->in_occs_closure) {
            res_interval = random_complement(res_interval, mt);
        }
#endif

#ifdef INIT_VAR_V2
        for (auto interval : var_intervals) {
            res_interval = random_intersect(res_interval, interval, mt);
        }
#endif

#ifdef INIT_VAR_V3
        for (auto interval : var_intervals) {
            res_interval = random_intersect(res_interval, interval, mt);
        }
        res_interval = random_complement(res_interval, mt);
#endif
        _vars_initialization_intervals[v_idx] = res_interval;
    }
}

void ls_sampler::initialize() {
    clear_prev_data();
    construct_solution_score();  // Initializing a variable to take a value
    initialize_lit_datas();
    initialize_clause_datas();
    initialize_variable_datas();
    best_found_this_restart = _unsat_clauses->size();
    update_best_solution();
#if !defined(BAM_V2) && !defined(BAM_V1) 
    if (_use_interval_move) {
        update_literals_sat_steps_count();
    }
#endif
}

void ls_sampler::clear_prev_data() {
    // equal_move_cnt = 0;
    for (int v : _bool_var_vec) {
        _vars[v].score = 0;
    }
    _best_found_hard_cost_this_bool = INT32_MAX;
    _best_found_hard_cost_this_lia = INT32_MAX;
    _no_improve_cnt_bool = 0;
    _no_improve_cnt_lia = 0;
    pair_x_value.clear();
    pair_y_value.clear();

    for (auto l : _lits) {
        l.sat_steps_count = 0;
    }

    // _unsat_clauses->clear();
    // _contain_bool_unsat_clauses->clear();
    // _sat_clause_with_false_literal->clear();
    // SASSERT(_vars.size() == _bak_vars.size());

    // _num_vars = _vars.size();
}

__int128_t ls_sampler::random_int128_in_range(__int128_t left, __int128_t right) {
    std::uniform_int_distribution<uint64_t> distr;
    // 生成两个随机的 64 位数，组合成一个128位的随机数
    uint64_t high = mt();
    uint64_t low = mt();
    __int128_t random_number = (static_cast<__int128_t>(high) << 64) | low;

    // 调整符号 [-2^127, 2^127 - 1]
    __int128_t offset = static_cast<__int128_t>(1) << 127;
    __int128_t signed_random_number;
    is_overflow = __builtin_sub_overflow(random_number, offset, &signed_random_number);

    // 映射到指定的范围 [min, max]
    __int128_t range = right - left + 1;

    // 当随机数或范围涉及负数时，使用这种方法确保结果正确
    __int128_t scaled_random = left + ((signed_random_number % range + range) % range);

    SASSERT(scaled_random >= left && scaled_random <= right);
    return scaled_random;
}

int64_t ls_sampler::random_int64_in_range(int64_t left, int64_t right) {
    // Validate the parameters
    if (left > right) {
        throw std::invalid_argument("Invalid range: left must be less than or equal to right.");
    }

    // Define uniform distribution for the range [left, right]
    std::uniform_int_distribution<int64_t> dist(left, right);

    // Generate and return the random integer
    int64_t res = dist(mt);
    SASSERT(res >= left && res <= right);
    return res;
}

// construction
void ls_sampler::construct_solution_score() {
    for (int i = 0; i < _num_vars; i++) {
        if (!_vars[i].is_lia) {
            if (mt() % 2 == 1) {
                _solution[i] = 1;
            } else {
                _solution[i] = -1;
            }
            continue;
        }
        if (_vars[i].low_bound != -max_int) {
            _vars[i].s_lower_bound = _vars[i].low_bound;
        }
        if (_vars[i].upper_bound != max_int) {
            _vars[i].s_upper_bound = _vars[i].upper_bound;
        }

        __int64_t s_lower_bound = _vars[i].s_lower_bound;
        __int64_t s_upper_bound = _vars[i].s_upper_bound;

#if defined(INIT_VAR_V1) || defined(BAM_V2) || defined(BAM_V1)
        if (_vars[i].low_bound > 0)
            _solution[i] = _vars[i].low_bound;
        else if (_vars[i].upper_bound < 0)
            _solution[i] = _vars[i].upper_bound;
        else
            _solution[i] = 0;
        continue;
#endif

#if defined(INIT_VAR_V2) || defined(INIT_VAR_V3)
        if (_vars_initialization_intervals[i].start > _vars_initialization_intervals[i].end) {
            if (_vars[i].low_bound > 0)
                _solution[i] = _vars[i].low_bound;
            else if (_vars[i].upper_bound < 0)
                _solution[i] = _vars[i].upper_bound;
            else
                _solution[i] = 0;
        } else {
            _solution[i] = random_int64_in_range(std::max(s_lower_bound, _vars_initialization_intervals[i].start), std::min(s_upper_bound, _vars_initialization_intervals[i].end));
        }
#endif

#ifdef INIT_VAR_V4
        _solution[i] = random_int64_in_range(s_lower_bound, s_upper_bound);
#endif

#if !defined(INIT_VAR_V1) && !defined(INIT_VAR_V2) && !defined(INIT_VAR_V3) && !defined(INIT_VAR_V4)
        if (_vars[i].in_equal_closure) {  //  || _vars[i].in_occs_closure
            if (_vars[i].low_bound > 0)
                _solution[i] = _vars[i].low_bound;
            else if (_vars[i].upper_bound < 0)
                _solution[i] = _vars[i].upper_bound;
            else
                _solution[i] = 0;
        } else if (is_pb){
            std::uniform_int_distribution<int> d(0, 1);
            _solution[i] = d(mt);
        }else {
            _solution[i] = random_int64_in_range(std::max(s_lower_bound, _vars_initialization_intervals[i].start), std::min(s_upper_bound, _vars_initialization_intervals[i].end));
        }
        TRACE("sampler",
              tout << "is occs closure var: " << _vars[i].in_occs_closure << "\n";
              tout << "is equal closure var: " << _vars[i].in_equal_closure << "\n";
              tout << "initialization_intervals: [" << print_128(_vars_initialization_intervals[i].start) << ", " << print_128(_vars_initialization_intervals[i].end) << "]\n";
              tout << "boundary intervals: [" << print_128(s_lower_bound) << ", " << print_128(s_upper_bound) << "]\n";
              tout << _vars[i].var_name << " = " << print_128(_solution[i]) << "\n";);
#endif
    }
}

double ls_sampler::TimeElapsed_total() {
    std::chrono::steady_clock::time_point finish = std::chrono::steady_clock::now();
    std::chrono::duration<double> duration = finish - _total_start;
    return duration.count();
}

bool ls_sampler::update_best_solution() {
    bool improve = false;
    if (_unsat_clauses->size() < best_found_this_restart) {
        improve = true;
        best_found_this_restart = _unsat_clauses->size();
    }
    if (_unsat_clauses->size() < _best_found_cost) {
        improve = true;
        _best_found_cost = _unsat_clauses->size();
        _best_cost_time = TimeElapsed_total();
    }
    return improve;
}

void ls_sampler::initialize_variable_datas() {
}

// initialize the delta of each literal by delta_lit operation
void ls_sampler::initialize_lit_datas() {
    for (uint64_t i = 0; i < _num_lits; i++) {
        if (_lits[i].lits_index != 0 && _lits[i].is_lia_lit) {
            _lits[i].delta = delta_lit(_lits[i]);
        }
    }
}

// set the sat num of each clause, and sat/unsat a clause
void ls_sampler::initialize_clause_datas() {
    _lit_in_unsat_clause_num = 0;
    _bool_lit_in_unsat_clause_num = 0;
    __int128_t pos_delta;
    for (uint64_t c = 0; c < _num_clauses; c++) {
        clause* cl = &(_clauses[c]);
        cl->sat_count = 0;                // 子句中已被满足的文字数
        cl->weight = 1;                   // 子句权重
        cl->min_delta = max_int;          // 子句中所有文字的最小 delta
        for (int l_idx : cl->literals) {  // 遍历子句中的文字
            __int128_t delta = _lits[std::abs(l_idx)].delta;
            bool is_equal = _lits[std::abs(l_idx)].is_equal;
            if (!_lits[std::abs(l_idx)].is_lia_lit) {
                if ((_solution[delta] > 0 && l_idx > 0) || (_solution[delta] < 0 && l_idx < 0)) {
                    cl->sat_count++;
                }
            }  // bool lit
            else if ((!is_equal && ((delta <= 0 && l_idx > 0) || (delta > 0 && l_idx < 0))) || (is_equal && ((delta == 0 && l_idx > 0) || (delta != 0 && l_idx < 0)))) {
                cl->sat_count++;
            }  // lia lit
            pos_delta = delta;
            convert_to_pos_delta(pos_delta, l_idx);
            if (pos_delta < cl->min_delta) {
                cl->min_delta = pos_delta;
                cl->min_delta_lit_index = l_idx;
            }
        }
        if (cl->sat_count == 0) {
            unsat_a_clause(c);
            _lit_in_unsat_clause_num += _clauses[c].literals.size();
            _bool_lit_in_unsat_clause_num += _clauses[c].bool_literals.size();
            for (int l_sign_idx : cl->bool_literals) {
                _vars[_lits[std::abs(l_sign_idx)].delta].score++;
            }
        } else {
            sat_a_clause(c);
        }
        if (cl->sat_count > 0 && cl->sat_count < cl->literals.size()) {
            _sat_clause_with_false_literal->insert_element((int)c);
        }
        // TODO::else{sat_clause_with_false_literal->delete_element((int)c);}
        if (cl->sat_count == 1) {
            lit* l = &(_lits[std::abs(cl->min_delta_lit_index)]);
            if (!l->is_lia_lit) {
                _vars[l->delta].score--;
            }
        }
    }
    _total_clause_weight = _num_clauses;
}

// all coffs are positive, go through all terms of the literal
__int128_t ls_sampler::delta_lit(lit& l) {
    __int128_t delta = l.key;
    __int128_t tmp;
    for (int i = 0; i < l.pos_coff.size(); i++) {
        is_overflow = __builtin_mul_overflow(l.pos_coff[i], _solution[l.pos_coff_var_idx[i]], &tmp) || is_overflow;
        // SASSERT(!is_overflow);
        is_overflow = __builtin_add_overflow(delta, tmp, &delta) || is_overflow;
        // SASSERT(!is_overflow);
        // delta += (l.pos_coff[i] * _solution[l.pos_coff_var_idx[i]]);
    }
    for (int i = 0; i < l.neg_coff.size(); i++) {
        is_overflow = __builtin_mul_overflow(l.neg_coff[i], _solution[l.neg_coff_var_idx[i]], &tmp) || is_overflow;
        // SASSERT(!is_overflow);
        is_overflow = __builtin_sub_overflow(delta, tmp, &delta) || is_overflow;
        // SASSERT(!is_overflow);
        // delta -= (l.neg_coff[i] * _solution[l.neg_coff_var_idx[i]]);
    }

    if (is_overflow && !update_sampling_interval) {
        shrinkSampleInterval(&l);
    }

    return delta;
}

__int128_t ls_sampler::delta_lit_by_cdcl_model(lit& l, const std::vector<__int128_t>& cdcl_solution) {
    __int128_t delta = l.key;
    __int128_t tmp;
    for (int i = 0; i < l.pos_coff.size(); i++) {
        is_overflow = __builtin_mul_overflow(l.pos_coff[i], cdcl_solution[l.pos_coff_var_idx[i]], &tmp) || is_overflow;
        is_overflow = __builtin_add_overflow(delta, tmp, &delta) || is_overflow;
    }
    for (int i = 0; i < l.neg_coff.size(); i++) {
        is_overflow = __builtin_mul_overflow(l.neg_coff[i], cdcl_solution[l.neg_coff_var_idx[i]], &tmp) || is_overflow;
        is_overflow = __builtin_sub_overflow(delta, tmp, &delta) || is_overflow;
    }

    if (is_overflow && !update_sampling_interval) {
        shrinkSampleInterval(&l);
    }

    return delta;
}

void ls_sampler::shrinkSampleInterval(lit* l) {
    double alpha = 0.9;
    update_sampling_interval = true;
    for (int i = 0; i < l->pos_coff.size(); ++i) {
        __int128_t sampling_lower_bound = _vars[l->pos_coff_var_idx[i]].s_lower_bound;
        __int128_t sampling_upper_bound = _vars[l->pos_coff_var_idx[i]].s_upper_bound;

        __int128_t lower_bound = _vars[l->pos_coff_var_idx[i]].low_bound;
        __int128_t upper_bound = _vars[l->pos_coff_var_idx[i]].upper_bound;

        __int128_t mid = (sampling_lower_bound + sampling_upper_bound) >> 1;
        __int128_t old_range = sampling_upper_bound - sampling_lower_bound;

        __int128_t new_sampling_lower_bound = mid - alpha * (old_range >> 1);
        __int128_t new_sampling_upper_bound = mid + alpha * (old_range >> 1);

        if (lower_bound <= new_sampling_lower_bound && new_sampling_lower_bound < upper_bound) {
            _vars[l->pos_coff_var_idx[i]].s_lower_bound = new_sampling_lower_bound;
        }
        if (upper_bound >= new_sampling_upper_bound && lower_bound <= new_sampling_lower_bound) {
            _vars[l->pos_coff_var_idx[i]].s_upper_bound = new_sampling_upper_bound;
        }
    }

    for (int i = 0; i < l->neg_coff.size(); ++i) {
        __int128_t sampling_lower_bound = _vars[l->neg_coff_var_idx[i]].s_lower_bound;
        __int128_t sampling_upper_bound = _vars[l->neg_coff_var_idx[i]].s_upper_bound;

        __int128_t lower_bound = _vars[l->neg_coff_var_idx[i]].low_bound;
        __int128_t upper_bound = _vars[l->neg_coff_var_idx[i]].upper_bound;

        __int128_t mid = (sampling_lower_bound + sampling_upper_bound) >> 1;
        __int128_t old_range = sampling_upper_bound - sampling_lower_bound;

        __int128_t new_sampling_lower_bound = mid - alpha * (old_range >> 1);
        __int128_t new_sampling_upper_bound = mid + alpha * (old_range >> 1);

        if (lower_bound <= new_sampling_lower_bound && new_sampling_lower_bound < upper_bound) {
            _vars[l->neg_coff_var_idx[i]].s_lower_bound = new_sampling_lower_bound;
        }
        if (upper_bound >= new_sampling_upper_bound && lower_bound <= new_sampling_lower_bound) {
            _vars[l->neg_coff_var_idx[i]].s_upper_bound = new_sampling_upper_bound;
        }
    }
}

// Distance to True of literal: dtt
void ls_sampler::convert_to_pos_delta(__int128_t& delta, int l_idx) {
    lit* l = &(_lits[std::abs(l_idx)]);
    if (l->is_lia_lit) {
        if (l->is_equal) {
            if ((delta == 0 && l_idx > 0) || (delta != 0 && l_idx < 0)) {  // sat
                delta = 0;
            } else {  // unsat
                delta = 1;
            }
        } else {
            if (l_idx < 0) {        // negative lit requires (delta > 0)
                delta = 1 - delta;  // (delta > 0) --> (1-delta <= 0)
            }
            if (delta < 0) {  // max{delta, 0}
                delta = 0;
            }
        }
    } else {
        __int128_t var_idx = l->delta;
        delta = ((_solution[var_idx] > 0 && l_idx > 0) || (_solution[var_idx] < 0 && l_idx < 0)) ? 0 : 1;
    }
}

void ls_sampler::build_neighbor() {
}

/*
    \brief Unit propagation only for boolean variables
*/
void ls_sampler::unit_prop() {
    std::stack<uint64_t> unit_clause;                                         // the var_idx in the unit clause
    for (uint64_t clause_idx = 0; clause_idx < _num_clauses; clause_idx++) {  // the unit clause is the undeleted clause containing only one bool var
        if (!_clauses[clause_idx].is_delete && _clauses[clause_idx].literals.size() == 1 && !_lits[std::abs(_clauses[clause_idx].literals[0])].is_lia_lit) {
            unit_clause.push(clause_idx);
        }
    }

    while (!unit_clause.empty()) {
        uint64_t unit_clause_idx = unit_clause.top();
        unit_clause.pop();
        if (_clauses[unit_clause_idx].is_delete) {
            continue;
        }

        int is_pos_lit = (_clauses[unit_clause_idx].literals[0] > 0) ? 1 : -1;             // the sign of the var in unit clause
        uint64_t unit_var = _lits[std::abs(_clauses[unit_clause_idx].literals[0])].delta;  // the unit_var's idx in _resolution_vars
        _resolution_vars[unit_var].is_delete = true;                                       // delete the unit var
        _resolution_vars[unit_var].up_bool = is_pos_lit;                                   // set the solution of a boolean var as its unit propogation value

        for (uint64_t cl_idx : _resolution_vars[unit_var].clause_idxs) {  // All clauses containing unit_var
            clause* cl = &(_clauses[cl_idx]);
            if (cl->is_delete)
                continue;
            for (uint64_t lit_idx = 0; lit_idx < cl->literals.size(); lit_idx++) {  // Iterate over the clause
                int l_id_in_lits = cl->literals[lit_idx];
                lit* l = &(_lits[std::abs(l_id_in_lits)]);
                if (!l->is_lia_lit && l->delta == unit_var) {                                            // go through the clauses of the unit var, find the var in corresponding clause
                    if ((is_pos_lit > 0 && l_id_in_lits > 0) || (is_pos_lit < 0 && l_id_in_lits < 0)) {  // positive literal with var is assigned true;
                                                                                                         // negative literal with var is assigned false.

                        cl->is_delete = true;
                        for (int l_idx_inner : cl->literals) {  // delete the clause from corresponding bool var
                            lit* l_inner = &(_lits[std::abs(l_idx_inner)]);
                            if (!l_inner->is_lia_lit && l_inner->delta != unit_var) {
                                variable* var_inner = &(_resolution_vars[l_inner->delta]);                                 // The remaining vars in the clause
                                for (uint64_t delete_idx = 0; delete_idx < var_inner->clause_idxs.size(); delete_idx++) {  // Delete the clause in the set of clauses in which it resides
                                    if (var_inner->clause_idxs[delete_idx] == cl_idx) {
                                        var_inner->clause_idxs[delete_idx] = var_inner->clause_idxs.back();  // 复制末尾元素
                                        var_inner->clause_idxs.pop_back();                                   // 删除末尾元素
                                        break;
                                    }
                                }
                            }
                        }
                    }  // if there exist same lit, the clause is already set true, then delete the clause
                    else {
                        cl->literals[lit_idx] = cl->literals.back();  // 复制末尾元素
                        cl->literals.pop_back();                      // 删除末尾元素
                        if (cl->literals.size() == 1 && !_lits[std::abs(cl->literals[0])].is_lia_lit) {
                            unit_clause.push(cl_idx);
                        }  // if after deleting, it becomes unit clause
                    }  // else delete the lit, falsied a clause.
                    break;
                }
            }
        }
    }
}

void ls_sampler::resolution() {
    std::vector<uint64_t> pos_clauses(10 * _num_clauses);  // 正文字子句 (p \or  q)
    std::vector<uint64_t> neg_clauses(10 * _num_clauses);  // 负文字子句 (\neg p \or q)
    int pos_clause_size, neg_clause_size;
    bool is_improve = true;
    while (is_improve) {
        is_improve = false;
        for (uint64_t bool_var_idx : _bool_var_vec) {  // sequentially resolve all Boolean variables
            if (_resolution_vars[bool_var_idx].is_delete)
                continue;  // skip variables that have already been deleted
            pos_clause_size = 0;
            neg_clause_size = 0;
            for (int i = 0; i < _resolution_vars[bool_var_idx].clause_idxs.size(); i++) {  // record the clauses in which the var has a positive/negative occurrence.
                uint64_t clause_idx = _resolution_vars[bool_var_idx].clause_idxs[i];
                if (_clauses[clause_idx].is_delete)
                    continue;  // skip clauses that have already been deleted
                for (int l_var_sign : _clauses[clause_idx].literals) {
                    int l_idx = std::abs(l_var_sign);
                    if (!_lits[l_idx].is_lia_lit && _lits[l_idx].delta == bool_var_idx) {  // make sure that it is a boolean literal and is exactly the one containing the var
                        if (l_var_sign > 0) {
                            pos_clauses[pos_clause_size++] = clause_idx;
                        } else {
                            neg_clauses[neg_clause_size++] = clause_idx;
                        }
                        break;
                    }
                }
            }  // determine the pos_clause and neg_clause
            // 统计永真式数量
            int tautology_num = 0;
            for (int i = 0; i < pos_clause_size; i++) {    // pos clause X neg clause (Cartesian product)
                uint64_t pos_clause_idx = pos_clauses[i];  // 拿出一个正子句
                for (int j = 0; j < neg_clause_size; j++) {
                    uint64_t neg_clause_idx = neg_clauses[j];                             // 拿出一个负子句
                    for (int k = 0; k < _clauses[neg_clause_idx].literals.size(); k++) {  // 遍历负子句中的文字
                        int l_neg_lit = _clauses[neg_clause_idx].literals[k];
                        int l_idx = std::abs(l_neg_lit);
                        if (_lits[l_idx].delta != bool_var_idx || _lits[l_idx].is_lia_lit) {  // the bool_var for resolution is not considered(that is \neg ( the lit is bool lit and it contains the var))
                            for (int l_pos_lit : _clauses[pos_clause_idx].literals) {
                                if (-l_neg_lit == (l_pos_lit)) {  // 若除了本轮归结变量外，还存在其他归结变量，可获取永真式
                                    tautology_num++;
                                    break;
                                }  // if there exists (a V b V c) \and (-a V -b V d), the new clause (b V -b V c V d) is tautology.
                            }
                        }
                    }
                }
            }
            // 若归结后产生的式子超过原本的式子数，则不做本轮归结
            if ((pos_clause_size * neg_clause_size - tautology_num) > (pos_clause_size + neg_clause_size)) {
                continue;
            }  // if deleting the var can cause 2 times clauses, then skip it
            // 开始归结
            // 这里不能删除归结子句，会导致解空间变化
            // 双向删除，标记删除归结子句，更新子句中每个布尔变量的子句列表
            for (uint64_t clause_idx : _resolution_vars[bool_var_idx].clause_idxs) {  // delete the clauses with bool_var
                _clauses[clause_idx].is_delete = true;
                for (int l_idx_sign : _clauses[clause_idx].literals) {  // delete the clause from corresponding bool var
                    lit* l = &(_lits[std::abs(l_idx_sign)]);
                    if (!l->is_lia_lit && l->delta != bool_var_idx) {
                        variable* var_inner = &(_resolution_vars[l->delta]);                                       // 操作归结子句中的其他变量
                        for (uint64_t delete_idx = 0; delete_idx < var_inner->clause_idxs.size(); delete_idx++) {  // 更新被删除子句中每个布尔变量的子句列表
                            if (var_inner->clause_idxs[delete_idx] == clause_idx) {
                                var_inner->clause_idxs[delete_idx] = var_inner->clause_idxs.back();  // 赋值表尾元素
                                var_inner->clause_idxs.pop_back();                                   // 删除表尾元素
                                break;
                            }
                        }
                    }
                }
            }

            is_improve = true;                                // 本次存在归结
            _resolution_vars[bool_var_idx].is_delete = true;  // 删除被归结的变量

            // 纯文字跳过
            if (pos_clause_size == 0 || neg_clause_size == 0)
                continue;  // pos or neg clause is empty, meaning the clauses are SAT when assigned to true or false, then cannot resolute, just delete the clause

            for (int i = 0; i < pos_clause_size; i++) {    // pos clause X neg clause
                uint64_t pos_clause_idx = pos_clauses[i];  // Already deleted.
                for (int j = 0; j < neg_clause_size; j++) {
                    uint64_t neg_clause_idx = neg_clauses[j];  // Already deleted.
                    clause new_clause;                         // 归结后产生的新子句
                    uint64_t pos_lit_size = _clauses[pos_clause_idx].literals.size();
                    uint64_t neg_lit_size = _clauses[neg_clause_idx].literals.size();
                    new_clause.literals.reserve(pos_lit_size + neg_lit_size);
                    bool is_tautology = false;                // 判断是否为永真式
                    for (int k = 0; k < pos_lit_size; k++) {  // 遍历正子句中各文字
                        int l_sign_idx = _clauses[pos_clause_idx].literals[k];
                        int l_idx = std::abs(l_sign_idx);
                        if (_lits[l_idx].is_lia_lit || _lits[l_idx].delta != bool_var_idx) {  // lia 文字 或 非归结变量
                            new_clause.literals.push_back(l_sign_idx);                        // 存入新子句
                        }
                    }  // add the lits in pos clause to new clause
                    for (int k = 0; k < neg_lit_size; k++) {  // non-equivalence transformation.
                        int l_sign_idx = _clauses[neg_clause_idx].literals[k];
                        if (_lits[std::abs(l_sign_idx)].is_lia_lit || _lits[std::abs(l_sign_idx)].delta != bool_var_idx) {
                            bool is_existed_lit = false;
                            for (uint64_t i = 0; i < pos_lit_size - 1; i++) {
                                if (l_sign_idx == (new_clause.literals[i])) {
                                    is_existed_lit = true;
                                    break;
                                }  // if the lit has existed, then it will not be added
                                if (l_sign_idx == (-new_clause.literals[i])) {
                                    is_tautology = true;
                                    break;
                                }  // if there exists (a V b) ^ (-a V -b), the new clause is tautology
                            }
                            if (is_tautology) {
                                break;
                            }
                            if (!is_existed_lit) {
                                new_clause.literals.push_back(l_sign_idx);
                            }
                        }
                    }
                    if (!is_tautology) {  // add new clause, and modify the clause of corresponding bool var
                        for (int l_sign_idx : new_clause.literals) {
                            lit* l_inner = &(_lits[std::abs(l_sign_idx)]);
                            if (!l_inner->is_lia_lit) {
                                _resolution_vars[l_inner->delta].clause_idxs.push_back((int)_num_clauses);
                            }
                        }
                        _clauses.push_back(new_clause);
                        _num_clauses++;
                    }
                }
            }
            for (int i = 0; i < pos_clause_size; i++) {  // remove bool_var_idx from all positive clause
                clause pos_cl = _clauses[pos_clauses[i]];
                for (int j = 0; j < pos_cl.literals.size(); j++) {
                    int l_idx = pos_cl.literals[j];
                    lit* l = &(_lits[std::abs(l_idx)]);
                    if (!l->is_lia_lit && l->delta == bool_var_idx) {
                        pos_cl.literals[j] = pos_cl.literals[0];  // 复制尾元素
                        pos_cl.literals[0] = l_idx;               // 删除尾元素
                        break;
                    }
                }
                _reconstruct_stack.push(pos_cl);
            }
            for (int i = 0; i < neg_clause_size; i++) {  // remove bool_var_idx from all negative clause
                clause neg_cl = _clauses[neg_clauses[i]];
                for (int j = 0; j < neg_cl.literals.size(); j++) {
                    int l_idx = neg_cl.literals[j];
                    lit* l = &(_lits[std::abs(l_idx)]);
                    if (!l->is_lia_lit && l->delta == bool_var_idx) {
                        neg_cl.literals[j] = neg_cl.literals[0];
                        neg_cl.literals[0] = l_idx;
                        break;
                    }
                }
                _reconstruct_stack.push(neg_cl);
            }
        }
    }
}

void ls_sampler::reduce_clause() {
    _bool_var_vec.clear();
    _lia_var_vec.clear();
    _vars.reserve(_resolution_vars.size());
    int i, reduced_clause_num;
    i = 0;
    reduced_clause_num = 0;
    for (; i < _num_clauses; i++) {  // Remove already deleted clauses in _clause
        if (!_clauses[i].is_delete) {
            _clauses[reduced_clause_num++] = _clauses[i];
        }
    }
    _clauses.resize(reduced_clause_num);

    _num_lia_lits = 0;
    _num_bool_lits = 0;
    for (int l_idx = 0; l_idx < _lits.size(); l_idx++) {
        lit* l = &(_lits[l_idx]);
        if (l->lits_index == 0) {
            continue;
        }  // true literal
        if (l->is_lia_lit) {
            _num_lia_lits++;
        } else {  // Keep only the literals that have not been resoluted
            if (!_resolution_vars[l->delta].is_delete) {
                _num_bool_lits++;
            } else {
                l->lits_index = 0;  // resoluted literal --> true
            }
        }
    }  // transfer the _resolution_vars to _vars
    _num_clauses = reduced_clause_num;
    _lit_appear.resize(_num_lits + _additional_len, false);  // 去重
    for (int clause_idx = 0; clause_idx < reduced_clause_num; clause_idx++) {
        _clauses[clause_idx].weight = 1;
        for (int k = 0; k < _clauses[clause_idx].literals.size(); k++) {  // constructor variable set
            int l_sign_idx = _clauses[clause_idx].literals[k];
            lit* l = &(_lits[std::abs(l_sign_idx)]);
            if (l->is_lia_lit) {
                variable* v;
                for (int j = 0; j < l->neg_coff.size(); j++) {
                    if (!_lit_appear[l->lits_index]) {  // 标记哪些文字出现于约简后的子句中
                        l->neg_coff_var_idx[j] = (int)transfer_name_to_reduced_var(_resolution_vars[l->neg_coff_var_idx[j]].var_name, true, false);
                    }
                    v = &(_vars[l->neg_coff_var_idx[j]]);
                    v->literals.push_back(l_sign_idx);
                    v->literal_clause.push_back(clause_idx);
                    v->literal_coff.push_back(-l->neg_coff[j]);
                }
                for (int j = 0; j < l->pos_coff.size(); j++) {
                    if (!_lit_appear[l->lits_index]) {
                        l->pos_coff_var_idx[j] = (int)transfer_name_to_reduced_var(_resolution_vars[l->pos_coff_var_idx[j]].var_name, true, false);
                    }
                    v = &(_vars[l->pos_coff_var_idx[j]]);
                    v->literals.push_back(l_sign_idx);
                    v->literal_clause.push_back(clause_idx);
                    v->literal_coff.push_back(l->pos_coff[j]);
                }
                _clauses[clause_idx].lia_literals.push_back(l_sign_idx);
            } else {
                if (l->lits_index == 0)
                    continue;
                if (!_lit_appear[l->lits_index]) {
                    l->delta = transfer_name_to_reduced_var(_resolution_vars[l->delta].var_name, false, false);
                }
                _vars[l->delta].literals.push_back(l_sign_idx);
                _vars[l->delta].literal_clause.push_back(clause_idx);
                _clauses[clause_idx].bool_literals.push_back(l_sign_idx);
            }
            if (!_lit_appear[l->lits_index]) {
                _lit_appear[l->lits_index] = true;
            }
        }
    }  // determine the literals of _vars
    _vars.resize(_vars.size());
    _num_vars = _vars.size();
    _num_lia_vars = 0;
    for (variable& v : _vars) {
        int pre_clause_idx = INT32_MAX;
        for (int i = 0; i < v.literal_clause.size(); i++) {  // 去重
            int tmp_clause_idx = v.literal_clause[i];
            if (pre_clause_idx != tmp_clause_idx) {
                v.clause_idxs.push_back(tmp_clause_idx);
                pre_clause_idx = tmp_clause_idx;
            }
        }
        if (v.is_lia) {
            v.upper_bound = _resolution_vars[transfer_name_to_resolution_var(v.var_name, true, false)].upper_bound;
            v.low_bound = _resolution_vars[transfer_name_to_resolution_var(v.var_name, true, false)].low_bound;
            _num_lia_vars++;
        }
    }  // determine the clause_idxs of var
    __int128_t max_lit_num = 0;
    for (int var_idx = 0; var_idx < _num_vars; var_idx++) {
        if (!_vars[var_idx].is_lia) {
            continue;
        }
        if (_vars[var_idx].literals.size() > max_lit_num) {
            _lia_var_idx_with_most_lits = var_idx;
            max_lit_num = _vars[var_idx].literals.size();
        }
    }
    for (int lit_idx = 0; lit_idx < _lits.size(); lit_idx++) {
        lit* l = &(_lits[lit_idx]);
        if (l->lits_index == 0 || !l->is_lia_lit) {
            continue;
        }
        if (l->pos_coff.size() != 1 || l->neg_coff.size() != 1 || l->pos_coff[0] != 1 || l->neg_coff[0] != 1) {
            _lia_var_idx_with_most_lits = -1;
            is_idl = false;
            break;
        }  // var_with_most_lit are dedicated for IDL
    }
}

uint64_t ls_sampler::transfer_name_to_reduced_var(std::string& name, bool is_lia, bool in_equal) {
    if (_name2var.find(name) == _name2var.end()) {
        _name2var[name] = _vars.size();
        variable var;
        var.var_name = name;
        var.is_lia = is_lia;
        if (var.is_in_equal == false) {
            var.is_in_equal = in_equal;
        }
        _vars.push_back(var);
        if (is_lia) {
            _lia_var_vec.push_back((int)_vars.size() - 1);
        } else {
            _bool_var_vec.push_back((int)_vars.size() - 1);
        }
        return _vars.size() - 1;
    } else
        return _name2var[name];
}

void ls_sampler::set_pre_value() {
    _pre_value_1.resize(_num_vars + _additional_len, INT32_MAX);
    _pre_value_2.resize(_num_vars + _additional_len, INT32_MAX);
    for (clause& cl : _clauses) {
        if (cl.literals.size() == 1 && cl.literals[0] > 0 && _lits[cl.literals[0]].is_equal) {  // 单元等式子句
            lit* l = &(_lits[cl.literals[0]]);
            if (l->pos_coff.size() + l->neg_coff.size() == 1) {
                if (l->pos_coff.size() == 1) {
                    _pre_value_1[l->pos_coff_var_idx[0]] = (int)(-l->key / l->pos_coff[0]);
                } else if (l->neg_coff.size() == 1) {
                    _pre_value_1[l->neg_coff_var_idx[0]] = (int)(l->key / l->neg_coff[0]);
                }
            }
        }  //(a==0)
        else if (cl.literals.size() == 2 && cl.literals[0] > 0 && _lits[cl.literals[0]].is_equal && cl.literals[1] > 0 && _lits[cl.literals[1]].is_equal) {  // 二元等式子句
            lit* l1 = &(_lits[cl.literals[0]]);
            lit* l2 = &(_lits[cl.literals[1]]);
            if ((l1->pos_coff.size() + l1->neg_coff.size() == 1) && (l2->pos_coff.size() + l2->neg_coff.size() == 1)) {
                int var_idx_1 = (l1->pos_coff.size() == 1) ? (l1->pos_coff_var_idx[0]) : (l1->neg_coff_var_idx[0]);
                int var_idx_2 = (l2->pos_coff.size() == 1) ? (l2->pos_coff_var_idx[0]) : (l2->neg_coff_var_idx[0]);
                if (var_idx_1 == var_idx_2) {
                    _pre_value_1[var_idx_1] = (l1->pos_coff.size() == 1) ? ((int)(-l1->key / l1->pos_coff[0])) : ((int)(l1->key / l1->neg_coff[0]));
                    _pre_value_2[var_idx_1] = (l2->pos_coff.size() == 1) ? ((int)(-l2->key / l2->pos_coff[0])) : ((int)(l2->key / l2->neg_coff[0]));
                }
            }
        }  //(a==0 OR a==1)
    }
}

// Constructing constraint instances
void ls_sampler::build_instance(std::vector<std::vector<int>>& clause_vec, const std::unordered_map<std::string, std::string>& model) {
    last_cdcl_model = model;

    // iterate over all clauses
    for (int clause_idx = 0; clause_idx < clause_vec.size(); clause_idx++) {  // 可以做边界传播
        if (clause_vec[clause_idx].size() == 1) {                             // unit clause, bound lit (a + key <= 0)
            lit* l = &(_lits[std::abs(clause_vec[clause_idx][0])]);

            if (l->is_equal || !l->is_lia_lit) {
                continue;
            }  // equal lit is not bound lit

            if (l->pos_coff.size() == 0 && l->neg_coff.size() == 1) {                       // unit var with negative coeff (-a + key <= 0)
                if (clause_vec[clause_idx][0] > 0 &&                                        // positive literal (a >= key)
                    l->key > _tmp_vars[l->neg_coff_var_idx[0]].low_bound) {                 // key > old_lower_bound
                    _tmp_vars[l->neg_coff_var_idx[0]].low_bound = l->key;                   // tightening the lower bound
                } else if (clause_vec[clause_idx][0] < 0 &&                                 // negative literal (a < key) --> (a <= key - 1)
                           (l->key - 1) < _tmp_vars[l->neg_coff_var_idx[0]].upper_bound) {  // key - 1 < old_upper_bound
                    _tmp_vars[l->neg_coff_var_idx[0]].upper_bound = (l->key - 1);           // tightening the upper bound
                }

                _bound_lits.push_back(l->lits_index);

                l->lits_index = 0;
                if (clause_vec[clause_idx][0] < 0) {                         // negative literal
                    clause_vec[clause_idx][0] = -clause_vec[clause_idx][0];  // ??
                }
            } else if (l->pos_coff.size() == 1 && l->neg_coff.size() == 0) {              // unit var with positive coeff (a + key <= 0)
                if (clause_vec[clause_idx][0] > 0 &&                                      // positive literal (a <= -key)
                    (-l->key) < _tmp_vars[l->pos_coff_var_idx[0]].upper_bound) {          // -key < old_upper_bound
                    _tmp_vars[l->pos_coff_var_idx[0]].upper_bound = -l->key;              // tightening the upper bound
                } else if (clause_vec[clause_idx][0] < 0 &&                               // negative literal (a >= -key + 1)
                           (1 - l->key) > _tmp_vars[l->pos_coff_var_idx[0]].low_bound) {  // -key + 1 > old_lower_bound
                    _tmp_vars[l->pos_coff_var_idx[0]].low_bound = (1 - l->key);           // tightening the lower bound
                }

                _bound_lits.push_back(l->lits_index);

                l->lits_index = 0;
                if (clause_vec[clause_idx][0] < 0) {                         // negative literal
                    clause_vec[clause_idx][0] = -clause_vec[clause_idx][0];  // ??
                }
            }
        }
    }

    reduce_vars();  // handling of differential terms

    // Converting Clause Sets 'clause_vec' to Internal Data Structures '_clauses'
    _clauses.resize(clause_vec.size());
    _num_clauses = 0;
    for (auto clause_curr : clause_vec) {
        bool is_tautology = false;
        for (auto l_idx : clause_curr) {
            if (_lits[std::abs(l_idx)].lits_index == 0) {
                is_tautology = true;
                break;
            }
        }
        if (is_tautology) {
            continue;
        }
        for (auto l_idx : clause_curr) {
            _clauses[_num_clauses].literals.push_back(l_idx);
            lit* l = &(_lits[std::abs(l_idx)]);
            if (l->lits_index == 0) {  // true literal
                continue;
            }
            if (!l->is_lia_lit) {  // Marks which clause the boolean variable belongs to
                _resolution_vars[l->delta].clause_idxs.push_back(_num_clauses);
            }
        }
        _num_clauses++;
    }
    _clauses.resize(_num_clauses);
    // now the vars are all in the resolution vars

    unit_prop();   // 一些布尔变量和子句被删除
    resolution();  // 一些子句被删除
    unit_prop();
    reduce_clause();  // 约简子句 get _vars

    // SAMPLER_TRACE(
    //     tout << "print formula:\n";
    //     print_formula(tout););

    SASSERT(_num_vars == _vars.size());
    for (int i = 0; i < _num_vars; ++i) {
        variable* v = &_vars[i];
        if (!v->is_lia) continue;
        for (auto l_sign : v->literals) {
            int l_idx = std::abs(l_sign);
            lit* l = &_lits[l_idx];
            if (l->is_equal) {
                v->is_in_equal = true;
                break;
            }
        }
    }

    for (size_t i = 0; i < _lits.size(); ++i) {
        lit* l = &_lits[i];
        if (l->lits_index == 0 || !l->is_lia_lit) {
            continue;
        }
        if (l->is_equal)
            _eq_form_cnt++;
    }

    _best_found_cost = (int)_num_clauses;
    make_space();
    set_pre_value();

#ifdef EQ2INEQ_BUILD_TABLE
    build_equal_table();  // count num of form "x <= 0 && x >= 0"
#endif

    int average_lits_num = 0;  // On average, each variable exists in how many literals
#ifdef DEBUG
    std::vector<std::pair<std::string, int>> vec;
#endif

    for (int var_idx = 0; var_idx < _num_vars; var_idx++) {
        _vars[var_idx].occs = _vars[var_idx].literals.size();
        average_lits_num += _vars[var_idx].literals.size();
#ifdef DEBUG
        vec.push_back({_vars[var_idx].var_name, _vars[var_idx].literals.size()});
#endif
    }
    average_lits_num /= _num_vars + 1;
    use_swap_from_from_small_weight = (average_lits_num < 10);
    // std::cout << "average_lits_num: " << average_lits_num << "\n";

#if defined(DEBUG) && defined(PRINT_OCCS)
    std::sort(vec.begin(), vec.end(),
              [](const std::pair<std::string, int>& a, const std::pair<std::string, int>& b) {
                  return a.second > b.second;  // 升序，如果需要降序则改为 a.second > b.second
              });

    // 输出排序后的结果
    for (const auto& pair : vec) {
        std::cout << pair.first << " occs: " << pair.second << std::endl;
    }
#endif

#ifdef BUILD_OCCS_CLOSURES
    build_occs_closures();
#endif

    calc_var_intervals();

#ifdef VERBOSE
    std::cout << "num euqal_cnt(==): " << _eq_form_cnt << "\n";
    std::cout << "num equal_cnt(<=&>=): " << _ineq_form_cnt << "\n";
    std::cout << "num occs_closure_vars: " << _num_occs_closure_vars << "\n";
    std::cout << "num equal_closure_vars: " << _num_equal_closure_vars << "\n";
    std::cout << "num ordinary vars: " << _num_ordinary_vars << "\n";
#endif
}

void ls_sampler::reduce_vars() {
    const uint64_t tmp_vars_size = _tmp_vars.size();
    std::vector<int> hash_map(tmp_vars_size * tmp_vars_size, 0);  // hash_map[A*(size)+b]=n means A-B has occurred n times
    std::vector<int> occur_time(tmp_vars_size, 0);                // occur_time[a]=n means that a has occured in lits for n times
    pair_x = new Array((int)tmp_vars_size);
    pair_y = new Array((int)tmp_vars_size);
    lit* l;
    variable* original_var;
    variable* new_var;
    std::string var_name;
    int pos_var_idx, neg_var_idx, original_var_idx;

    TRACE("bound", for (int var_idx = 0; var_idx < tmp_vars_size; var_idx++) {
        if (_tmp_vars[var_idx].upper_bound > 1 || _tmp_vars[var_idx].low_bound < 0) {
            tout << "not pb\n";
            break;
        } });

    // is it possible to use pseudo-Boolean constraints to solve
    use_pbs = !(_resolution_vars.size() == 0);

    // whether the value of the variable in _tmp_vars is only 0, 1
    for (int var_idx = 0; var_idx < tmp_vars_size; var_idx++) {
        if (_tmp_vars[var_idx].upper_bound > 1 || _tmp_vars[var_idx].low_bound < 0) {
            use_pbs = false;
            is_pb = false;
            break;
        }
    }

    if (use_pbs) {
        _resolution_vars = _tmp_vars;
    }  // if there is no boolean vars and all lia vars are in [0,1], then use pbs, and no need to reduce the vars
    else {
        // calculate the hash_map
        for (uint64_t l_idx = 0; l_idx < _num_lits; l_idx++) {
            l = &(_lits[l_idx]);

            if (l->lits_index == 0) {  // true literal
                continue;
            }

            for (int i = 0; i < l->pos_coff.size(); i++) {
                pos_var_idx = l->pos_coff_var_idx[i];
                for (int j = 0; j < l->neg_coff.size(); j++) {
                    if (l->pos_coff[i] != l->neg_coff[j]) {
                        continue;
                    }
                    neg_var_idx = l->neg_coff_var_idx[j];
                    if (neg_var_idx < pos_var_idx) {
                        hash_map[neg_var_idx * tmp_vars_size + pos_var_idx]++;
                    }  // small_idx* num_var+ large_idx
                    else {
                        hash_map[pos_var_idx * tmp_vars_size + neg_var_idx]++;
                    }
                }
            }
        }

        // calculate the occur time
        for (uint64_t l_idx = 0; l_idx < _num_lits; l_idx++) {
            l = &(_lits[l_idx]);
            if (l->lits_index == 0 || !l->is_lia_lit) {
                continue;
            }

            for (int i = 0; i < l->pos_coff.size(); i++) {
                occur_time[l->pos_coff_var_idx[i]]++;
            }
            for (int i = 0; i < l->neg_coff.size(); i++) {
                occur_time[l->neg_coff_var_idx[i]]++;
            }
        }

        // calculate the x-y pair
        for (int pre_idx = 0; pre_idx < tmp_vars_size - 1; pre_idx++) {
            if (pair_y->is_in_array(pre_idx) || occur_time[pre_idx] == 0) {
                continue;
            }  // prevent reinsert
            for (int pos_idx = pre_idx + 1; pos_idx < tmp_vars_size; pos_idx++) {
                if (pair_y->is_in_array(pos_idx)) {
                    continue;
                }  // prevent reinsert
                if (hash_map[pre_idx * tmp_vars_size + pos_idx] == occur_time[pre_idx] &&  // A-B occurs the same number of times that A occurs
                    occur_time[pre_idx] == occur_time[pos_idx]) {                          // A occurs the same number of times as B
                    pair_x->insert_element(pre_idx);
                    pair_y->insert_element(pos_idx);
                    break;
                }
            }
        }

        SAMPLER_TRACE(
            tout << pair_x->array_size << "\n";
            for (int i = 0; i < pair_x->array_size; ++i) {
                tout << "pair_x " << i << ": " << pair_x->element_at(i) << "\n";
                tout << "pair_y " << i << ": " << pair_y->element_at(i) << "\n";
            });

        _name2var.clear();

        // rewrite lits
        for (uint64_t l_idx = 0; l_idx < _num_lits; l_idx++) {
            l = &(_lits[l_idx]);
            lit new_lit;
            if (l->lits_index == 0 || !l->is_lia_lit) {
                continue;
            }
            new_lit.key = l->key;
            new_lit.lits_index = l->lits_index;
            new_lit.is_equal = l->is_equal;
            new_lit.is_lia_lit = l->is_lia_lit;

            for (int i = 0; i < l->pos_coff.size(); i++) {  // iterate over all positive coeff variables
                original_var_idx = l->pos_coff_var_idx[i];
                original_var = &(_tmp_vars[original_var_idx]);
                if (pair_x->is_in_array(original_var_idx)) {
                    new_lit.pos_coff.push_back(l->pos_coff[i]);
                    //                var_name="_new_var_"+std::to_string(pair_x->index_of(original_var_idx));
                    var_name = "_new_var_" + original_var->var_name;
                    new_lit.pos_coff_var_idx.push_back((int)transfer_name_to_resolution_var(var_name, true, false));
                } else if (pair_y->is_in_array(original_var_idx)) {
                    new_lit.neg_coff.push_back(l->pos_coff[i]);
                    //                var_name="_new_var_"+std::to_string(pair_y->index_of(original_var_idx));
                    var_name = "_new_var_" + _tmp_vars[pair_x->element_at(pair_y->index_of(original_var_idx))].var_name;
                    new_lit.neg_coff_var_idx.push_back((int)transfer_name_to_resolution_var(var_name, true, false));
                } else {
                    new_lit.pos_coff.push_back(l->pos_coff[i]);
                    new_lit.pos_coff_var_idx.push_back((int)transfer_name_to_resolution_var(original_var->var_name, true, false));
                }
            }

            for (int i = 0; i < l->neg_coff.size(); i++) {  // iterate over all negative coeff variables
                original_var_idx = l->neg_coff_var_idx[i];
                original_var = &(_tmp_vars[original_var_idx]);
                if (!pair_x->is_in_array(original_var_idx) && !pair_y->is_in_array(original_var_idx)) {
                    new_lit.neg_coff.push_back(l->neg_coff[i]);
                    new_lit.neg_coff_var_idx.push_back((int)transfer_name_to_resolution_var(original_var->var_name, true, false));
                }
            }
            _lits[l_idx] = new_lit;
        }

        // set low and up bound
        for (original_var_idx = 0; original_var_idx < _tmp_vars.size(); original_var_idx++) {
            original_var = &(_tmp_vars[original_var_idx]);
            if (occur_time[original_var_idx] == 0) {
                continue;
            }
            // original var
            if (!pair_x->is_in_array(original_var_idx) && !pair_y->is_in_array(original_var_idx)) {
                new_var = &(_resolution_vars[transfer_name_to_resolution_var(original_var->var_name, true, false)]);
                new_var->low_bound = original_var->low_bound;
                new_var->upper_bound = original_var->upper_bound;
            }
            // new var
            else if (pair_x->is_in_array(original_var_idx)) {
                int pair_idx = pair_x->index_of(original_var_idx);
                //            var_name="_new_var_"+std::to_string(pair_idx);
                var_name = "_new_var_" + original_var->var_name;
                new_var = &(_resolution_vars[transfer_name_to_resolution_var(var_name, true, false)]);
                __int128_t x_low = original_var->low_bound;
                __int128_t x_upper = original_var->upper_bound;
                __int128_t y_low = _tmp_vars[pair_y->element_at(pair_idx)].low_bound;
                __int128_t y_upper = _tmp_vars[pair_y->element_at(pair_idx)].upper_bound;
                if (x_low == -max_int || y_upper == max_int) {
                    new_var->low_bound = -max_int;
                } else {
                    new_var->low_bound = x_low - y_upper;
                }
                if (x_upper == max_int || y_low == -max_int) {
                    new_var->upper_bound = max_int;
                } else {
                    new_var->upper_bound = x_upper - y_low;
                }
            }
        }
    }

    int num_var_with_bound = 0;
    for (int var_idx = 0; var_idx < _resolution_vars.size(); var_idx++) {
        new_var = &(_resolution_vars[var_idx]);
        if (!new_var->is_lia) {
            continue;
        }
        if (new_var->upper_bound != max_int && new_var->low_bound != -max_int) {
            continue;
        }  // if a var has both upper bound and lower bound, no bound lits is added.
        if (new_var->low_bound != -max_int) {
            int lit_idx = _bound_lits[num_var_with_bound++];
            lit bound_lit;
            bound_lit.is_lia_lit = true;
            bound_lit.lits_index = lit_idx;
            bound_lit.neg_coff.push_back(1);
            bound_lit.neg_coff_var_idx.push_back(var_idx);
            bound_lit.key = new_var->low_bound;
            _lits[lit_idx] = bound_lit;
            new_var->low_bound = -max_int;
        }
        if (new_var->upper_bound != max_int) {
            int lit_idx = _bound_lits[num_var_with_bound++];
            lit bound_lit;
            bound_lit.is_lia_lit = true;
            bound_lit.lits_index = lit_idx;
            bound_lit.pos_coff.push_back(1);
            bound_lit.pos_coff_var_idx.push_back(var_idx);
            bound_lit.key = -new_var->upper_bound;
            _lits[lit_idx] = bound_lit;
            new_var->upper_bound = max_int;
        }
    }
}

void ls_sampler::ls_sampling() {
    _total_start = std::chrono::steady_clock::now();

    SAMPLER_TRACE(
        print_interal_data_strcture(tout););

    SASSERT(_num_vars == _vars.size());
    for (variable v : _tmp_vars) {
        if (v.low_bound > v.upper_bound) {
            return;
        }
    }

#ifdef DEBUG
    std::cout << "start sampling ...\n";
#endif

    _num_vars = _vars.size();

    SAMPLER_TRACE(
        print_interal_data_strcture(tout););

    search();

#ifdef DEBUG
    check_solution();
#endif
}

bool ls_sampler::search() {
    initialize();

#ifdef DEBUG
    for (variable v : _tmp_vars) {  // check the bound condition of vars
        if (v.low_bound > v.upper_bound) {
            std::cout << "bound error!\n";
            return false;
        }
    }
#endif

    int no_improve_cnt = 0;
    int flip_v;
    __int128_t change_value = 0;
    _outer_layer_step = 1;
    for (_step = 1; _step < _max_step; ++_step) {
#ifndef BAM_V2
        if (_overflow_cnt > 10 && _use_interval_move) {
#ifdef VERBOSE
            std::cout << "restart(overflow)...\n";
#endif
            initialize();
            no_improve_cnt = 0;
            _use_interval_move = false;
            is_overflow = false;
        }
#endif

        if (is_overflow) {
            is_overflow = false;
#if defined(VERBOSE) && defined(DEBUG)
            std::cout << "overflow ...\n";
#endif
            _overflow_cnt++;
            update_sampling_interval = false;
            initialize();
            no_improve_cnt = 0;
        }

        if (0 == _unsat_clauses->size()) {
            SASSERT(!is_overflow);
#ifdef VERBOSE
            std::cout << "_overflow_cnt = " << _overflow_cnt << "\n";
#endif
            choose_value_for_pair();  // 为前面化简的 IDL 变量赋值
            up_bool_vars();
            SASSERT(!is_overflow);
            return true;
        }

        if (_step % 1000 == 0 && (TimeElapsed_total() > _cutoff)) {
#ifdef VERBOSE
            std::cout << "_overflow_cnt = " << _overflow_cnt << "\n";
#endif
            std::cout << "this round time out !\n";
            break;
        }

        if (no_improve_cnt > 500000) {  // 重启
#ifdef VERBOSE
            std::cout << "restart(step out)...\n";
#endif
            initialize();
            no_improve_cnt = 0;
        }
        if (!use_swap_from_from_small_weight || mt() % 100 < 99 || _sat_clause_with_false_literal->size() == 0) {
            bool time_up_bool = (_no_improve_cnt_bool * _lit_in_unsat_clause_num >
                                 5 * _bool_lit_in_unsat_clause_num)  // non_improve_steps > L * Pb
                                || (_unsat_clauses->size() <= 20);
            bool time_up_lia = (_no_improve_cnt_lia * _lit_in_unsat_clause_num >  // non_improve_steps > L * Pi
                                20 * (_lit_in_unsat_clause_num - _bool_lit_in_unsat_clause_num));
            // 切换模式
            if ((is_in_bool_search && _bool_lit_in_unsat_clause_num < _lit_in_unsat_clause_num && time_up_bool) || _bool_lit_in_unsat_clause_num == 0) {
                enter_lia_mode();
            } else if ((!is_in_bool_search && _bool_lit_in_unsat_clause_num > 0 && time_up_lia) || (_lit_in_unsat_clause_num == _bool_lit_in_unsat_clause_num)) {
                // SASSERT(false);
                enter_bool_mode();
            }

            if (is_in_bool_search) {
                flip_v = pick_critical_move_bool();  // 选择翻转变量
                if (flip_v != -1) {
                    critical_move(flip_v, change_value);
                }

                if (update_outer_best_solution())  // 重置未提升步长
                    _no_improve_cnt_bool = 0;
                else
                    _no_improve_cnt_bool++;
            } else {
                flip_v = pick_critical_move(change_value);
                if (flip_v != -1) {
                    critical_move(flip_v, change_value);
                }

                if (update_inner_best_solution())
                    _no_improve_cnt_lia = 0;
                else
                    _no_improve_cnt_lia++;
            }
        } else {
            swap_from_small_weight_clause();
        }
        no_improve_cnt = (update_best_solution()) ? 0 : (no_improve_cnt + 1);
    }
    return false;
}

void ls_sampler::update_literals_sat_steps_count() {
    clause* cp;
    __int128_t delta;
    for (size_t i = 0; i < _num_clauses; ++i) {
        cp = &(_clauses[i]);
        for (int lit_idx : cp->literals) {
            lit* l = &_lits[std::abs(lit_idx)];
            if (!l->is_lia_lit)
                continue;
            delta = delta_lit(*l);
            bool is_equal = l->is_equal;

            if ((!is_equal && ((delta <= 0 && lit_idx > 0) || (delta > 0 && lit_idx < 0))) || (is_equal && ((delta == 0 && lit_idx > 0) || (delta != 0 && lit_idx < 0)))) {
                l->sat_steps_count++;
            }
        }
    }
}

void ls_sampler::up_bool_vars() {
    for (variable& var : _resolution_vars) {                                             // 某些被删除子句中的变量
        if (var.is_lia && _name2var.find(var.var_name) == _name2var.end()) {             // if it is an lia var and it is not in the formula
            int var_idx = (int)transfer_name_to_reduced_var(var.var_name, true, false);  // insert it into the vars

            // if (var.low_bound > 0) {
            //     _solution[var_idx] = var.low_bound;
            // } else if (var.upper_bound < 0) {
            //     _solution[var_idx] = var.upper_bound;
            // } else {
            //     _solution[var_idx] = 0;
            // }

            __int128_t random_val = random_int64_in_range(var.s_lower_bound, var.s_upper_bound);
            SASSERT(random_val >= var.low_bound && random_val <= var.upper_bound);
            _solution[var_idx] = random_val;
        }
    }  // set the var solution
    for (int lit_idx = 0; lit_idx < _lits.size(); lit_idx++) {
        lit* l = &(_lits[lit_idx]);
        if (!_lit_appear[lit_idx] && _lits[lit_idx].is_lia_lit && l->lits_index != 0) {  // 不在约简后子句中的文字
            _lit_appear[lit_idx] = true;
            for (int var_idx = 0; var_idx < l->pos_coff_var_idx.size(); var_idx++) {
                int resolution_var_idx = l->pos_coff_var_idx[var_idx];
                l->pos_coff_var_idx[var_idx] = (int)transfer_name_to_reduced_var(_resolution_vars[resolution_var_idx].var_name, true, false);
            }
            for (int var_idx = 0; var_idx < l->neg_coff_var_idx.size(); var_idx++) {
                int resolution_var_idx = l->neg_coff_var_idx[var_idx];
                l->neg_coff_var_idx[var_idx] = (int)transfer_name_to_reduced_var(_resolution_vars[resolution_var_idx].var_name, true, false);
            }
            l->delta = delta_lit(*l);
        }
    }  // now all lia lit has delta
    std::bernoulli_distribution dist(0.5);
    for (int i = 0; i < _resolution_vars.size(); i++) {  // 为被归结掉的布尔变量赋值
        if (!_resolution_vars[i].is_lia && _resolution_vars[i].up_bool == 0) {
            if (dist(mt)) {
                _resolution_vars[i].up_bool = 1;
            } else {
                _resolution_vars[i].up_bool = -1;
            }
        }
    }  // set all origin bool var as false
    while (!_reconstruct_stack.empty()) {  // 判断被归结掉的子句是否为true
        clause cl = _reconstruct_stack.top();
        _reconstruct_stack.pop();
        bool sat_flag = false;
        for (int l_idx : cl.literals) {
            lit* l = &(_lits[std::abs(l_idx)]);
            if (l->is_lia_lit) {
                if (!l->is_equal) {
                    if ((l->delta <= 0 && l_idx > 0) || (l->delta > 0 && l_idx < 0)) {
                        sat_flag = true;
                        break;  // 一个文字为真，该子句为真
                    }
                } else {
                    if ((l->delta == 0 && l_idx > 0) || (l->delta != 0 && l_idx < 0)) {
                        sat_flag = true;
                        break;
                    }
                }
            } else {
                if (!_lit_appear[std::abs(l_idx)]) {
                    if ((l_idx > 0 && _resolution_vars[l->delta].up_bool > 0) || (l_idx < 0 && _resolution_vars[l->delta].up_bool < 0)) {
                        sat_flag = true;
                        break;
                    }
                }  // if the boolean lit does not exist
                else if ((_solution[l->delta] > 0 && l_idx > 0) || (_solution[l->delta] < 0 && l_idx < 0)) {
                    sat_flag = true;
                    break;
                }
            }
        }
        if (sat_flag == false) {  // 被归结掉的子句此时为假
            lit* l = &(_lits[std::abs(cl.literals[0])]);
            _resolution_vars[l->delta].up_bool *= -1;
        }  // if the clause is false, flip the var
    }

    _num_vars = _vars.size();
}

void ls_sampler::choose_value_for_pair() {  // x - y = val
    pair_x_value.reserve(pair_x->size());
    pair_y_value.reserve(pair_x->size());
    variable* original_var_x;
    variable* original_var_y;
    __int128_t z_value, upper, lower, upper_y, lower_y, new_x_value;
    __int64_t s_upper_y, s_lower_y, s_lower, s_upper;
    // std::cout << "pair_x->size(): " << pair_x->size() << std::endl;
    for (int pair_idx = 0; pair_idx < pair_x->size(); pair_idx++) {
        original_var_x = &(_tmp_vars[pair_x->element_at(pair_idx)]);
        original_var_y = &(_tmp_vars[pair_y->element_at(pair_idx)]);

        z_value = _solution[_name2var["_new_var_" + original_var_x->var_name]];

        upper_y = (original_var_y->upper_bound == max_int) ? max_int : (original_var_y->upper_bound + z_value);
        lower_y = (original_var_y->low_bound == -max_int) ? (-max_int) : (original_var_y->low_bound + z_value);
        upper = (original_var_x->upper_bound < upper_y) ? original_var_x->upper_bound : upper_y;
        lower = (original_var_x->low_bound > lower_y) ? original_var_x->low_bound : lower_y;

        SASSERT(upper >= lower);

        // 随机赋值
        __int128_t random_val = lower;

        // if ((lower > neg_inf_64 && upper < pos_inf_64)) {
        //     random_val = random_int64_in_range(lower, upper);
        // } else if (lower > neg_inf_64) {
        //     random_val = random_int64_in_range(lower, pos_inf_64);
        // } else if (upper < pos_inf_64) {
        //     random_val = random_int64_in_range(neg_inf_64, upper);
        // } else {
        //     random_val = random_int64_in_range(neg_inf_64, pos_inf_64);
        // }

        SASSERT(random_val >= lower && random_val <= upper);
        new_x_value = random_val;

        pair_x_value.push_back(new_x_value);
        pair_y_value.push_back(new_x_value - z_value);  // x-y=z  x=y+z  x [0,inf) y+z [-1,inf)-->x \wedge y+z [0,inf) -->x=0--> y=x-z
    }
}

bool ls_sampler::update_inner_best_solution() {
    if (_unsat_clauses->size() < _best_found_hard_cost_this_lia) {
        _best_found_hard_cost_this_lia = _unsat_clauses->size();
        return true;
    }
    return false;
}

bool ls_sampler::update_outer_best_solution() {
    if (_unsat_clauses->size() < _best_found_hard_cost_this_bool) {
        _best_found_hard_cost_this_bool = _unsat_clauses->size();
        return true;
    }
    return false;
}

void ls_sampler::enter_lia_mode() {
    _best_found_hard_cost_this_lia = _unsat_clauses->size();
    _no_improve_cnt_lia = 0;
    is_in_bool_search = false;
}

void ls_sampler::enter_bool_mode() {
    _best_found_hard_cost_this_bool = _unsat_clauses->size();
    _no_improve_cnt_bool = 0;
    is_in_bool_search = true;
}

// sat or unsat a clause, update the delta, dedicated for lia var
void ls_sampler::critical_score_subscore(uint64_t var_idx, __int128_t change_value) {
    static std::vector<int> lit_exist(_num_lits + _additional_len, 0);
    variable* var = &(_vars[var_idx]);
    lit* l;
    clause* cp;
    __int128_t l_clause_idx, delta_old, delta_new, curr_clause_idx;
    __int128_t pos_delta;
    __int128_t new_future_min_delta = max_int;  // Distance to True of clauses: dts

    int min_delta_lit_idx = -1;
    bool contained_in_min_delta_lit = false;  // this var is present in the literal with the smallest delta in the clause
    int lit_idx;
    _lit_occur->clear();
    int make_break_in_clause = 0;                     // make how many literals become sat
    for (int i = 0; i < var->literals.size(); i++) {  // literals contained the var
        lit_idx = var->literals[i];
        l = &(_lits[std::abs(lit_idx)]);
        l_clause_idx = var->literal_clause[i];
        delta_old = l->delta;
        __int128_t tmp;
        is_overflow = __builtin_mul_overflow(var->literal_coff[i], change_value, &tmp) || is_overflow;
        // SASSERT(!is_overflow);
        is_overflow = __builtin_add_overflow(l->delta, tmp, &delta_new) || is_overflow;
        // SASSERT(!is_overflow);
        if (is_overflow && !update_sampling_interval) {
            shrinkSampleInterval(l);
        }
        pos_delta = delta_new;
        // pos_delta = delta_new = (l->delta + var->literal_coff[i] * change_value);
        convert_to_pos_delta(pos_delta, lit_idx);
        if (pos_delta < new_future_min_delta) {
            new_future_min_delta = pos_delta;
            min_delta_lit_idx = lit_idx;
        }
        _lit_occur->insert_element(std::abs(lit_idx));
        if (lit_idx == _clauses[l_clause_idx].min_delta_lit_index) {
            contained_in_min_delta_lit = true;
        }
        bool is_equal = l->is_equal;
        // SASSERT(is_equal == false);
        // positive literal: the goal is to make the delta smaller (delta <= 0)
        // negative literal: the goal is to make the delta larger  (delta > 0)
        if ((!is_equal && delta_old <= 0 && delta_new > 0) || (is_equal && delta_old == 0 && delta_new != 0)) {       // make_break_in_clause + 1 means sat a literal
            make_break_in_clause = (var->literals[i] > 0) ? (make_break_in_clause - 1) : (make_break_in_clause + 1);  // make_break_in_clause - 1 means unsat a literal
        } else if ((!is_equal && delta_old > 0 && delta_new <= 0) || (is_equal && delta_old != 0 && delta_new == 0)) {
            make_break_in_clause = (var->literals[i] > 0) ? (make_break_in_clause + 1) : (make_break_in_clause - 1);
        }
        // enter a new clause or the last literal
        // (l1 --> c1, l2 --> c1, l2 --> c2 ...)
        if ((i != (var->literals.size() - 1) && l_clause_idx != var->literal_clause[i + 1]) || i == (var->literals.size() - 1)) {
            curr_clause_idx = abs_128(l_clause_idx);  // ??
            cp = &(_clauses[curr_clause_idx]);
            if (cp->sat_count > 0 && cp->sat_count + make_break_in_clause == 0) {  // the true literals in the clause are set to false
                unsat_a_clause(curr_clause_idx);                                   // unsat clause
                _lit_in_unsat_clause_num += cp->literals.size();
                _bool_lit_in_unsat_clause_num += cp->bool_literals.size();
            } else if (cp->sat_count == 0 && cp->sat_count + make_break_in_clause > 0) {  // a clause that was false has at least one of its literals made true.
                sat_a_clause(curr_clause_idx);                                            // sat a clause
                _lit_in_unsat_clause_num -= cp->literals.size();
                _bool_lit_in_unsat_clause_num -= cp->bool_literals.size();
            }
            int origin_sat_count = cp->sat_count;
            int origin_watch_lit = cp->min_delta_lit_index;
            cp->sat_count += make_break_in_clause;
            if (cp->sat_count > 0 && cp->sat_count < cp->literals.size()) {
                _sat_clause_with_false_literal->insert_element((int)curr_clause_idx);
            } else {
                _sat_clause_with_false_literal->delete_element((int)curr_clause_idx);
            }
            // update the minimum delta literal for this clause
            // if new_future_min_delta <= cp->min_delta, then min_delta and watch needs updating if var is changed
            if (new_future_min_delta <= cp->min_delta) {
                cp->min_delta = new_future_min_delta;
                cp->min_delta_lit_index = min_delta_lit_idx;
            } else if (contained_in_min_delta_lit) {   // this variable exists in the minimum delta literal, and changing it increases the delta of that literal.
                for (int cp_lit_idx : cp->literals) {  // update the minimum delta literal in this clause
                    if (!_lit_occur->is_in_array(std::abs(cp_lit_idx))) {
                        pos_delta = _lits[std::abs(cp_lit_idx)].delta;
                        convert_to_pos_delta(pos_delta, cp_lit_idx);
                        if (pos_delta < new_future_min_delta) {
                            new_future_min_delta = pos_delta;
                            min_delta_lit_idx = cp_lit_idx;
                        }
                    }
                }
                cp->min_delta = new_future_min_delta;
                cp->min_delta_lit_index = min_delta_lit_idx;
            }  // if new_future_min_delta>cp->min_delta and var_idx belongs to the watch_lit
            if (_num_bool_lits > 0) {
                if (make_break_in_clause > 0) {
                    if (origin_sat_count == 0) {  // make the unsat clause become sat
                        for (int l_sign_idx : cp->bool_literals) {
                            lit* l = &(_lits[std::abs(l_sign_idx)]);
                            _vars[l->delta].score -= cp->weight;
                        }
                    } else if (origin_sat_count == 1) {  // make a clause with only one true literal have one more true literal
                        lit* l = &(_lits[std::abs(origin_watch_lit)]);
                        if (!l->is_lia_lit) {
                            _vars[l->delta].score += cp->weight;
                        }
                    }
                } else if (make_break_in_clause < 0) {
                    if (cp->sat_count == 0) {  // unsat clause still unsat
                        for (int l_sign_idx : cp->bool_literals) {
                            lit* l = &(_lits[std::abs(l_sign_idx)]);
                            _vars[l->delta].score += cp->weight;
                        }
                    } else if (cp->sat_count == 1) {  // sat clause become unsat
                        lit* l = &(_lits[std::abs(cp->min_delta_lit_index)]);
                        if (!l->is_lia_lit) {
                            _vars[l->delta].score -= cp->weight;
                        }
                    }
                }
            }
            make_break_in_clause = 0;
            new_future_min_delta = max_int;
            contained_in_min_delta_lit = false;
            _lit_occur->clear();
        }
    }
    // updating literals that contain var
    for (int i = 0; i < var->literals.size(); i++) {
        lit_idx = std::abs(var->literals[i]);
        if (lit_exist[lit_idx] == 0) {
            l = &(_lits[lit_idx]);
            __int128_t tmp;
            is_overflow = __builtin_mul_overflow(var->literal_coff[i], change_value, &tmp) || is_overflow;
            // SASSERT(!is_overflow);
            is_overflow = __builtin_add_overflow(l->delta, tmp, &l->delta) || is_overflow;
            // SASSERT(!is_overflow);
            // l->delta += (var->literal_coff[i] * change_value);
            if (is_overflow && !update_sampling_interval) {
                shrinkSampleInterval(l);
            }
            lit_exist[lit_idx] = 1;
        }
    }
    // SASSERT(!overflow);
    // reset lit_exist
    for (int i = 0; i < var->literals.size(); i++) {
        lit_idx = std::abs(var->literals[i]);
        lit_exist[lit_idx] = 0;
    }
}

// dedicated for boolean var
void ls_sampler::critical_score_subscore(uint64_t var_idx) {
    variable* var = &(_vars[var_idx]);  // 获取布尔变量
    __int128_t pos_delta;
    int make_break_in_clause = 0;
    __int128_t new_future_min_delta = max_int;
    int watch_lit = 0;
    int l_sign_idx;
    lit* l;
    for (int i = 0; i < var->literals.size(); i++) {  // 遍历所有包含该变量的文字
        l_sign_idx = var->literals[i];
        l = &(_lits[l_sign_idx]);
        convert_to_pos_delta(pos_delta, l_sign_idx);  // dtt
        if (pos_delta == 0) {                         // true to false
            make_break_in_clause = -1;
            new_future_min_delta = 1;  // TODO::average_k
        } else {                       // false to true
            make_break_in_clause = 1;
            new_future_min_delta = 0;
        }
        watch_lit = l_sign_idx;
        int clause_idx = var->literal_clause[i];
        clause* cp = &(_clauses[clause_idx]);
        if (cp->sat_count > 0 && cp->sat_count + make_break_in_clause == 0) {  // 本次操作会使得子句变为假
            unsat_a_clause(clause_idx);
            _lit_in_unsat_clause_num += cp->literals.size();
            _bool_lit_in_unsat_clause_num += cp->bool_literals.size();
        } else if (cp->sat_count == 0 && cp->sat_count + make_break_in_clause > 0) {  // 本次操作会使得子句变为真
            sat_a_clause(clause_idx);
            _lit_in_unsat_clause_num -= cp->literals.size();
            _bool_lit_in_unsat_clause_num -= cp->bool_literals.size();
        }
        int origin_watch_lit = cp->min_delta_lit_index;
        int origin_sat_count = cp->sat_count;
        cp->sat_count += make_break_in_clause;
        if (cp->sat_count > 0 && cp->sat_count < cp->literals.size()) {
            _sat_clause_with_false_literal->insert_element(clause_idx);
        } else {
            _sat_clause_with_false_literal->delete_element(clause_idx);
        }
        if (new_future_min_delta <= cp->min_delta) {
            cp->min_delta = new_future_min_delta;
            cp->min_delta_lit_index = watch_lit;
        } else if (cp->min_delta_lit_index == l_sign_idx) {
            for (int l_sign_idx_inner : cp->literals) {
                if (cp->min_delta_lit_index != l_sign_idx_inner) {
                    pos_delta = _lits[std::abs(l_sign_idx_inner)].delta;
                    convert_to_pos_delta(pos_delta, l_sign_idx_inner);
                    if (pos_delta < new_future_min_delta) {
                        new_future_min_delta = pos_delta;
                        watch_lit = l_sign_idx_inner;
                    }
                }
            }
            cp->min_delta = new_future_min_delta;
            cp->min_delta_lit_index = watch_lit;
        }
        if (make_break_in_clause > 0) {
            if (origin_sat_count == 0) {
                for (int bl : cp->bool_literals) {
                    lit* l = &(_lits[std::abs(bl)]);
                    _vars[l->delta].score -= cp->weight;
                }
            } else if (origin_sat_count == 1) {
                lit* l = &(_lits[std::abs(origin_watch_lit)]);
                if (!l->is_lia_lit) {
                    _vars[l->delta].score += cp->weight;
                }
            }
        } else if (make_break_in_clause < 0) {
            if (cp->sat_count == 0) {
                for (int bl : cp->bool_literals) {
                    lit* l = &(_lits[std::abs(bl)]);
                    _vars[l->delta].score += cp->weight;
                }
            } else if (cp->sat_count == 1) {
                lit* l = &(_lits[std::abs(cp->min_delta_lit_index)]);
                if (!l->is_lia_lit) {
                    _vars[l->delta].score -= cp->weight;
                }
            }
        }
    }
}

// calculate score
__int128_t ls_sampler::critical_score(uint64_t var_idx, __int128_t change_value) {
    lit* l;
    clause* cp;
    __int128_t critical_score = 0;
    __int128_t delta_old, delta_new, l_clause_idx;
    __int128_t tmp;
    // number of make_lits in a clause
    int make_break_in_clause = 0;
    variable* var = &(_vars[var_idx]);
    for (int i = 0; i < var->literals.size(); i++) {
        l = &(_lits[std::abs(var->literals[i])]);
        l_clause_idx = var->literal_clause[i];
        delta_old = l->delta;
        is_overflow = __builtin_mul_overflow(var->literal_coff[i], change_value, &tmp) || is_overflow;

        // SAMPLER_CTRACE(
        //     is_overflow,
        //     tout << "var->literal_coff[i]: " << print_128(var->literal_coff[i]) << "\n";
        //     tout << "change_value: " << print_128(change_value) << "\n";

        //     print_literal(tout, *l););

        // SASSERT(!is_overflow);
        is_overflow = __builtin_add_overflow(delta_old, tmp, &delta_new) || is_overflow;
        // SASSERT(!is_overflow);
        if (is_overflow && !update_sampling_interval) {
            shrinkSampleInterval(l);
        }

        // delta_new = delta_old + (var->literal_coff[i] * change_value);  // l_clause_idx means that the coff is positive, and vice versa
        if ((!l->is_equal && delta_old <= 0 && delta_new > 0) || (l->is_equal && delta_old == 0 && delta_new != 0))
            make_break_in_clause = (var->literals[i] > 0) ? (make_break_in_clause - 1) : (make_break_in_clause + 1);
        else if ((!l->is_equal && delta_old > 0 && delta_new <= 0) || (l->is_equal && delta_old != 0 && delta_new == 0))
            make_break_in_clause = (var->literals[i] > 0) ? (make_break_in_clause + 1) : (make_break_in_clause - 1);
        // enter a new clause or the last literal
        if ((i != (var->literals.size() - 1) && l_clause_idx != var->literal_clause[i + 1]) || i == (var->literals.size() - 1)) {
            cp = &(_clauses[abs_128(l_clause_idx)]);
            if (cp->sat_count == 0 && cp->sat_count + make_break_in_clause > 0)
                critical_score += cp->weight;
            else if (cp->sat_count > 0 && cp->sat_count + make_break_in_clause == 0)
                critical_score -= cp->weight;
            make_break_in_clause = 0;
        }
    }
    // SASSERT(!overflow);
    return critical_score;
}

void ls_sampler::modify_CC(uint64_t var_idx, int direction) {
}

void ls_sampler::insert_operation(int var_idx, __int128_t change_value, int& operation_idx) {
    __int128_t future_solution = _solution[var_idx] + change_value;
    bool no_pre_value = (_pre_value_1[var_idx] == INT32_MAX && _pre_value_2[var_idx] == INT32_MAX &&
                         future_solution >= _vars[var_idx].low_bound && future_solution <= _vars[var_idx].upper_bound);
    bool has_pre_value_1 = (_pre_value_1[var_idx] != INT32_MAX && _pre_value_2[var_idx] == INT32_MAX &&
                            future_solution == _pre_value_1[var_idx]);
    bool has_pre_value_2 = (_pre_value_1[var_idx] != INT32_MAX && _pre_value_2[var_idx] != INT32_MAX &&
                            (future_solution == _pre_value_1[var_idx] || future_solution == _pre_value_2[var_idx]));
    if (no_pre_value || has_pre_value_1 || has_pre_value_2) {  // if the change is legal, the change is recorded
        //    if(future_solution>=_vars[var_idx].low_bound&&future_solution<=_vars[var_idx].upper_bound){
        _operation_var_idx_vec[operation_idx] = var_idx;              // op var
        _operation_change_value_vec[operation_idx++] = change_value;  // op val
    }
}

void ls_sampler::insert_operation(int var_idx, __int128_t change_value, int& operation_idx, int const& flip_lit) {
    __int128_t future_solution = _solution[var_idx] + change_value;
    bool no_pre_value = (_pre_value_1[var_idx] == INT32_MAX && _pre_value_2[var_idx] == INT32_MAX &&
                         future_solution >= _vars[var_idx].low_bound && future_solution <= _vars[var_idx].upper_bound);
    bool has_pre_value_1 = (_pre_value_1[var_idx] != INT32_MAX && _pre_value_2[var_idx] == INT32_MAX &&
                            future_solution == _pre_value_1[var_idx]);
    bool has_pre_value_2 = (_pre_value_1[var_idx] != INT32_MAX && _pre_value_2[var_idx] != INT32_MAX &&
                            (future_solution == _pre_value_1[var_idx] || future_solution == _pre_value_2[var_idx]));

    if (no_pre_value || has_pre_value_1 || has_pre_value_2) {         // if the change is legal, the change is recorded
                                                                      //    if(future_solution>=_vars[var_idx].low_bound&&future_solution<=_vars[var_idx].upper_bound){
        _operation_var_idx_vec[operation_idx] = var_idx;              // op var
        _operation_lit_idx_vec[operation_idx] = flip_lit;             // op lit
        _operation_change_value_vec[operation_idx++] = change_value;  // op val
    }
}

int ls_sampler::pick_critical_move_bool() {
    __int128_t best_score, score;
    int best_var_idx, cnt, operation;
    bool BMS = false;  // BMS heuristic
    best_score = 1;
    best_var_idx = -1;
    uint64_t best_last_move = UINT64_MAX;
    int operation_idx = 0;

    // iterate over all unsatisfied clauses containing Boolean variables
    for (int i = 0; i < _contain_bool_unsat_clauses->size(); i++) {
        int clause_idx = _contain_bool_unsat_clauses->element_at(i);
        clause* cl = &(_clauses[clause_idx]);
        for (int l_sign_idx : cl->bool_literals) {
            lit* l = &(_lits[std::abs(l_sign_idx)]);
            if (_is_chosen_bool_var[l->delta])
                continue;
            if (_step > _tabulist[2 * l->delta] && _CClist[2 * l->delta] > 0) {
                _operation_var_idx_bool_vec[operation_idx++] = (int)l->delta;
                _is_chosen_bool_var[l->delta] = true;
            }
        }
    }
    for (int i = 0; i < operation_idx; i++) {
        _is_chosen_bool_var[_operation_var_idx_bool_vec[i]] = false;
    }  // recover chosen_bool_var
    if (operation_idx > 45) {
        BMS = true;
        cnt = 45;
    } else {
        BMS = false;
        cnt = operation_idx;
    }
    for (int i = 0; i < cnt; i++) {
        if (BMS) {
            int idx = mt() % (operation_idx - i);
            int tmp = _operation_var_idx_bool_vec[operation_idx - i - 1];
            operation = _operation_var_idx_bool_vec[idx];
            _operation_var_idx_bool_vec[idx] = tmp;
        } else {
            operation = _operation_var_idx_bool_vec[i];
        }
        int var_idx = operation;
        score = _vars[var_idx].score;
        uint64_t last_move_step = _last_move[2 * var_idx];
        if (score > best_score || (score == best_score && last_move_step < best_last_move)) {
            best_score = score;
            best_var_idx = var_idx;
            best_last_move = last_move_step;
        }
    }
    // if there is untabu decreasing move
    if (best_var_idx != -1) {
        return best_var_idx;
    }
    // update weight
    if (mt() % 10000 > smooth_probability) {
        update_clause_weight();
    } else {
        smooth_clause_weight();
    }
    random_walk();
    return -1;
}

#ifdef EQ2INEQ_BUILD_TABLE
void ls_sampler::build_equal_table() {
    std::map<std::string, __int128_t> hash_table;
    bool equ_flag;
    for (int i = 0; i < _lits.size(); ++i) {
        lit* l = &_lits[i];
        if (l->lits_index == 0 || !l->is_lia_lit || l->is_equal || !_lit_appear[i])
            continue;
        equ_flag = true;
        if (!hash_table.empty()) {
            for (int j = 0; j < l->pos_coff.size(); ++j) {
                if (hash_table.find(_vars[l->pos_coff_var_idx[j]].var_name) == hash_table.end()) {
                    equ_flag = false;
                    break;
                }
                if (hash_table[_vars[l->pos_coff_var_idx[j]].var_name] != -l->pos_coff[j]) {
                    equ_flag = false;
                    break;
                }
            }
            for (int j = 0; j < l->neg_coff.size(); ++j) {
                if (!equ_flag)
                    break;
                if (hash_table.find(_vars[l->neg_coff_var_idx[j]].var_name) == hash_table.end()) {
                    equ_flag = false;
                    break;
                }
                if (hash_table[_vars[l->neg_coff_var_idx[j]].var_name] != l->neg_coff[j]) {
                    equ_flag = false;
                    break;
                }
            }
            if (hash_table["key"] != -l->key) {
                equ_flag = false;
            }
        } else {
            equ_flag = false;
        }

        // 更新 hash_table
        hash_table.clear();
        for (int j = 0; j < l->pos_coff.size(); ++j) {
            std::pair<std::string, __int128_t> t = {_vars[l->pos_coff_var_idx[j]].var_name, l->pos_coff[j]};
            hash_table.insert(t);
        }
        for (int j = 0; j < l->neg_coff.size(); ++j) {
            std::pair<std::string, __int128_t> t = {_vars[l->neg_coff_var_idx[j]].var_name, -l->neg_coff[j]};
            hash_table.insert(t);
        }
        std::pair<std::string, __int128_t> t = {"key", l->key};
        hash_table.insert(t);

        // 将等式对应的两个不等式文字在 _lits 中的索引存储于 equ_table
        if (equ_flag) {
            _ineq_form_cnt++;
            // std::cout << "term in equ: " << l->pos_coff.size() + l->neg_coff.size() << "\n";
            for (int j = 0; j < l->pos_coff.size(); ++j) {
                _vars[l->pos_coff_var_idx[j]].is_in_equal = true;
            }
            for (int j = 0; j < l->neg_coff.size(); ++j) {
                _vars[l->neg_coff_var_idx[j]].is_in_equal = true;
            }
            _lits[i - 1].equal_pair = i;
            _lits[i].equal_pair = i - 1;
            std::pair<int, int> p(i - 1, i);
            equal_table.push_back(p);
        }
    }

    TRACE(
        "equal_table",
        tout << "equ_table:\n";
        for (int i = 0; i < equal_table.size(); ++i) {
            tout << "{ " << equal_table[i].first << ", " << equal_table[i].second << " }\n";
        });
}
#endif

void ls_sampler::build_occs_closures() {
    // 构建 occs 相关闭包
    std::queue<size_t> vars_in_equal_closure;
    std::queue<size_t> vars_in_occs_closure;
    std::vector<bool> visited_equal(_vars.size(), false);
    std::vector<bool> visited_occs(_vars.size(), false);

    for (size_t i = 0; i < _vars.size(); ++i) {
        if (_vars[i].is_lia) {
            // _vars[i].init_to_zero = true;
            if (_vars[i].occs >= 50) {
                _vars[i].in_occs_closure = true;
                vars_in_occs_closure.push(i);
                visited_occs[i] = true;
#ifdef VERBOSE
                _num_occs_closure_vars++;
#endif
            }
            if (_vars[i].is_in_equal == true) {
                _vars[i].in_equal_closure = true;
                vars_in_equal_closure.push(i);
                visited_equal[i] = true;
#ifdef VERBOSE
                _num_equal_closure_vars++;
#endif
            }
        }
    }

    // 计算等式变量闭包
    while (!vars_in_equal_closure.empty()) {
        size_t var_idx = vars_in_equal_closure.front();
        vars_in_equal_closure.pop();

        for (int j = 0; j < _vars[var_idx].literals.size(); ++j) {
            lit* l = &_lits[std::abs(_vars[var_idx].literals[j])];
            for (size_t k = 0; k < l->pos_coff.size(); ++k) {
                if (!visited_equal[l->pos_coff_var_idx[k]]) {
#ifdef VERBOSE
                    _num_equal_closure_vars++;
#endif
                    _vars[l->pos_coff_var_idx[k]].in_equal_closure = true;
                    vars_in_equal_closure.push(l->pos_coff_var_idx[k]);
                    visited_equal[l->pos_coff_var_idx[k]] = true;
                }
            }
            for (size_t k = 0; k < l->neg_coff.size(); ++k) {
                if (!visited_equal[l->neg_coff_var_idx[k]]) {
#ifdef VERBOSE
                    _num_equal_closure_vars++;
#endif
                    _vars[l->neg_coff_var_idx[k]].in_equal_closure = true;
                    vars_in_equal_closure.push(l->neg_coff_var_idx[k]);
                    visited_equal[l->neg_coff_var_idx[k]] = true;
                }
            }
        }
    }

    // 计算高频变量闭包
    while (!vars_in_occs_closure.empty()) {
        size_t var_idx = vars_in_occs_closure.front();
        vars_in_occs_closure.pop();

        for (int j = 0; j < _vars[var_idx].literals.size(); ++j) {
            lit* l = &_lits[std::abs(_vars[var_idx].literals[j])];
            for (size_t k = 0; k < l->pos_coff.size(); ++k) {
                if (!visited_occs[l->pos_coff_var_idx[k]]) {
#ifdef VERBOSE
                    _num_occs_closure_vars++;
#endif
                    _vars[l->pos_coff_var_idx[k]].in_occs_closure = true;
                    vars_in_occs_closure.push(l->pos_coff_var_idx[k]);
                    visited_occs[l->pos_coff_var_idx[k]] = true;
                }
            }
            for (size_t k = 0; k < l->neg_coff.size(); ++k) {
                if (!visited_occs[l->neg_coff_var_idx[k]]) {
#ifdef VERBOSE
                    _num_occs_closure_vars++;
#endif
                    _vars[l->neg_coff_var_idx[k]].in_occs_closure = true;
                    vars_in_occs_closure.push(l->neg_coff_var_idx[k]);
                    visited_occs[l->neg_coff_var_idx[k]] = true;
                }
            }
        }
    }

#ifdef VERBOSE
    for (size_t i = 0; i < _vars.size(); ++i) {
        if (!(_vars[i].in_equal_closure || _vars[i].in_occs_closure)) {
            _num_ordinary_vars++;
        }
    }
#endif

    TRACE("build_occs_closures", for (size_t i = 0; i < _vars.size(); ++i) {
        if (!_vars[i].is_lia)
            continue;
        if (_vars[i].in_occs_closure) {
            std::cout << "in_occs_closure: " << _vars[i].var_name << "\n";
        } else if (_vars[i].in_equal_closure){
            std::cout << "in_equal_closure: " << _vars[i].var_name << "\n";
        } else {
            std::cout << "ordinary var: " << _vars[i].var_name << "\n";
        } });
}

/*
    \brief Calculate the movement increment 'best_value';
    \return lia variables that need to be changed
*/
int ls_sampler::pick_critical_move(__int128_t& best_value) {
    __int128_t best_score, score;
    int operation_var_idx, operation_lit_idx, best_var_idx, best_lit_idx = -1, cnt;
    double best_lit_idx_rank, operation_lit_idx_rank;
    int best_bit_gain = 0, curr_bit_gain = 0;
    __int128_t operation_change_value, change_value;
    bool BMS = false;  // Best Move Strategy
    bool should_push_vec;
    best_score = (is_idl) ? 0 : 1;
    best_var_idx = -1;
    change_value = 0;
    uint64_t best_last_move = UINT64_MAX;
    int operation_idx = 0;
    // 计算临界值
    for (int i = 0; i < _unsat_clauses->size(); i++) {
        clause* cl = &(_clauses[_unsat_clauses->element_at(i)]);
        for (int l_sign_ldx : cl->lia_literals) {
            int l_idx = std::abs(l_sign_ldx);
            lit* l = &(_lits[l_idx]);

            if (l->is_equal) {
                // SASSERT(false);
                if (l_sign_ldx < 0) {  // negative literal, -(a = b) TODO 可以区间采样
                    for (int var_idx : l->pos_coff_var_idx) {
                        if (_step > _tabulist[2 * var_idx]) {
                            insert_operation(var_idx, 1, operation_idx, l_idx);
                        }
                        if (_step > _tabulist[2 * var_idx + 1]) {
                            insert_operation(var_idx, -1, operation_idx, l_idx);
                        }
                    }
                    for (int var_idx : l->neg_coff_var_idx) {
                        if (_step > _tabulist[2 * var_idx]) {
                            insert_operation(var_idx, 1, operation_idx, l_idx);
                        }
                        if (_step > _tabulist[2 * var_idx + 1]) {
                            insert_operation(var_idx, -1, operation_idx, l_idx);
                        }
                    }
                }  // delta should not be 0, while it is 0, so the var should increase 1/-1
                else {
                    for (int j = 0; j < l->pos_coff.size(); j++) {
                        int var_idx = l->pos_coff_var_idx[j];
                        if ((l->delta % l->pos_coff[j]) != 0) {
                            continue;
                        }
                        if ((l->delta < 0 && _step > _tabulist[2 * var_idx]) ||
                            (l->delta > 0 && _step > _tabulist[2 * var_idx + 1])) {
                            insert_operation(var_idx, (-l->delta / l->pos_coff[j]), operation_idx, l_idx);
                        }
                    }
                    for (int j = 0; j < l->neg_coff.size(); j++) {
                        int var_idx = l->neg_coff_var_idx[j];
                        if ((l->delta % l->neg_coff[j]) != 0) {
                            continue;
                        }
                        if ((l->delta > 0 && _step > _tabulist[2 * var_idx]) ||
                            (l->delta < 0 && _step > _tabulist[2 * var_idx + 1])) {
                            insert_operation(var_idx, (l->delta / l->neg_coff[j]), operation_idx, l_idx);
                        }
                    }
                }  // delta should be 0, while it is not 0, so the var should increase (-delta/coff), while (-delta%coff)==0
                continue;
            }

            for (int i = 0; i < l->pos_coff.size(); i++) {
                should_push_vec = false;
                int var_idx = l->pos_coff_var_idx[i];
                if (var_idx == _lia_var_idx_with_most_lits) {
                    continue;
                }
                if (l_sign_ldx > 0 && _step > _tabulist[2 * var_idx + 1]) {
                    should_push_vec = true;
                    change_value = devide(-l->delta, l->pos_coff[i]);
                } else if (l_sign_ldx < 0 && _step > _tabulist[2 * var_idx]) {
                    should_push_vec = true;
                    change_value = devide(1 - l->delta, l->pos_coff[i]);
                }
                if (should_push_vec) {
#ifndef BAM_V2
                    if (_use_interval_move && !(is_pb || _vars[var_idx].is_in_equal))
                        interval_move(var_idx, change_value);
#endif
                    insert_operation(var_idx, change_value, operation_idx, l_idx);
                }
                // if l_idx>0, delta should be <=0, while it is now >0(too large), so the var should enlarge by (-delta/coff) (this is a negative value), if l_idx<0, delta should be >=1, while it is now <1(too small), so the var should enlarge by (1-delta)/coff (positive value)
            }
            for (int i = 0; i < l->neg_coff.size(); i++) {
                should_push_vec = false;
                int var_idx = l->neg_coff_var_idx[i];
                if (var_idx == _lia_var_idx_with_most_lits) {
                    continue;
                }
                if (l_sign_ldx > 0 && _step > _tabulist[2 * var_idx]) {
                    should_push_vec = true;
                    change_value = devide(l->delta, l->neg_coff[i]);
                } else if (l_sign_ldx < 0 && _step > _tabulist[2 * var_idx + 1]) {
                    should_push_vec = true;
                    change_value = devide(l->delta - 1, l->neg_coff[i]);
                }
                if (should_push_vec) {
#ifndef BAM_V2
                    if (_use_interval_move && !(is_pb || _vars[var_idx].is_in_equal))
                        interval_move(var_idx, change_value);
#endif
                    insert_operation(var_idx, change_value, operation_idx, l_idx);
                }
                // if l_idx>0, delta should be <=0, while it is now >0(too large), so the var should enlarge by (delta/coff) (this is a positive value since the coff is neg), if l_idx<0, the delta should be >=1, while it is now <1(too small), so the var should enlarge by (delta-1)/coff (neg value)
            }
        }
    }
    // go through the forward and backward move of vars, evaluate their score, pick the untabued best one
    if (operation_idx > 45) {
        BMS = true;
        cnt = 45;
    } else {
        BMS = false;
        cnt = operation_idx;
    }

    for (int i = 0; i < cnt; i++) {
        if (BMS) {
            int idx = mt() % (operation_idx - i);
            operation_change_value = _operation_change_value_vec[idx];
            operation_var_idx = _operation_var_idx_vec[idx];
            operation_lit_idx = _operation_lit_idx_vec[idx];
            _operation_change_value_vec[idx] = _operation_change_value_vec[operation_idx - i - 1];
            _operation_var_idx_vec[idx] = _operation_var_idx_vec[operation_idx - i - 1];
            _operation_lit_idx_vec[idx] = _operation_lit_idx_vec[operation_idx - i - 1];
        } else {
            operation_change_value = _operation_change_value_vec[i];
            operation_var_idx = _operation_var_idx_vec[i];
            operation_lit_idx = _operation_lit_idx_vec[i];
        }
        score = critical_score(operation_var_idx, operation_change_value);
        int opposite_direction = (operation_change_value > 0) ? 1 : 0;  // if the change value is >0, then means it is moving forward, the opposite direction is 1(backward)
        uint64_t last_move_step = _last_move[2 * operation_var_idx + opposite_direction];

        if (score > best_score || (score == best_score && last_move_step < best_last_move)) {
            best_score = score;
            best_var_idx = operation_var_idx;
            best_lit_idx = operation_lit_idx;
            best_value = operation_change_value;
            best_last_move = last_move_step;
        }
    }
    // if there is untabu decreasing move
    if (best_var_idx != -1) {
        _last_flip_lia_lit = best_lit_idx;
        return best_var_idx;
    }
    // choose from swap operations if there is no decreasing unsat critical
    if (!_sat_clause_with_false_literal->empty()) {
        best_score = 0;
        operation_idx = 0;
        for (int i = 0; operation_idx < 20 && i < 50; i++) {
            add_swap_operation(operation_idx);
        }
        for (int i = 0; i < operation_idx; i++) {
            operation_change_value = _operation_change_value_vec[i];
            operation_var_idx = _operation_var_idx_vec[i];
            operation_lit_idx = _operation_lit_idx_vec[i];
            score = critical_score(operation_var_idx, operation_change_value);
            int opposite_direction = (operation_change_value > 0) ? 1 : 0;
            uint64_t last_move_step = _last_move[2 * operation_var_idx + opposite_direction];
            if (score > best_score || (score == best_score && last_move_step < best_last_move)) {
                best_score = score;
                best_var_idx = operation_var_idx;
                best_lit_idx = operation_lit_idx;
                best_value = operation_change_value;
                best_last_move = last_move_step;
            }
        }
        if (best_var_idx != -1) {
            _last_flip_lia_lit = best_lit_idx;
            return best_var_idx;
        }
    }
    // update weight and random walk
    if (mt() % 10000 > smooth_probability) {
        update_clause_weight();
    } else {
        smooth_clause_weight();
    }
    random_walk();
    return -1;
}

#ifndef BAM_V2
// 区间移动
void ls_sampler::interval_move(uint64_t var_idx, __int128_t& change_value) {
    // if (is_pb || _vars[var_idx].is_in_equal)  //
    //     return;
    __int64_t slack_val = 0;
    __int128_t random_val = 0, delta;
    __int128_t term_val = 0, coff_val = 1;
    variable* var = &(_vars[var_idx]);
    int sign_l_idx, l_idx;
    __int128_t constraint_upper_bound = var->s_upper_bound, constraint_lower_bound = var->s_lower_bound;
    SASSERT(var->s_upper_bound >= var->s_lower_bound);

    if (change_value > 0) {  // lower bound = _solution[var_idx] + change_value
        constraint_lower_bound = _solution[var_idx] + change_value;
        // calc upper bound accroding to true lits which contain var
        for (int i = 0; i < var->literals.size(); ++i) {
            random_val = 0;

            sign_l_idx = var->literals[i];
            l_idx = std::abs(sign_l_idx);

#ifndef BAM_V1
            // 计算跳过的概率
            double prob = (double)_lits[l_idx].sat_steps_count / (double)_step;
            // 创建一个均匀分布的浮点数生成器，范围 [0, 1)
            std::uniform_real_distribution<> dist(0.0, 1.0);
            if (dist(mt) <= prob) {
                continue;
            }
#endif

            delta = delta_lit(_lits[l_idx]);
            // true lit
            SASSERT(!_lits[l_idx].is_equal && _lits[l_idx].equal_pair == -1);
            if (((delta <= 0 && sign_l_idx > 0) || (delta > 0 && sign_l_idx < 0))) {
                coff_val = var->literal_coff[i];
                term_val = coff_val * _solution[var_idx];
                if ((sign_l_idx > 0 && coff_val > 0) || (sign_l_idx < 0 && coff_val < 0)) {  // coff * x + delta' <= 0 --> x <= (val(x) - delta) / coff
                    __int128_t tmp_upper_bound = floor_div((term_val - _lits[l_idx].delta), coff_val, (sign_l_idx < 0));
                    if (tmp_upper_bound < constraint_upper_bound && constraint_lower_bound <= tmp_upper_bound) {
                        constraint_upper_bound = tmp_upper_bound;
                    }
                }
            }
        }  // lia lit
        slack_val = constraint_upper_bound - constraint_lower_bound + 1;
        // std::cout << "slack_val = " << print_128(slack_val) << "\n";
        if (slack_val > 0) {
            random_val = random_int64_in_range(0, slack_val);
        }
        change_value += random_val;
    } else if (change_value < 0) {  // upper bound = _solution[var_idx] + change_value
        constraint_upper_bound = _solution[var_idx] + change_value;
        // calc lower bound accroding to true lits which contain var
        for (int i = 0; i < var->literals.size(); ++i) {
            sign_l_idx = var->literals[i];
            l_idx = std::abs(sign_l_idx);

#ifndef BAM_V1
            // 计算跳过的概率
            double prob = (double)_lits[l_idx].sat_steps_count / (double)_step;
            // 创建一个均匀分布的浮点数生成器，范围 [0, 1)
            std::uniform_real_distribution<> dist(0.0, 1.0);
            if (dist(mt) <= prob) {
                continue;
            }
#endif

            delta = delta_lit(_lits[l_idx]);
            // true lit
            SASSERT(!_lits[l_idx].is_equal && _lits[l_idx].equal_pair == -1);
            if (((delta <= 0 && sign_l_idx > 0) || (delta > 0 && sign_l_idx < 0))) {
                coff_val = var->literal_coff[i];
                term_val = coff_val * _solution[var_idx];
                if ((sign_l_idx > 0 && coff_val < 0) || (sign_l_idx < 0 && coff_val > 0)) {  // coff * x + delta' <= 0 --> x >= (val(x) - delta) / coff
                    __int128_t tmp_lower_bound = ceil_div((term_val - _lits[l_idx].delta), coff_val, (sign_l_idx < 0));
                    if (tmp_lower_bound > constraint_lower_bound && constraint_upper_bound >= tmp_lower_bound) {
                        constraint_lower_bound = tmp_lower_bound;
                    }
                }
            }
        }
        slack_val = constraint_upper_bound - constraint_lower_bound + 1;
        // std::cout << "slack_val = " << print_128(slack_val) << "\n";
        if (slack_val > 0) {
            random_val = random_int64_in_range(0, slack_val);
        }
        change_value -= random_val;
    }
}
#endif

// random walk
void ls_sampler::update_clause_weight() {
    for (int i = 0; i < _unsat_clauses->size(); i++) {
        clause* unsat_cl = &(_clauses[_unsat_clauses->element_at(i)]);
        unsat_cl->weight++;
        for (int l_sign_idx : unsat_cl->bool_literals) {
            _vars[_lits[std::abs(l_sign_idx)].delta].score++;
        }
    }
    total_clause_weight += _unsat_clauses->size();
}

void ls_sampler::smooth_clause_weight() {
    for (int i = 0; i < _num_clauses; i++) {
        if (_clauses[i].weight > 1 && !_unsat_clauses->is_in_array(i)) {
            _clauses[i].weight--;
            total_clause_weight--;
            if (_clauses[i].sat_count == 1 && !_lits[std::abs(_clauses[i].min_delta_lit_index)].is_lia_lit) {
                __int128_t watch_lit_idx = _lits[std::abs(_clauses[i].min_delta_lit_index)].delta;
                _vars[watch_lit_idx].score++;
            }
        }
    }
}

void ls_sampler::random_walk() {
    int clause_idx, operation_idx, var_idx, lit_idx, operation_direction, best_op_lit_idx;
    double best_op_lit_idx_rank, lit_idx_rank;
    __int128_t change_value;  // measure of change
    __int128_t best_subscore = max_int;
    int best_score_bool = INT32_MIN;
    __int128_t subscore;
    __int128_t score;
    int best_operation_idx = 0;
    int best_operation_idx_bool = 0;
    uint64_t best_last_move = UINT64_MAX;
    uint64_t best_last_move_bool = UINT64_MAX;
    uint64_t last_move_step;
    operation_idx = 0;
    int operation_idx_bool = 0;
    clause* cp;
    lit* l;
    // determine the operations
    for (int i = 0; i < 3 && operation_idx + operation_idx_bool < 5; i++) {
        if (_unsat_clauses->size() == 0)
            return;
        clause_idx = _unsat_clauses->element_at(mt() % _unsat_clauses->size());  // random unsat clause
        cp = &(_clauses[clause_idx]);
        for (int l_sign_idx : cp->lia_literals) {
            int l_idx = std::abs(l_sign_idx);
            l = &(_lits[l_idx]);
            if (l->is_equal) {
                // SASSERT(false);
                if (l_sign_idx < 0) {  // negative literals means inequality
                    for (int var_idx : l->pos_coff_var_idx) {
                        insert_operation(var_idx, 1, operation_idx, l_idx);
                        insert_operation(var_idx, -1, operation_idx, l_idx);
                    }
                    for (int var_idx : l->neg_coff_var_idx) {
                        insert_operation(var_idx, 1, operation_idx, l_idx);
                        insert_operation(var_idx, -1, operation_idx, l_idx);
                    }
                }  // delta should not be 0, while it is 0, so the var should increase 1/-1
                else {  // positive literals means equality
                    for (int j = 0; j < l->pos_coff.size(); j++) {
                        int var_idx = l->pos_coff_var_idx[j];
                        if ((l->delta % l->pos_coff[j]) != 0) {
                            continue;
                        }
                        insert_operation(var_idx, (-l->delta / l->pos_coff[j]), operation_idx, l_idx);
                    }
                    for (int j = 0; j < l->neg_coff.size(); j++) {
                        int var_idx = l->neg_coff_var_idx[j];
                        if ((l->delta % l->neg_coff[j]) != 0) {
                            continue;
                        }
                        insert_operation(var_idx, (l->delta / l->neg_coff[j]), operation_idx, l_idx);
                    }
                }  // delta should be 0, while it is not 0, so the var should increase (-delta/coff), while (-delta%coff)==0
                continue;
            }
            // (c1*a + c2*b + key <= 0), delta = c1*a + c2*b + key
            for (int k = 0; k < l->pos_coff.size(); k++) {
                var_idx = l->pos_coff_var_idx[k];
                change_value = (l_sign_idx > 0) ? devide(-l->delta, l->pos_coff[k]) : devide(1 - l->delta, l->pos_coff[k]);
                // #ifdef INTERVAL_MOVE
                //                 interval_move(var_idx, change_value);
                // #endif
                insert_operation(var_idx, change_value, operation_idx, l_idx);
            }
            for (int k = 0; k < l->neg_coff.size(); k++) {
                var_idx = l->neg_coff_var_idx[k];
                change_value = (l_sign_idx > 0) ? devide(l->delta, l->neg_coff[k]) : devide(l->delta - 1, l->neg_coff[k]);
                // #ifdef INTERVAL_MOVE
                //                 interval_move(var_idx, change_value);
                // #endif
                insert_operation(var_idx, change_value, operation_idx, l_idx);
            }
        }
        for (int l_idx : cp->bool_literals) {
            __int128_t bool_var_idx = _lits[std::abs(l_idx)].delta;
            if (!_is_chosen_bool_var[bool_var_idx]) {
                _operation_var_idx_bool_vec[operation_idx_bool++] = (int)bool_var_idx;
                _is_chosen_bool_var[bool_var_idx] = true;
            }
        }
    }
    for (int i = 0; i < operation_idx_bool; i++) {  // Reset the set of Boolean variables to be manipulated
        _is_chosen_bool_var[_operation_var_idx_bool_vec[i]] = false;
    }
    // choose the best operation
    for (int i = 0; i < operation_idx; i++) {  // lia operations
        var_idx = _operation_var_idx_vec[i];
        lit_idx = _operation_lit_idx_vec[i];
        best_op_lit_idx = _operation_lit_idx_vec[best_operation_idx];
        change_value = _operation_change_value_vec[i];
        subscore = critical_subscore(var_idx, change_value);  // dscore
        operation_direction = (change_value > 0) ? 0 : 1;
        last_move_step = _last_move[2 * var_idx + (operation_direction + 1) % 2];
#ifdef PROB_GUIDED
        best_op_lit_idx_rank = _lits[best_op_lit_idx].delta <= 0 ? (1 - _lits[best_op_lit_idx].prob) : _lits[best_op_lit_idx].prob;
        lit_idx_rank = _lits[lit_idx].delta <= 0 ? (1 - _lits[lit_idx].prob) : _lits[lit_idx].prob;
#endif
        if (subscore < best_subscore || (subscore == best_subscore && last_move_step < best_last_move)
#ifdef PROB_GUIDED
            || (subscore == best_subscore && lit_idx_rank > best_op_lit_idx_rank)
#endif
        ) {
            best_subscore = subscore;  // dscore
            best_last_move = last_move_step;
            best_operation_idx = i;  // op id
        }
    }
    for (int i = 0; i < operation_idx_bool; i++) {  // boolean operations
        var_idx = _operation_var_idx_bool_vec[i];
        score = _vars[var_idx].score;  // score
        uint64_t last_move_step = _last_move[2 * var_idx];
        if (score > best_score_bool || (score == best_score_bool && last_move_step < best_last_move_bool)) {
            best_score_bool = score;  // score
            best_last_move_bool = last_move_step;
            best_operation_idx_bool = i;
        }
    }
    // make move
    if (operation_idx + operation_idx_bool == 0) {  // empty move
        return;
    }
    if (operation_idx_bool == 0 || (operation_idx > 0 && operation_idx_bool > 0 && !is_in_bool_search)) {  // only lia operation
        var_idx = _operation_var_idx_vec[best_operation_idx];
        lit_idx = _operation_lit_idx_vec[best_operation_idx];
        change_value = _operation_change_value_vec[best_operation_idx];
    } else {  // only bool operation
        var_idx = _operation_var_idx_bool_vec[best_operation_idx_bool];
        change_value = 0;
    }

    critical_move(var_idx, change_value);
    _last_flip_lia_lit = lit_idx;
    // if (_last_flip_lia_lit > 0 && _lits[abs(_last_flip_lia_lit)].equal_pair != -1 && _lits[_lits[abs(_last_flip_lia_lit)].equal_pair].delta > 0) {
    //     SASSERT(_lits[abs(_last_flip_lia_lit)].delta <= 0);
    //     equal_move(_last_flip_lia_lit, var_idx);
    // }
}

/*
    \brief return the dscore of op(var, change_val)
 */
__int128_t ls_sampler::critical_subscore(uint64_t var_idx, __int128_t change_value) {
    __int128_t critical_subscore = 0;  // dscore
    __int128_t delta_old, delta_new;
    variable* var = &(_vars[var_idx]);
    int lit_idx, l_clause_idx;
    __int128_t tmp1, tmp2;
    // the future min delta containing var
    __int128_t new_future_min_delta = max_int;
    bool contained_in_min_delta_lit = false;  // determing if the var appears in the lit with min delta
    _lit_occur->clear();
    for (int i = 0; i < var->literals.size(); i++) {
        lit_idx = var->literals[i];             // literal contains var
        l_clause_idx = var->literal_clause[i];  // clause contains literal
        _lit_occur->insert_element(std::abs(lit_idx));
        if (lit_idx == _clauses[l_clause_idx].min_delta_lit_index) {  // min{dtt(l, alpha)}, l in c.
            contained_in_min_delta_lit = true;
        }
        is_overflow = __builtin_mul_overflow(change_value, var->literal_coff[i], &tmp1) || is_overflow;
        // SASSERT(!is_overflow);
        is_overflow = __builtin_add_overflow(_lits[std::abs(lit_idx)].delta, tmp1, &delta_new) || is_overflow;
        // SASSERT(!is_overflow);
        // delta_new = _lits[std::abs(lit_idx)].delta + (change_value * var->literal_coff[i]);

        if (is_overflow && !update_sampling_interval) {
            shrinkSampleInterval(&_lits[std::abs(lit_idx)]);
        }

        convert_to_pos_delta(delta_new, lit_idx);
        if (delta_new < new_future_min_delta) {
            new_future_min_delta = delta_new;
        }
        // enter a new clause or the last literal
        if ((i != (var->literals.size() - 1) && l_clause_idx != var->literal_clause[i + 1]) || i == (var->literals.size() - 1)) {
            clause* cp = &(_clauses[l_clause_idx]);
            if (new_future_min_delta <= cp->min_delta) {
                is_overflow = __builtin_sub_overflow(new_future_min_delta, cp->min_delta, &tmp1) || is_overflow;
                // SASSERT(!is_overflow);
                is_overflow = __builtin_mul_overflow(tmp1, cp->weight, &tmp2) || is_overflow;
                // SASSERT(!is_overflow);
                is_overflow = __builtin_add_overflow(critical_subscore, tmp2, &critical_subscore) || is_overflow;
                // SASSERT(!is_overflow);
                // critical_subscore += (new_future_min_delta - cp->min_delta) * cp->weight;  // dscore
            } else if (contained_in_min_delta_lit) {
                for (int lit_idx_in_cp : cp->literals) {
                    if (!_lit_occur->is_in_array(std::abs(lit_idx_in_cp))) {
                        delta_old = _lits[std::abs(lit_idx_in_cp)].delta;
                        convert_to_pos_delta(delta_old, lit_idx_in_cp);
                        if (delta_old < new_future_min_delta) {
                            new_future_min_delta = delta_old;
                        }
                    }
                }
                is_overflow = __builtin_sub_overflow(new_future_min_delta, cp->min_delta, &tmp1) || is_overflow;
                // SASSERT(!is_overflow);
                is_overflow = __builtin_mul_overflow(tmp1, cp->weight, &tmp2) || is_overflow;
                // SASSERT(!is_overflow);
                is_overflow = __builtin_add_overflow(critical_subscore, tmp2, &critical_subscore) || is_overflow;
                // SASSERT(!is_overflow);
                // critical_subscore += (new_future_min_delta - cp->min_delta) * cp->weight;
            }  // if new_future_min_delta > cp->min_delta and var_idx belongs to the min_delta_lit
            new_future_min_delta = max_int;
            contained_in_min_delta_lit = false;
            _lit_occur->clear();
        }
    }
    // SASSERT(!overflow);
    return critical_subscore;
}

void ls_sampler::critical_move(uint64_t var_idx, __int128_t change_value) {
    int direction = (change_value > 0) ? 0 : 1;
    if (_vars[var_idx].is_lia) {
        critical_score_subscore(var_idx, change_value);  // 修改lia变量取值及对其他文字或子句的影响
        is_overflow = __builtin_add_overflow(_solution[var_idx], change_value, &_solution[var_idx]) || is_overflow;
        // SASSERT(!is_overflow);
    } else {
        int origin_score = _vars[var_idx].score;
        critical_score_subscore(var_idx);  // 修改bool变量取值及对其他文字或子句的影响
        _solution[var_idx] *= -1;          // flip
        _vars[var_idx].score = -origin_score;
    }

    // step
    if (_vars[var_idx].is_lia) {
        _last_move[2 * var_idx + direction] = _step;
        _tabulist[var_idx * 2 + (direction + 1) % 2] = _step + 3 + mt() % 10;
        if (CC_mode != -1) {
            modify_CC(var_idx, direction);
        }
    } else {
        _last_move[2 * var_idx] = _outer_layer_step;
        _tabulist[2 * var_idx] = _outer_layer_step + 1 + mt() % 3;
        if (CC_mode != -1) {
            modify_CC(var_idx, direction);
        }
        _outer_layer_step++;
    }
#if !defined(BAM_V2) && !defined(BAM_V1)
    if (_vars[var_idx].is_lia && _use_interval_move) {
        update_literals_sat_steps_count();  // 更新文字满足步数
    }
#endif
}

void ls_sampler::add_swap_operation(int& operation_idx) {
    int clause_idx = _sat_clause_with_false_literal->element_at(mt() % _sat_clause_with_false_literal->size());
    clause* cl = &(_clauses[clause_idx]);
    lit* l;
    int var_idx;
    __int128_t change_value = 0;
    for (int l_sign_idx : cl->lia_literals) {
        int l_idx = std::abs(l_sign_idx);
        l = &(_lits[l_idx]);
        if (l->is_equal) {
            // SASSERT(false);
            if (l->delta == 0 && l_sign_idx < 0) {
                for (int var_idx : l->pos_coff_var_idx) {
                    insert_operation(var_idx, 1, operation_idx, l_idx);
                    insert_operation(var_idx, -1, operation_idx, l_idx);
                }
                for (int var_idx : l->neg_coff_var_idx) {
                    insert_operation(var_idx, 1, operation_idx, l_idx);
                    insert_operation(var_idx, -1, operation_idx, l_idx);
                }
            }  // delta should not be 0, while it is 0, so the var should increase 1/-1
            else if (l->delta != 0 && l_sign_idx > 0) {
                for (int j = 0; j < l->pos_coff.size(); j++) {
                    int var_idx = l->pos_coff_var_idx[j];
                    if ((l->delta % l->pos_coff[j]) != 0) {
                        continue;
                    }
                    insert_operation(var_idx, (-l->delta / l->pos_coff[j]), operation_idx, l_idx);
                }
                for (int j = 0; j < l->neg_coff.size(); j++) {
                    int var_idx = l->neg_coff_var_idx[j];
                    if ((l->delta % l->neg_coff[j]) != 0) {
                        continue;
                    }
                    insert_operation(var_idx, (l->delta / l->neg_coff[j]), operation_idx, l_idx);
                }
            }  // delta should be 0, while it is not 0, so the var should increase (-delta/coff), while (-delta%coff)==0
        } else if ((l->delta > 0 && l_sign_idx > 0) || (l->delta <= 0 && l_sign_idx < 0)) {  // determine a false literal
            for (int i = 0; i < l->neg_coff.size(); i++) {
                var_idx = l->neg_coff_var_idx[i];
                if (l_sign_idx > 0) {
                    change_value = devide(l->delta, l->neg_coff[i]);
                }  // delta should <=0, while it is now >0, it should enlarge by (-delta/-coff) pos
                else {
                    change_value = devide(l->delta - 1, l->neg_coff[i]);
                }  // delta should >=1, while it is now <=0, it should enlarge by (1-delta/-coff) neg
                insert_operation(var_idx, change_value, operation_idx, l_idx);
            }
            for (int i = 0; i < l->pos_coff.size(); i++) {
                var_idx = l->pos_coff_var_idx[i];
                if (l_sign_idx > 0) {
                    change_value = devide(-l->delta, l->pos_coff[i]);
                }  // delta should <=0, while it is now >0, it should enlarge by (-delta/coff) neg
                else {
                    change_value = devide(1 - l->delta, l->pos_coff[i]);
                }  // delta should >=1, while it is now <=0, it should enlarge by (1-delta/coff) pos

                insert_operation(var_idx, change_value, operation_idx, l_idx);  // do not consider tabu here
            }
        }
    }
}

// choose a clause with small weight, then choose a random lit, select the operation with greatest score in the lit
void ls_sampler::swap_from_small_weight_clause() {
    uint64_t min_weight = UINT64_MAX;
    uint64_t min_weight_clause_idx = 0;
    __int128_t best_score = INT32_MIN;
    __int128_t best_operation_var = 0;
    __int128_t best_operation_value = 0;
    __int128_t score;
    __int128_t value;
    for (int i = 0; i < 45; i++) {
        int clause_idx = _sat_clause_with_false_literal->element_at(mt() % _sat_clause_with_false_literal->size());
        if (_clauses[clause_idx].weight < min_weight) {
            min_weight = _clauses[clause_idx].weight;
            min_weight_clause_idx = clause_idx;
        }
    }
    clause* cl = &(_clauses[min_weight_clause_idx]);
    for (int lit_sign : cl->literals) {
        lit* l = &(_lits[std::abs(lit_sign)]);
        __int128_t pos_delta = l->delta;
        convert_to_pos_delta(pos_delta, lit_sign);
        if (pos_delta > 0) {  // determine a false literal
            if (l->is_equal) {
                if (l->delta == 0 && lit_sign < 0) {
                    for (int var_idx : l->pos_coff_var_idx) {
                        if (_solution[var_idx] + 1 <= _vars[var_idx].upper_bound && _solution[var_idx] + 1 >= _vars[var_idx].low_bound) {
                            score = critical_score(var_idx, 1);
                            if (score > best_score) {
                                best_score = score;
                                best_operation_var = var_idx;
                                best_operation_value = 1;
                            }
                        }
                        if (_solution[var_idx] - 1 <= _vars[var_idx].upper_bound && _solution[var_idx] - 1 >= _vars[var_idx].low_bound) {
                            score = critical_score(var_idx, -1);
                            if (score > best_score) {
                                best_score = score;
                                best_operation_var = var_idx;
                                best_operation_value = -1;
                            }
                        }
                    }
                    for (int var_idx : l->neg_coff_var_idx) {
                        if (_solution[var_idx] + 1 <= _vars[var_idx].upper_bound && _solution[var_idx] + 1 >= _vars[var_idx].low_bound) {
                            score = critical_score(var_idx, 1);
                            if (score > best_score) {
                                best_score = score;
                                best_operation_var = var_idx;
                                best_operation_value = 1;
                            }
                        }
                        if (_solution[var_idx] - 1 <= _vars[var_idx].upper_bound && _solution[var_idx] - 1 >= _vars[var_idx].low_bound) {
                            score = critical_score(var_idx, -1);
                            if (score > best_score) {
                                best_score = score;
                                best_operation_var = var_idx;
                                best_operation_value = -1;
                            }
                        }
                    }
                }  // delta should not be 0, while it is 0, so the var should increase 1/-1
                else if (l->delta != 0 && lit_sign > 0) {
                    for (int j = 0; j < l->pos_coff.size(); j++) {
                        int var_idx = l->pos_coff_var_idx[j];
                        if ((l->delta % l->pos_coff[j]) != 0) {
                            continue;
                        }
                        value = (-l->delta / l->pos_coff[j]);
                        if (_solution[var_idx] + value <= _vars[var_idx].upper_bound && _solution[var_idx] + value >= _vars[var_idx].low_bound) {
                            score = critical_score(var_idx, value);
                            if (score > best_score) {
                                best_score = score;
                                best_operation_var = var_idx;
                                best_operation_value = value;
                            }
                        }
                    }
                    for (int j = 0; j < l->neg_coff.size(); j++) {
                        int var_idx = l->neg_coff_var_idx[j];
                        if ((l->delta % l->neg_coff[j]) != 0) {
                            continue;
                        }
                        value = (l->delta / l->neg_coff[j]);
                        if (_solution[var_idx] + value <= _vars[var_idx].upper_bound && _solution[var_idx] + value >= _vars[var_idx].low_bound) {
                            score = critical_score(var_idx, value);
                            if (score > best_score) {
                                best_score = score;
                                best_operation_var = var_idx;
                                best_operation_value = value;
                            }
                        }
                    }
                }  // delta should be 0, while it is not 0, so the var should increase (-delta/coff), while (-delta%coff)==0
                critical_move(best_operation_var, best_operation_value);
            }  // equal lit
            else if (l->is_lia_lit) {
                for (int i = 0; i < l->neg_coff.size(); i++) {
                    int var_idx = l->neg_coff_var_idx[i];
                    if (lit_sign > 0) {
                        value = devide(l->delta, l->neg_coff[i]);
                    }  // delta should <=0, while it is now >0, it should enlarge by (-delta/-coff) pos
                    else {
                        value = devide(l->delta - 1, l->neg_coff[i]);
                    }  // delta should >=1, while it is now <=0, it should enlarge by (1-delta/-coff) neg
                    if (_solution[var_idx] + value <= _vars[var_idx].upper_bound && _solution[var_idx] + value >= _vars[var_idx].low_bound) {
                        score = critical_score(var_idx, value);
                        if (score > best_score) {
                            best_score = score;
                            best_operation_var = var_idx;
                            best_operation_value = value;
                        }
                    }
                }
                for (int i = 0; i < l->pos_coff.size(); i++) {
                    int var_idx = l->pos_coff_var_idx[i];
                    if (lit_sign > 0) {
                        value = devide(-l->delta, l->pos_coff[i]);
                    }  // delta should <=0, while it is now >0, it should enlarge by (-delta/coff) neg
                    else {
                        value = devide(1 - l->delta, l->pos_coff[i]);
                    }  // delta should >=1, while it is now <=0, it should enlarge by (1-delta/coff) pos
                    if (_solution[var_idx] + value <= _vars[var_idx].upper_bound && _solution[var_idx] + value >= _vars[var_idx].low_bound) {
                        score = critical_score(var_idx, value);
                        if (score > best_score) {
                            best_score = score;
                            best_operation_var = var_idx;
                            best_operation_value = value;
                        }
                    }  // do not consider tabu here
                }
                critical_move(best_operation_var, best_operation_value);
            }  // a-b+k<=0
            else {
                critical_move(l->delta, 0);
            }  // a boolean operation
            break;
        }
    }
}

bool ls_sampler::check_solution() {
    clause* cp;
    int unsat_num = 0;
    for (uint64_t i = 0; i < _num_clauses; i++) {
        int sat_count = 0;
        cp = &(_clauses[i]);
        for (int lit_idx : cp->literals) {
            __int128_t delta = delta_lit(_lits[std::abs(lit_idx)]);
            bool is_equal = _lits[std::abs(lit_idx)].is_equal;
            if (!_lits[std::abs(lit_idx)].is_lia_lit) {
                __int128_t var_idx = _lits[std::abs(lit_idx)].delta;
                if ((_solution[var_idx] > 0 && lit_idx > 0) || (_solution[var_idx] < 0 && lit_idx < 0)) {
                    sat_count++;
                }
            } else if ((!is_equal && ((delta <= 0 && lit_idx > 0) || (delta > 0 && lit_idx < 0))) || (is_equal && ((delta == 0 && lit_idx > 0) || (delta != 0 && lit_idx < 0)))) {
                sat_count++;
            }
        }
        if (sat_count != cp->sat_count) {
            std::cout << "sat count wrong at clause " << i << "\n";
        }
        if (sat_count == 0) {
            unsat_num++;
        }
    }
#ifdef VERBOSE&& DEBUG

    for (int var_idx = 0; var_idx < _vars.size(); var_idx++) {
        if (_solution[var_idx] > _vars[var_idx].upper_bound || _solution[var_idx] < _vars[var_idx].low_bound) {
            std::cout << "var " << var_idx << " out of range\n";
            std::cout << "_solution[var_idx] = " << print_128(_solution[var_idx]) << "\n";
            std::cout << "_vars[var_idx].upper_bound = " << print_128(_vars[var_idx].upper_bound) << "\n";
            std::cout << "_vars[var_idx].low_bound = " << print_128(_vars[var_idx].low_bound) << "\n";
            std::cout << "_vars[var_idx].s_upper_bound = " << print_128(_vars[var_idx].s_upper_bound) << "\n";
            std::cout << "_vars[var_idx].s_lower_bound = " << print_128(_vars[var_idx].s_lower_bound) << "\n";
        }
    }

    if (unsat_num == _unsat_clauses->size()) {
        std::cout << "unsat_num = " << unsat_num << "\n";
        std::cout << "right solution\n";
    } else {
        std::cout << "wrong solution\n";
        for (int var_idx = 0; var_idx < _vars.size(); var_idx++) {
            if (_solution[var_idx] > _vars[var_idx].upper_bound || _solution[var_idx] < _vars[var_idx].low_bound) {
                std::cout << "var " << var_idx << ": " << _vars[var_idx].var_name << " out of range\n";
                std::cout << "lower: " << print_128(_vars[var_idx].low_bound) << "\n";
                std::cout << "upper: " << print_128(_vars[var_idx].upper_bound) << "\n";
                std::cout << "value: " << print_128(_solution[var_idx]) << "\n";
            }
        }
    }
#endif
    return unsat_num == _unsat_clauses->size();
}

// return the upper round of (a/b): (-3.5)->-4; (3.5)->4
__int128_t ls_sampler::devide(__int128_t a, __int128_t b) {
    SASSERT(b != 0);
    __int128_t up_round = (abs_128(a)) / (b);
    if (abs_128(a) % b > 0) {
        up_round++;
    }
    return a > 0 ? up_round : -up_round;
}

void ls_sampler::print_var_solution(std::string& var_name, std::string& var_value) {
    uint64_t var_idx = 0;

    if (_name2tmp_var.find(var_name) == _name2tmp_var.end()) {
        if (_name2var.find(var_name) != _name2var.end()) {
            var_idx = _name2var[var_name];
            var_value = print_128(_solution[var_idx]);
        }  // the boolean var exists in _vars
        else {
            var_value = _resolution_vars[_name2resolution_var[var_name]].up_bool > 0 ? "1" : "-1";  // mybe random ?
        }  // the boolean does not exists in _vars
        return;
    }  // Bool case: since the Bool var will directly enter resolution var
    // LIA case follows
    int origin_var_idx = (int)_name2tmp_var[var_name];
    if (pair_x->is_in_array(origin_var_idx)) {  // x-y=x case x
        var_value = print_128(pair_x_value[pair_x->index_of(origin_var_idx)]);
        return;
    } else if (pair_y->is_in_array(origin_var_idx)) {  // x-y=z case y
        var_value = print_128(pair_y_value[pair_y->index_of(origin_var_idx)]);
        return;
    } else if (_name2var.find(var_name) != _name2var.end()) {
        var_idx = _name2var[var_name];
        var_value = print_128(_solution[var_idx]);
        return;
    }  // the var exists in _vars
    else {
        // __int128_t random_val = random_int64_in_range(_tmp_vars[origin_var_idx].lower_bound, _tmp_vars[origin_var_idx].upper_bound);
        __int128_t random_val = _tmp_vars[origin_var_idx].low_bound;
        SASSERT(_tmp_vars[origin_var_idx].low_bound <= random_val && random_val <= _tmp_vars[origin_var_idx].upper_bound);
        var_value = print_128(random_val);
        return;
    }  // the var does not exist in reduced formula
}

void ls_sampler::print_move_status(std::ostream& out, int v_idx, __int128_t change_val) {
    out << "status:\n";
    int unsat_cluase_num = _unsat_clauses->size();
    out << "unsat clause num: " << unsat_cluase_num << "\n";
    out << "unsat clauses:\n";
    for (int i = 0; i < unsat_cluase_num; ++i) {
        out << _unsat_clauses->element_at(i) << " ";
    }
    out
        << "\n";
    out << "var: " << _vars[v_idx].var_name << "; ";
    out << "change_val: " << print_128(change_val) << "\n";
}

void ls_sampler::print_vars(std::ostream& out) {
    out << "print vars:\n";
    for (int i = 0; i < _num_vars; ++i) {
        variable* v = &_vars[i];
        out << v->var_name << " = " << print_128(_solution[i]) << "; ";
    }
}

void ls_sampler::print_interal_data_strcture(std::ostream& out) {
    out << "interal_data_strctures:\n";
    out << "cls:\n";
    for (int i = 0; i < _clauses.size(); ++i) {
        out << "cls " << i << ": {";
        for (int j = 0; j < _clauses[i].lia_literals.size(); ++j) {
            if (j != 0) {
                out << ", " << _clauses[i].lia_literals[j];
            } else {
                out << _clauses[i].lia_literals[j];
            }
        }
        out << "}\n";
    }
    out << "_lits:\n";
    for (int i = 0; i < _lits.size(); ++i) {
        if (_lits[i].lits_index == 0)
            continue;
        print_literal(out, _lits[i]);
    }
    out << "\n";
    SASSERT(_num_vars == _vars.size());
    out << "_vars: " << _num_vars << "\n";
    for (int i = 0; i < _num_vars; ++i) {
        out << "(" << _vars[i].var_name << ":" << i << "); ";
    }
    out << "\n";
    out << "_tmp_vars: " << _tmp_vars.size() << "\n";
    for (int i = 0; i < _tmp_vars.size(); ++i) {
        out << "(" << _tmp_vars[i].var_name << ":" << i << "); ";
    }
    out << "\n";
    out << "_resolution_vars: " << _resolution_vars.size() << "\n";
    for (int i = 0; i < _resolution_vars.size(); ++i) {
        out << "(" << _resolution_vars[i].var_name << ":" << i << "); ";
    }
    out << "\n";
    out << "_name2resolution_var:\n";
    for (auto v : _name2resolution_var) {
        out << "(" << v.first << ":" << v.second << "); ";
    }
    out << "\n";
    out << "_name2var:\n";
    for (auto v : _name2var) {
        out << "(" << v.first << ":" << v.second << "); ";
    }
    out << "\n";
    out << "_name2tmp_var:\n";
    for (auto v : _name2var) {
        out << "(" << v.first << ":" << v.second << "); ";
    }
}

std::string ls_sampler::print_128(__int128_t n) {
    std::stringstream ss;
    if (n == 0)
        return "0";
    if (n < 0) {
        ss << "-";
        n = -n;
    }
    int a[50], ai = 0;
    memset(a, 0, sizeof a);
    while (n != 0) {
        a[ai++] = n % 10;
        n /= 10;
    }
    for (int i = 1; i <= ai; i++)
        ss << abs(a[ai - i]);
    return ss.str();
}

void ls_sampler::print_literal(std::ostream& out, lit& l) {
    out << l.lits_index << ": ";
    if (!l.is_lia_lit) {
        out << _vars[l.delta].var_name << "\n";
    } else {
        // for (int i = 0; i < l.pos_coff.size(); i++) {
        //     out << "( " << print_128(l.pos_coff[i]) << " * " << _vars[l.pos_coff_var_idx[i]].var_name << " ) + ";
        // }
        // for (int i = 0; i < l.neg_coff.size(); i++) {
        //     out << "( -" << print_128(l.neg_coff[i]) << " * " << _vars[l.neg_coff_var_idx[i]].var_name << " ) + ";
        // }
        for (int i = 0; i < l.pos_coff.size(); i++) {
            out << "( " << print_128(l.pos_coff[i]) << " * " << print_128(_solution[l.pos_coff_var_idx[i]]) << " ) + ";
        }
        for (int i = 0; i < l.neg_coff.size(); i++) {
            out << "( -" << print_128(l.neg_coff[i]) << " * " << print_128(_solution[l.neg_coff_var_idx[i]]) << " ) + ";
        }
        out << "( " << print_128(l.key) << " ) " << (l.is_equal ? "==" : "<=") << " 0\n";
    }
}

void ls_sampler::print_formula(std::ostream& out) {
    for (int i = 0; i < _num_clauses; i++) {
        clause* cl = &(_clauses[i]);
        out << i << "\n";
        for (int l_idx : cl->literals) {
            if (l_idx < 0) {
                out << "neg: ";
            }
            print_literal(out, _lits[std::abs(l_idx)]);
        }
        out << "\n";
    }
}

void ls_sampler::print_result() {
    std::cout << "--------------------- result ---------------------\n";
    std::cout << "total time: " << TimeElapsed_total() << std::endl;
    std::cout << "random seed: " << _random_seed << "\n";
}

}  // namespace sampler