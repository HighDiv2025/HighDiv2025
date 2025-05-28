#include "sampler.h"

namespace sampler {

void Sampler::show_progress_bar(int current, int total) {
    int bar_width = 50;  // 进度条的宽度
    float progress = (float)current / total;
    int pos = bar_width * progress;

    // 清除当前行内容
    std::cout << "\r[";  // 确保从行首开始输出进度条
    for (int i = 0; i < bar_width; ++i) {
        if (i < pos) {
            std::cout << "#";
        } else {
            std::cout << " ";
        }
    }
    std::cout << "] " << int(progress * 100.0) << "%";

    std::cout.flush();  // 强制刷新输出
}

void Sampler::safe_exit(int exitcode) {
    if (exitcode) {
        result = "failure";
    } else {
        result = "success";
    }
    exit(exitcode);
}

void Sampler::_compute_formula_stats_aux(z3::expr e, int depth) {
    if (sup.find(e) != sup.end())
        return;                                            // 若该公式已被解析过，直接返回
    assert(e.is_app());                                    // 确保该表达式是一个函数应用
    z3::func_decl fd = e.decl();                           // 获取表达式对应的函数声明
    if (e.is_const()) {                                    // 若表达式是一个常量
        std::string name = fd.name().str();                // 获取变量名
        if (var_names.find(name) == var_names.end()) {     // 若该变量未被访问过
            var_names.insert(name);                        // 记录变量名称
            variables.push_back(fd);                       // 记录变量的函数声明
            variable_names.push_back(name);                // 记录变量名称（用于输出模型）
            if (fd.range().is_array()) {                   // 若该函数声明为数组
                ++num_arrays;                              // 统计数组数量
            } else if (fd.is_const()) {                    // 若函数声明为零元函数
                switch (fd.range().sort_kind()) {          // 进一步判断常量类型
                    case Z3_BV_SORT:                       // 若为位向量常量
                        ++num_bv;                          // 统计位向量常量数
                        num_bits += fd.range().bv_size();  // 统计公式中所有位向量的位宽之和
                        break;
                    case Z3_BOOL_SORT:  // 若为布尔常量
                        ++num_bools;    // 统计布尔常量数
                        ++num_bits;     // 将布尔常量作为位宽为 1 的位向量统计位宽
                        break;
                    case Z3_INT_SORT:  // 若为整数常量
                        ++num_ints;    // 统计整数常量数
                        break;
                    case Z3_REAL_SORT:  // 若为实数常量
                        ++num_reals;    // 统计实数常量数
                        break;
                    default:
                        std::cout << "Invalid sort\n";
                        safe_exit(1);
                }
            }
        }
    } else if (fd.decl_kind() == Z3_OP_UNINTERPRETED) {  // 若为未解释函数
        std::string name = fd.name().str();              // 获取函数名
        if (var_names.find(name) == var_names.end()) {
            var_names.insert(name);
            // std::cout << "declaration: " << fd << '\n';
            variables.push_back(fd);
            ++num_uf;
        }
    }
    sup.insert(e);
    if (depth > max_depth) {
        max_depth = depth;
    }
    for (size_t i = 0; i < e.num_args(); ++i) {
        _compute_formula_stats_aux(e.arg(i), depth + 1);
    }
}

void Sampler::parseSmtFile() {
    z3::expr_vector formulas = c.parse_file(smtFilePath.c_str());
    original_formula = mk_and(formulas);

#ifdef DEBUG
    _compute_formula_stats_aux(original_formula);
    std::cout << "AST depth: " << max_depth << std::endl;
#endif
}
};