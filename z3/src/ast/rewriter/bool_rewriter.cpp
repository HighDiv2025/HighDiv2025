/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bool_rewriter.h

Abstract:

    Basic rewrites for Boolean operators.

Author:

    Leonardo (leonardo) 2011-04-04

Notes:

--*/
#include "ast/rewriter/bool_rewriter.h"
#include "params/bool_rewriter_params.hpp"
#include "ast/rewriter/rewriter_def.h"
#include "ast/ast_lt.h"
#include "ast/for_each_expr.h"
#include <algorithm>

void bool_rewriter::updt_params(params_ref const & _p) {
    bool_rewriter_params p(_p);
    m_flat_and_or          = p.flat_and_or();
    m_sort_disjunctions    = p.sort_disjunctions();
    m_elim_and             = p.elim_and();
    m_elim_ite             = p.elim_ite();
    m_local_ctx            = p.local_ctx();
    m_local_ctx_limit      = p.local_ctx_limit();
    m_blast_distinct       = p.blast_distinct();
    m_blast_distinct_threshold = p.blast_distinct_threshold();
    m_ite_extra_rules      = p.ite_extra_rules();
}

void bool_rewriter::get_param_descrs(param_descrs & r) {
    bool_rewriter_params::collect_param_descrs(r);
}

br_status bool_rewriter::mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(f->get_family_id() == m().get_basic_family_id());
    switch (f->get_decl_kind()) {
    case OP_EQ:
        SASSERT(num_args == 2);
        return mk_eq_core(args[0], args[1], result);
    case OP_DISTINCT:
        return mk_distinct_core(num_args, args, result);
    case OP_AND:
        return mk_and_core(num_args, args, result);
    case OP_OR:
        return mk_or_core(num_args, args, result);
    case OP_NOT:
        SASSERT(num_args == 1);
        return mk_not_core(args[0], result);
    case OP_ITE:
        SASSERT(num_args == 3);
        return mk_ite_core(args[0], args[1], args[2], result);
    case OP_IMPLIES:
        SASSERT(num_args == 2);
        mk_implies(args[0], args[1], result);
        return BR_DONE;
    case OP_XOR:
        switch (num_args) {
        case 0: result = m().mk_false(); return BR_DONE;
        case 1: result = args[0]; return BR_DONE;
        case 2: mk_xor(args[0], args[1], result); return BR_DONE;
        default: UNREACHABLE(); return BR_FAILED;
        }
    default:
        return BR_FAILED;
    }
}

void bool_rewriter::mk_and_as_or(unsigned num_args, expr * const * args, expr_ref & result) {
    expr_ref_buffer new_args(m());
    for (unsigned i = 0; i < num_args; i++) {
        expr_ref tmp(m());
        mk_not(args[i], tmp);
        new_args.push_back(tmp);
    }
    expr_ref tmp(m());
    mk_or(new_args.size(), new_args.data(), tmp);
    mk_not(tmp, result);
}

br_status bool_rewriter::mk_nflat_and_core(unsigned num_args, expr * const * args, expr_ref & result) {
    bool s = false;
    ptr_buffer<expr> buffer;
    expr_fast_mark1 neg_lits;
    expr_fast_mark2 pos_lits;
    expr* atom = nullptr;

    for (unsigned i = 0; i < num_args; i++) {
        expr * arg  = args[i];
        if (m().is_true(arg)) {
            s = true;
            continue;
        }
        if (m().is_false(arg)) {
            neg_lits.reset();
            pos_lits.reset();
            result = m().mk_false();
            return BR_DONE;
        }
        if (m().is_not(arg, atom)) {
            if (neg_lits.is_marked(atom)) {
                s = true;
                continue;
            }
            if (pos_lits.is_marked(atom)) {
                neg_lits.reset();
                pos_lits.reset();
                result = m().mk_false();
                return BR_DONE;
            }
            neg_lits.mark(atom);
        }
        else {
            if (pos_lits.is_marked(arg)) {
                s = true;
                continue;
            }
            if (neg_lits.is_marked(arg)) {
                neg_lits.reset();
                pos_lits.reset();
                result = m().mk_false();
                return BR_DONE;
            }
            pos_lits.mark(arg);
        }
        buffer.push_back(arg);
    }
    neg_lits.reset();
    pos_lits.reset();

    unsigned sz = buffer.size();

    switch (sz) {
    case 0:
        result = m().mk_true();
        return BR_DONE;
    case 1:
        result = buffer.back();
        return BR_DONE;
    default:
        if (s) {
            result = m().mk_and(buffer);
            return BR_DONE;
        }
        return BR_FAILED;
    }
}

br_status bool_rewriter::mk_flat_and_core(unsigned num_args, expr * const * args, expr_ref & result) {
    unsigned i;
    for (i = 0; i < num_args; i++) {
        if (m().is_and(args[i]))
            break;
    }
    if (i < num_args) {
        // has nested ANDs
        ptr_buffer<expr> flat_args;
        flat_args.append(i, args);
        for (; i < num_args; i++) {
            expr * arg = args[i];
            // Remark: all rewrites are depth 1.
            if (m().is_and(arg)) {
                for (expr* e : *to_app(arg)) 
                    flat_args.push_back(e);
            }
            else {
                flat_args.push_back(arg);
            }
        }
        if (mk_nflat_and_core(flat_args.size(), flat_args.data(), result) == BR_FAILED)
            result = m().mk_and(flat_args);
        return BR_REWRITE1;
    }
    return mk_nflat_and_core(num_args, args, result);
}

br_status bool_rewriter::mk_nflat_or_core(unsigned num_args, expr * const * args, expr_ref & result) {
    bool s = false; // whether we have canceled some disjuncts or found some out or order
    ptr_buffer<expr> buffer;
    expr_fast_mark1 neg_lits;
    expr_fast_mark2 pos_lits;
    expr* prev = nullptr;
    for (unsigned i = 0; i < num_args; i++) {
        expr * arg  = args[i];
        if (m().is_true(arg)) {
            neg_lits.reset();
            pos_lits.reset();
            result = m().mk_true();
            return BR_DONE;
        }
        if (m().is_false(arg)) {
            s = true;
            continue;
        }
        expr* atom = nullptr;
        if (m().is_not(arg, atom)) {
            if (neg_lits.is_marked(atom)) {
                s = true;
                continue;
            }
            if (pos_lits.is_marked(atom)) {
                neg_lits.reset();
                pos_lits.reset();
                result = m().mk_true();
                return BR_DONE;
            }
            neg_lits.mark(atom);
        }
        else {
            if (pos_lits.is_marked(arg)) {
                s = true;
                continue;
            }
            if (neg_lits.is_marked(arg)) {
                neg_lits.reset();
                pos_lits.reset();
                result = m().mk_true();
                return BR_DONE;
            }
            pos_lits.mark(arg);
        }
        buffer.push_back(arg);
        s |= prev && lt(arg, prev);
        prev = arg;
    }

    neg_lits.reset();
    pos_lits.reset();


    unsigned sz = buffer.size();

    switch (sz) {
    case 0:
        result = m().mk_false();
        return BR_DONE;
    case 1:
        result = buffer.back();
        return BR_DONE;
    default:
#if 0
        // stupid or removal. A very special case of circuit optimization.
        expr* x, * y, * z, * u;
        auto is_complement = [&](expr* a, expr* b) {
            expr* c;
            if (m().is_not(a, c) && c == b)
                return true;
            if (m().is_not(b, c) && c == a)
                return true;
            return false;
        };

        if (sz == 2 && m().is_and(buffer[0], x, y) && m().is_and(buffer[1], z, u) && x == z && is_complement(y, u)) {
            result = x;
            return BR_DONE;
        }
#endif

        if (m_local_ctx && m_local_ctx_cost <= m_local_ctx_limit) {
            if (local_ctx_simp(sz, buffer.data(), result)) 
                return BR_DONE;
        }

        if (s) {
            if (m_sort_disjunctions) {
                ast_lt lt;
                std::stable_sort(buffer.begin(), buffer.end(), lt);
            }
            result = m().mk_or(sz, buffer.data());
            return BR_DONE;
        }
        return BR_FAILED;
    }
}


br_status bool_rewriter::mk_flat_or_core(unsigned num_args, expr * const * args, expr_ref & result) {
    unsigned i;
    for (i = 0; i < num_args; i++) {
        if (m().is_or(args[i]))
            break;
    }
    bool ordered = true;
    expr* prev = nullptr;
    if (i < num_args) {
        // has nested ORs
        ptr_buffer<expr> flat_args;
        flat_args.append(i, args);
        for (; i < num_args; i++) {
            expr * arg = args[i];
            // Remark: all rewrites are depth 1.
            if (m().is_or(arg)) {
                ordered = false;
                for (expr* e : *to_app(arg)) 
                    flat_args.push_back(e);
            }
            else {
                flat_args.push_back(arg);
                ordered &= (!prev || !lt(arg, prev));
                prev = arg;
            }
        }
        if (mk_nflat_or_core(flat_args.size(), flat_args.data(), result) == BR_FAILED) {
            if (m_sort_disjunctions && !ordered) {
                ast_lt lt;
                std::stable_sort(flat_args.begin(), flat_args.end(), lt);
            }
            result = mk_or_app(flat_args.size(), flat_args.data());
        }
        return BR_DONE;
    }
    return mk_nflat_or_core(num_args, args, result);
}

expr * bool_rewriter::mk_or_app(unsigned num_args, expr * const * args) {
    switch (num_args) {
    case 0: return m().mk_false();
    case 1: return args[0];
    default: return m().mk_or(num_args, args);
    }
}

/**
   \brief Auxiliary method for local_ctx_simp.

   Replace args[i] by true if marked in neg_lits.
   Replace args[i] by false if marked in pos_lits.
*/
bool bool_rewriter::simp_nested_not_or(unsigned num_args, expr * const * args,
                                       expr_fast_mark1 & neg_lits, expr_fast_mark2 & pos_lits, expr_ref & result) {
    ptr_buffer<expr> new_args;
    bool simp = false;
    m_local_ctx_cost += num_args;
    for (unsigned i = 0; i < num_args; i++) {
        expr * arg = args[i];
        if (neg_lits.is_marked(arg)) {
            result = m().mk_false();
            return true;
        }
        if (pos_lits.is_marked(arg)) {
            simp = true;
            continue;
        }
        if (m().is_not(arg)) {
            expr * atom = to_app(arg)->get_arg(0);
            if (neg_lits.is_marked(atom)) {
                simp = true;
                continue;
            }
            if (pos_lits.is_marked(atom)) {
                result = m().mk_false();
                return true;
            }
        }
        new_args.push_back(arg);
    }
    if (simp) {
        switch (new_args.size()) {
        case 0:
            result = m().mk_true();
            return true;
        case 1:
            mk_not(new_args[0], result);
            return true;
        default:
            result = m().mk_not(m().mk_or(new_args));
            return true;
        }
    }
    return false;
}


expr * bool_rewriter::simp_arg(expr * arg, expr_fast_mark1 & neg_lits, expr_fast_mark2 & pos_lits, bool & modified) {
    if (m().is_not(arg)) {
        expr * atom = to_app(arg)->get_arg(0);
        if (neg_lits.is_marked(atom)) {
            modified = true;
            return m().mk_false();
        }
        if (pos_lits.is_marked(atom)) {
            modified = true;
            return m().mk_true();
        }
        return arg;
    }
    else {
        if (neg_lits.is_marked(arg)) {
            modified = true;
            return m().mk_true();
        }
        if (pos_lits.is_marked(arg)) {
            modified = true;
            return m().mk_false();
        }
        return arg;
    }
}

/**
   \brief Simpler version of mk_ite, that will not invoke mk_or/mk_and.
   It is used byt local_ctx_simp to prevent a recursive call to local_ctx_simp.
   See comment at simp_nested_eq_ite.
*/
void bool_rewriter::mk_nested_ite(expr * c, expr * t, expr * e, expr_ref & result) {
    if (m().is_true(c)) {
        result = t;
        return;
    }

    if (m().is_false(c)) {
        result = e;
        return;
    }

    if (t == e) {
        result = t;
        return;
    }

    if (m().is_bool(t)) {
        if (m().is_true(t)) {
            if (m().is_false(e)) {
                result = c;
                return;
            }
            result = m().mk_or(c, e);
            return;
        }
        if (m().is_false(t)) {
            if (m().is_true(e)) {
                mk_not(c, result);
                return;
            }
            expr_ref tmp(m());
            mk_not(e, tmp);
            result = m().mk_not(m().mk_or(c, tmp));
            return;
        }
        if (m().is_true(e)) {
            expr_ref tmp(m());
            mk_not(c, tmp);
            result = m().mk_or(tmp, t);
            return;
        }
        if (m().is_false(e) || c == e) {
            expr_ref tmp1(m());
            expr_ref tmp2(m());
            mk_not(c, tmp1);
            mk_not(t, tmp2);
            result = m().mk_not(m().mk_or(tmp1, tmp2));
            return;
        }
        if (c == t) {
            result = m().mk_or(c, e);
            return;
        }
        if (m().is_complement_core(t, e)) { // t = not(e)
            mk_eq(c, t, result);
            return;
        }
        if (m().is_complement_core(e, t)) { // e = not(t)
            mk_eq(c, t, result);
            return;
        }
    }
    result = m().mk_ite(c, t, e);
}

bool bool_rewriter::simp_nested_eq_ite(expr * t, expr_fast_mark1 & neg_lits, expr_fast_mark2 & pos_lits, expr_ref & result) {
    bool neg = false;
    m_local_ctx_cost += 3;
    if (m().is_not(t)) {
        neg = true;
        t = to_app(t)->get_arg(0);
    }
    if (m().is_eq(t)) {
        bool modified = false;
        expr * new_lhs = simp_arg(to_app(t)->get_arg(0), neg_lits, pos_lits, modified);
        expr * new_rhs = simp_arg(to_app(t)->get_arg(1), neg_lits, pos_lits, modified);
        if (!modified)
            return false;
        mk_eq(new_lhs, new_rhs, result);
        if (neg)
            mk_not(result, result);
        return true;
    }
    if (m().is_ite(t)) {
        bool modified = false;
        expr * new_c = simp_arg(to_app(t)->get_arg(0), neg_lits, pos_lits, modified);
        expr * new_t = simp_arg(to_app(t)->get_arg(1), neg_lits, pos_lits, modified);
        expr * new_e = simp_arg(to_app(t)->get_arg(2), neg_lits, pos_lits, modified);
        if (!modified)
            return false;
        // It is not safe to invoke mk_ite here, since it can recursively call
        // local_ctx_simp by
        //     - transforming the ITE into an OR
        //     - and invoked mk_or, that will invoke local_ctx_simp
        // mk_ite(new_c, new_t, new_e, result);
        mk_nested_ite(new_c, new_t, new_e, result);
        if (neg)
            mk_not(result, result);
        return true;
    }
    return false;
}

void bool_rewriter::push_new_arg(expr* arg, expr_ref_vector& new_args, expr_fast_mark1& neg_lits, expr_fast_mark2& pos_lits) {
    expr* narg;
    if (m().is_not(arg, narg)) {
        if (!neg_lits.is_marked(narg)) {
            neg_lits.mark(narg);
            new_args.push_back(arg);
        }
    }
    else { 
        if (!pos_lits.is_marked(arg)) {
            pos_lits.mark(arg);            
            new_args.push_back(arg);
        }
    }
}

/**
   \brief Apply local context simplification at (OR args[0] ... args[num_args-1])
   Basic idea:
   - Replace args[i] by false in the other arguments
   - If args[i] is of the form (not t), then replace t by true in the other arguments.
   To make sure the simplification is efficient we bound the depth.
*/
bool bool_rewriter::local_ctx_simp(unsigned num_args, expr * const * args, expr_ref & result) {
    expr_ref_vector old_args(m());
    expr_ref_vector new_args(m());
    expr_ref        new_arg(m());
    expr_fast_mark1 neg_lits;
    expr_fast_mark2 pos_lits;
    bool simp     = false;
    bool modified = false;
    bool forward  = true;
    expr* narg;

    while (true) {

#define PROCESS_ARG()                                                                           \
        {                                                                                       \
            expr * arg = args[i];                                                               \
            if (m().is_not(arg, narg) && m().is_or(narg) &&                                     \
                simp_nested_not_or(to_app(narg)->get_num_args(),                                \
                                   to_app(narg)->get_args(),                                    \
                                   neg_lits,                                                    \
                                   pos_lits,                                                    \
                                   new_arg)) {                                                  \
                modified = true; simp = true;                                                   \
                arg = new_arg;                                                                  \
            }                                                                                   \
            if (simp_nested_eq_ite(arg, neg_lits, pos_lits, new_arg)) {                         \
                modified = true; simp = true;                                                   \
                 arg = new_arg;                                                                 \
            }                                                                                   \
            if (m().is_false(arg))                                                              \
                continue;                                                                       \
            if (m().is_true(arg)) {                                                             \
                result = arg;                                                                   \
                return true;                                                                    \
            }                                                                                   \
            if (m_flat_and_or && m().is_or(arg)) {                                              \
                for (expr * arg_arg : *to_app(arg)) {                                           \
                    push_new_arg(arg_arg, new_args, neg_lits, pos_lits);                        \
                }                                                                               \
            }                                                                                   \
            else {                                                                              \
                push_new_arg(arg, new_args, neg_lits, pos_lits);                                \
            }                                                                                   \
        }

        m_local_ctx_cost += 2*num_args;
#if 0
        static unsigned counter = 0;
        counter++;
        if (counter % 10000 == 0)
            verbose_stream() << "local-ctx-cost: " << m_local_ctx_cost << " " << num_args << "\n";
#endif

        if (forward) {
            for (unsigned i = 0; i < num_args; i++) {
                PROCESS_ARG();
            }
            forward = false;
        }
        else {
            unsigned i = num_args;
            while (i > 0) {
                --i;
                PROCESS_ARG();
            }
            if (!modified) {
                if (simp) {
                    result = mk_or_app(num_args, args);
                    return true;
                }
                return false; // didn't simplify
            }
            // preserve the original order...
            std::reverse(new_args.data(), new_args.data() + new_args.size());
            modified = false;
            forward  = true;
        }
        pos_lits.reset();
        neg_lits.reset();
        old_args.reset();
        old_args.swap(new_args);
        SASSERT(new_args.empty());
        args     = old_args.data();
        num_args = old_args.size();
    }
}

/**
   \brief Apply simplification if ite is an if-then-else tree where every leaf is a value.

   This is an efficient way to

*/
br_status bool_rewriter::try_ite_value(app * ite, app * val, expr_ref & result) {
    expr* cond = nullptr, *t = nullptr, *e = nullptr;
    VERIFY(m().is_ite(ite, cond, t, e));
    SASSERT(m().is_value(val));

    if (m().are_distinct(val, e)) {
        if (get_depth(t) < 500)
            mk_eq(t, val, result);
        else
            result = m().mk_eq(t, val);
        
        result = m().mk_and(result, cond);
        return BR_REWRITE2;
    }
    if (m().are_distinct(val, t)) {
        if (get_depth(e) < 500)
            mk_eq(e, val, result);
        else
            result = m().mk_eq(e, val);
        result = m().mk_and(result, m().mk_not(cond));
        return BR_REWRITE2;
    }
    if (m().are_equal(val, t)) {
        if (m().are_equal(val, e)) {
            result = m().mk_true();
            return BR_DONE;
        }
        else {
            mk_eq(e, val, result);
            result = m().mk_or(result, cond);
        }
        return BR_REWRITE2;
    }
    if (m().are_equal(val, e)) {
        mk_eq(t, val, result);
        result = m().mk_or(result, m().mk_not(cond));
        return BR_REWRITE2;
    }

    expr* cond2 = nullptr, *t2 = nullptr, *e2 = nullptr;
    if (m().is_ite(t, cond2, t2, e2) && m().is_value(t2) && m().is_value(e2) &&
        BR_FAILED != try_ite_value(to_app(t), val, result)) {
        result = m().mk_ite(cond, result, mk_eq_plain(e, val));
        return BR_REWRITE2;
    }
    if (m().is_ite(e, cond2, t2, e2) && m().is_value(t2) && m().is_value(e2) && 
        BR_FAILED != try_ite_value(to_app(e), val, result)) {
        result = m().mk_ite(cond, mk_eq_plain(t, val), result);
        return BR_REWRITE2;
    }

    return BR_FAILED;
}


app* bool_rewriter::mk_eq_plain(expr* lhs, expr* rhs) {
    if (m().are_equal(lhs, rhs))
        return m().mk_true();
    if (m().are_distinct(lhs, rhs))
        return m().mk_false();
    return m().mk_eq(lhs, rhs);
}

bool bool_rewriter::try_ite_eq(expr* lhs, expr* rhs, expr_ref& r) {
    expr* c, *t, *e;
    if (!m().is_ite(lhs, c, t, e))
        return false;
    if (m().are_equal(t, rhs) && m().are_distinct(e, rhs)) {
        r = c;
        return true;
    }
    if (m().are_equal(e, rhs) && m().are_distinct(t, rhs)) {
        r = m().mk_not(c);
        return true;
    }
    return false;
}


br_status bool_rewriter::mk_eq_core(expr * lhs, expr * rhs, expr_ref & result) {
    if (m().are_equal(lhs, rhs)) {
        result = m().mk_true();
        return BR_DONE;
    }

    if (m().are_distinct(lhs, rhs)) {
        result = m().mk_false();
        return BR_DONE;
    }

    br_status r = BR_FAILED;
    

    if (try_ite_eq(lhs, rhs, result))
        return BR_REWRITE1;

    if (try_ite_eq(rhs, lhs, result))
        return BR_REWRITE1;
    
    if (m_ite_extra_rules) {
        expr* c1, * t1, * e1;
        expr* c2, * t2, * e2;
        if (m().is_ite(lhs) && m().is_value(rhs)) {
            r = try_ite_value(to_app(lhs), to_app(rhs), result);
            CTRACE("try_ite_value", r != BR_FAILED,
                   tout << mk_bounded_pp(lhs, m()) << "\n" << mk_bounded_pp(rhs, m()) << "\n--->\n" << mk_bounded_pp(result, m()) << "\n";);
        }
        else if (m().is_ite(rhs) && m().is_value(lhs)) {
            r = try_ite_value(to_app(rhs), to_app(lhs), result);
            CTRACE("try_ite_value", r != BR_FAILED,
                   tout << mk_bounded_pp(lhs, m()) << "\n" << mk_bounded_pp(rhs, m()) << "\n--->\n" << mk_bounded_pp(result, m()) << "\n";);
        }
        else if (m().is_ite(lhs, c1, t1, e1) && m().is_ite(rhs, c2, t2, e2) &&
            m().is_value(t1) && m().is_value(e1) && m().is_value(t2) && m().is_value(e2)) {
            expr_ref_vector args(m());
            args.push_back(m().mk_or(c1, c2, m().mk_eq(e1, e2)));
            args.push_back(m().mk_or(m().mk_not(c1), m().mk_not(c2), m().mk_eq(t1, t2)));
            args.push_back(m().mk_or(m().mk_not(c1), c2, m().mk_eq(t1, e2)));
            args.push_back(m().mk_or(c1, m().mk_not(c2), m().mk_eq(e1, t2)));
            result = m().mk_and(args);
            return BR_REWRITE_FULL;
        }
        if (r != BR_FAILED)
            return r;
    }

    if (m().is_bool(lhs)) {
        bool unfolded = false;
        if (m().is_not(lhs) && m().is_not(rhs)) {
            lhs = to_app(lhs)->get_arg(0);
            rhs = to_app(rhs)->get_arg(0);
            unfolded = true;
        }
        if (m().is_true(lhs)) {
            result = rhs;
            return BR_DONE;
        }
        if (m().is_false(lhs)) {
            mk_not(rhs, result);
            return BR_DONE;
        }
        if (m().is_true(rhs)) {
            result = lhs;
            return BR_DONE;
        }
        if (m().is_false(rhs)) {
            mk_not(lhs, result);
            return BR_DONE;
        }
        if (m().is_complement(lhs, rhs)) {
            result = m().mk_false();
            return BR_DONE;
        }

        if (m().is_not(rhs))
            std::swap(lhs, rhs);
	
        if (m().is_not(lhs, lhs)) {
            result = m().mk_not(m().mk_eq(lhs, rhs));
            return BR_REWRITE2;
        }
	    
        if (unfolded) {
            result = m().mk_eq(lhs, rhs);
            return BR_REWRITE1;
        }

        expr *la, *lb, *ra, *rb;
        // fold (iff (iff a b) (iff (not a) b)) to false
        if (m().is_eq(lhs, la, lb) && m().is_eq(rhs, ra, rb)) {
            expr *n;
            if ((la == ra && ((m().is_not(rb, n) && n == lb) ||
                (m().is_not(lb, n) && n == rb))) ||
                (lb == rb && ((m().is_not(ra, n) && n == la) ||
                    (m().is_not(la, n) && n == ra)))) {
                result = m().mk_false();
                return BR_DONE;
            }
        }
    }
    if (m_order_eq && lhs->get_id() > rhs->get_id()) {
        result = m().mk_eq(rhs, lhs);
        return BR_DONE;
    }
    return BR_FAILED;
}

br_status bool_rewriter::mk_distinct_core(unsigned num_args, expr * const * args, expr_ref & result) {
    if (num_args <= 1) {
        result = m().mk_true();
        return BR_DONE;
    }

    if (num_args == 2) {
        expr_ref tmp(m());
        mk_eq(args[0], args[1], tmp);
        mk_not(tmp, result);
        return BR_REWRITE2; // mk_eq may be dispatched to other rewriters.
    }

    expr_fast_mark1 visited;
    bool all_value = true, all_diff = true;
    for (unsigned i = 0; i < num_args; i++) {
        expr * arg = args[i];
        if (visited.is_marked(arg)) {
            result = m().mk_false();
            return BR_DONE;
        }
        visited.mark(arg);
        if (!m().is_unique_value(arg))
            all_value = false;
        if (!all_value && all_diff) {
            for (unsigned j = 0; all_diff && j < i; ++j) {
                all_diff = m().are_distinct(arg, args[j]);
                if (!all_diff) { 
                    if (m().are_equal(arg, args[j])) {
                        result = m().mk_false();
                        return BR_DONE;
                    }
                }
            }
        }
    }
    if (all_diff) {
        result = m().mk_true();
        return BR_DONE;
    }

    SASSERT(num_args > 2);
    if (m().is_bool(args[0])) {
        result = m().mk_false();
        return BR_DONE;
    }

    if (m_blast_distinct && num_args < m_blast_distinct_threshold) {
        expr_ref_vector new_diseqs(m());
        for (unsigned i = 0; i < num_args; i++) {
            for (unsigned j = i + 1; j < num_args; j++)
                new_diseqs.push_back(m().mk_not(m().mk_eq(args[i], args[j])));
        }
        result = m().mk_and(new_diseqs);
        return BR_REWRITE3;
    }

    return BR_FAILED;
}

br_status bool_rewriter::mk_ite_core(expr * c, expr * t, expr * e, expr_ref & result) {
    bool s = false;

    // (ite (not c) a b) ==> (ite c b a)
    if (m().is_not(c)) {
        c = to_app(c)->get_arg(0);
        std::swap(t, e);
        s = true;
    }


    // (ite c (ite c t1 t2) t3)       ==> (ite c t1 t3
    if (m().is_ite(t) && to_app(t)->get_arg(0) == c) {
        // Remark: (ite c (ite (not c) t1 t2) t3) ==> (ite c t2 t3) does not happen if applying rewrites bottom up
        t = to_app(t)->get_arg(1);
        s = true;
    }
    // (ite c t1 (ite c2 t1 t2))      ==> (ite (or c c2) t1 t2)
    if (m().is_ite(e) && to_app(e)->get_arg(1) == t) {
        result = m().mk_ite(m().mk_or(c, to_app(e)->get_arg(0)), t, to_app(e)->get_arg(2));
        return BR_REWRITE3;
    }

    // (ite c t1 (ite c t2 t3))       ==> (ite c t1 t3)
    if (m().is_ite(e) && to_app(e)->get_arg(0) == c) {
        // Remark: (ite c t1 (ite (not c) t2 t3)) ==> (ite c t1 t2) does not happen if applying rewrites bottom up
        e = to_app(e)->get_arg(2);
        s = true;
    }

    if (m().is_true(c)) {
        result = t;
        return BR_DONE;
    }

    if (m().is_false(c)) {
        result = e;
        return BR_DONE;
    }

    if (t == e) {
        result = t;
        return BR_DONE;
    }

    if (m().is_bool(t)) {
        if (m().is_true(t)) {
            if (m().is_false(e)) {
                result = c;
                return BR_DONE;
            }
            if (m_elim_ite) {
                mk_or(c, e, result);
                return BR_DONE;
            }
        }
        if (m().is_false(t)) {
            if (m().is_true(e)) {
                mk_not(c, result);
                return BR_DONE;
            }
            if (m_elim_ite) {
                expr_ref tmp(m());
                mk_not(c, tmp);
                mk_and(tmp, e, result);
                return BR_REWRITE1;
            }
        }
        if (m().is_true(e) && m_elim_ite) {            
            expr_ref tmp(m());
            mk_not(c, tmp);
            mk_or(tmp, t, result);
            return BR_DONE;
        }
        if (m().is_false(e) && m_elim_ite) {
            mk_and(c, t, result);
            return BR_REWRITE1;
        }
        if (c == e && m_elim_ite) {
            mk_and(c, t, result);
            return BR_REWRITE1;
        }
        if (c == t && m_elim_ite) {
            mk_or(c, e, result);
            return BR_DONE;
        }
        if (m().is_complement_core(t, e) && m_elim_ite) { // t = not(e)
            mk_eq(c, t, result);
            return BR_DONE;
        }
        if (m().is_complement_core(e, t) && m_elim_ite) { // e = not(t)
            mk_eq(c, t, result);
            return BR_DONE;
        }
    }

#if 0
    // (ite c (not (= t1 t2)) t1) ==> (not (= t1 (and c t2)))
    if (m().is_not(t, t1) && m().is_eq(t1, t1, t2) && e == t1) {
        expr_ref a(m());
        mk_and(c, t2, a);
        result = mk_not(mk_eq(t1, a));
        return BR_REWRITE3;
    }
    if (m().is_not(t, t1) && m().is_eq(t1, t2, t1) && e == t1) {
        expr_ref a(m());
        mk_and(c, t2, a);
        result = mk_eq(t1, a);
        return BR_REWRITE3;
    }
#endif




    if (m().is_ite(t) && m_ite_extra_rules && m_elim_ite) {
        // (ite c1 (ite c2 t1 t2) t1) ==> (ite (and c1 (not c2)) t2 t1)
        if (e == to_app(t)->get_arg(1)) {
            expr_ref not_c2(m());
            mk_not(to_app(t)->get_arg(0), not_c2);
            expr_ref new_c(m());
            mk_and(c, not_c2, new_c);
            result = m().mk_ite(new_c, to_app(t)->get_arg(2), e);
            return BR_REWRITE2;
        }
        // (ite c1 (ite c2 t1 t2) t2) ==> (ite (and c1 c2) t1 t2)
        if (e == to_app(t)->get_arg(2)) {
            expr_ref new_c(m());
            mk_and(c, to_app(t)->get_arg(0), new_c);
            result = m().mk_ite(new_c, to_app(t)->get_arg(1), e);
            return BR_REWRITE2;
        }


        if (m().is_ite(e)) {
            // (ite c1 (ite c2 t1 t2) (ite c3 t1 t2)) ==> (ite (or (and c1 c2) (and (not c1) c3)) t1 t2)
            if (to_app(t)->get_arg(1) == to_app(e)->get_arg(1) &&
                to_app(t)->get_arg(2) == to_app(e)->get_arg(2)) {
                expr_ref and1(m());
                expr_ref and2(m());
                expr_ref notc(m());
                mk_and(c, to_app(t)->get_arg(0), and1);
                mk_not(c, notc);
                mk_and(notc, to_app(e)->get_arg(0), and2);
                expr_ref new_c(m());
                mk_or(and1, and2, new_c);
                result = m().mk_ite(new_c, to_app(t)->get_arg(1), to_app(t)->get_arg(2));
                return BR_REWRITE3;
            }

            // (ite c1 (ite c2 t1 t2) (ite c3 t2 t1)) ==> (ite (or (and c1 c2) (and (not c1) (not c3))) t1 t2)
            if (to_app(t)->get_arg(1) == to_app(e)->get_arg(2) &&
                to_app(t)->get_arg(2) == to_app(e)->get_arg(1)) {
                expr_ref and1(m());
                expr_ref and2(m());
                expr_ref notc(m());
                mk_and(c, to_app(t)->get_arg(0), and1);
                mk_not(c, notc);
                expr_ref notc3(m());
                mk_not(to_app(e)->get_arg(0), notc3);
                mk_and(notc, notc3, and2);
                expr_ref new_c(m());
                mk_or(and1, and2, new_c);
                result = m().mk_ite(new_c, to_app(t)->get_arg(1), to_app(t)->get_arg(2));
                return BR_REWRITE3;
            }
        }
    }

    if (m().is_ite(e) && m_ite_extra_rules && m_elim_ite) {
        // (ite c1 t1 (ite c2 t1 t2)) ==> (ite (or c1 c2)        t1 t2)
        if (t == to_app(e)->get_arg(1)) {
            expr_ref new_c(m());
            mk_or(c, to_app(e)->get_arg(0), new_c);
            result = m().mk_ite(new_c, t, to_app(e)->get_arg(2));
            return BR_REWRITE1;
        }
        // (ite c1 t1 (ite c2 t2 t1)) ==> (ite (or c1 (not c2))  t1 t2)
        if (t == to_app(e)->get_arg(2)) {
            expr_ref not_c2(m());
            mk_not(to_app(e)->get_arg(0), not_c2);
            expr_ref new_c(m());
            mk_or(c, not_c2, new_c);
            result = m().mk_ite(new_c, t, to_app(e)->get_arg(1));
            return BR_REWRITE1;
        }
    }

    if (s) {
        result = m().mk_ite(c, t, e);
        return BR_DONE;
    }

    return BR_FAILED;
}

br_status bool_rewriter::mk_not_core(expr * t, expr_ref & result) {
    if (m().is_not(t)) {
        result = to_app(t)->get_arg(0);
        return BR_DONE;
    }
    if (m().is_true(t)) {
        result = m().mk_false();
        return BR_DONE;
    }
    if (m().is_false(t)) {
        result = m().mk_true();
        return BR_DONE;
    }
    if (is_eq(t) && m().is_bool(to_app(t)->get_arg(0))) {
        expr_ref tmp(m());
        mk_not(to_app(t)->get_arg(0), tmp);
        mk_eq(tmp, to_app(t)->get_arg(1), result);
        return BR_DONE;
    }
    return BR_FAILED;
}

void bool_rewriter::mk_xor(expr * lhs, expr * rhs, expr_ref & result) {
    expr_ref tmp(m());
    mk_not(lhs, tmp);
    mk_eq(tmp, rhs, result);
}

void bool_rewriter::mk_implies(expr * lhs, expr * rhs, expr_ref & result) {
    expr_ref tmp(m());
    mk_not(lhs, tmp);
    mk_or(tmp, rhs, result);
}

void bool_rewriter::mk_nand(unsigned num_args, expr * const * args, expr_ref & result) {
    expr_ref tmp(m_manager);
    mk_and(num_args, args, tmp);
    mk_not(tmp, result);
}

void bool_rewriter::mk_nor(unsigned num_args, expr * const * args, expr_ref & result) {
    expr_ref tmp(m_manager);
    mk_or(num_args, args, tmp);
    mk_not(tmp, result);
}

void bool_rewriter::mk_nand(expr * arg1, expr * arg2, expr_ref & result) {
    expr_ref tmp(m_manager);
    mk_and(arg1, arg2, tmp);
    mk_not(tmp, result);
}

void bool_rewriter::mk_nor(expr * arg1, expr * arg2, expr_ref & result) {
    expr_ref tmp(m_manager);
    mk_or(arg1, arg2, tmp);
    mk_not(tmp, result);
}


void bool_rewriter::mk_ge2(expr* a, expr* b, expr* c, expr_ref& r) {
    if (m().is_false(a)) mk_and(b, c, r);
    else if (m().is_false(b)) mk_and(a, c, r);
    else if (m().is_false(c)) mk_and(a, b, r);
    else if (m().is_true(a)) mk_or(b, c, r);
    else if (m().is_true(b)) mk_or(a, c, r);
    else if (m().is_true(c)) mk_or(a, b, r);
    else {
        expr_ref i1(m()), i2(m()), i3(m());
        mk_and(a, b, i1);
        mk_and(a, c, i2);
        mk_and(b, c, i3);
        mk_or(i1, i2, i3, r);
    }
}


template class rewriter_tpl<bool_rewriter_cfg>;
