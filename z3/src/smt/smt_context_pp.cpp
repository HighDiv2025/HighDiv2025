/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_context_pp.cpp

Abstract:

    SMT logical context: pretty printing

Author:

    Leonardo de Moura (leonardo) 2008-02-21.

Revision History:

--*/
#include "smt/smt_context.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/ast_pp_util.h"
#include "util/stats.h"
#ifndef SINGLE_THREAD
#include <thread>
#endif

namespace smt {

std::ostream& context::display_last_failure(std::ostream& out) const {
    switch (m_last_search_failure) {
        case OK:
            return out << "OK";
        case UNKNOWN:
            return out << "UNKNOWN";
        case MEMOUT:
            return out << "MEMOUT";
        case CANCELED:
            return out << "CANCELED";
        case NUM_CONFLICTS:
            return out << "NUM_CONFLICTS";
        case RESOURCE_LIMIT:
            return out << "RESOURCE_LIMIT";
        case THEORY:
            if (!m_incomplete_theories.empty()) {
                bool first = true;
                for (theory* th : m_incomplete_theories) {
                    if (first)
                        first = false;
                    else
                        out << " ";
                    out << th->get_name();
                }
            } else {
                out << "THEORY";
            }
            return out;
        case QUANTIFIERS:
            return out << "QUANTIFIERS";
        case LAMBDAS:
            return out << "LAMBDAS";
    }
    UNREACHABLE();
    return out << "?";
}

std::string context::last_failure_as_string() const {
    std::string r;
    switch (m_last_search_failure) {
        case UNKNOWN:
        case OK:
            r = m_unknown;
            break;
        case MEMOUT:
            r = "memout";
            break;
        case CANCELED:
            r = "canceled";
            break;
        case NUM_CONFLICTS:
            r = "max-conflicts-reached";
            break;
        case THEORY: {
            r = "(incomplete (theory";
            for (theory* t : m_incomplete_theories) {
                r += " ";
                r += t->get_name();
            }
            r += "))";
            break;
        }
        case RESOURCE_LIMIT:
            r = "(resource limits reached)";
            break;
        case QUANTIFIERS:
            r = "(incomplete quantifiers)";
            break;
        case LAMBDAS:
            r = "(incomplete lambdas)";
            break;
    }
    return r;
}

void context::display_asserted_formulas(std::ostream& out) const {
    m_asserted_formulas.display_ll(out, get_pp_visited());
}

std::ostream& context::display_literal(std::ostream& out, literal l) const {
    smt::display_compact(out, l, m_bool_var2expr.data());
    return out;
}

std::ostream& context::display_literals(std::ostream& out, unsigned num_lits, literal const* lits) const {
    display_compact(out, num_lits, lits, m_bool_var2expr.data());
    return out;
}

std::ostream& context::display_literal_verbose(std::ostream& out, literal lit) const {
    return display_literals_verbose(out, 1, &lit);
}

std::ostream& context::display_literals_verbose(std::ostream& out, unsigned num_lits, literal const* lits) const {
    display_verbose(out, m, num_lits, lits, m_bool_var2expr.data(), "\n");
    return out;
}

std::ostream& context::display_literal_smt2(std::ostream& out, literal l) const {
    if (l.sign())
        out << "(not " << mk_pp(bool_var2expr(l.var()), m) << ") ";
    else
        out << mk_pp(bool_var2expr(l.var()), m) << " ";
    return out;
}

std::ostream& context::display_literals_smt2(std::ostream& out, unsigned num_lits, literal const* lits) const {
    out << literal_vector(num_lits, lits) << ":\n";
#if 1
    expr_ref_vector fmls(m);
    for (unsigned i = 0; i < num_lits; ++i)
        fmls.push_back(literal2expr(lits[i]));
    expr_ref c = mk_or(fmls);
    out << c << "\n";
#else
    for (unsigned i = 0; i < num_lits; ++i)
        display_literal_smt2(out, lits[i]) << "\n";
#endif
    return out;
}

void context::display_literal_info(std::ostream& out, literal l) const {
    smt::display_compact(out, l, m_bool_var2expr.data());
    display_literal_smt2(out << " " << l << ": ", l);
    out << "relevant: " << is_relevant(bool_var2expr(l.var())) << ", val: " << get_assignment(l) << "\n";
}

void context::display_watch_list(std::ostream& out, literal l) const {
    display_literal(out, l);
    out << " watch_list:\n";
    watch_list& wl = const_cast<watch_list&>(m_watches[l.index()]);
    watch_list::clause_iterator it = wl.begin_clause();
    watch_list::clause_iterator end = wl.end_clause();
    for (; it != end; ++it) {
        display_clause(out, *it);
        out << "\n";
    }
}

void context::display_watch_lists(std::ostream& out) const {
    unsigned s = m_watches.size();
    for (unsigned l_idx = 0; l_idx < s; l_idx++) {
        literal l = to_literal(l_idx);
        display_watch_list(out, l);
        out << "\n";
    }
}

void context::display_enode_defs(std::ostream& out) const {
    for (enode* x : m_enodes) {
        expr* n = x->get_expr();
        ast_def_ll_pp(out, m, n, get_pp_visited(), true, false);
    }
}

void context::display_bool_var_defs(std::ostream& out) const {
    unsigned num = get_num_bool_vars();
    for (unsigned v = 0; v < num; v++) {
        expr* n = m_bool_var2expr[v];
        ast_def_ll_pp(out << v << " ", m, n, get_pp_visited(), true, false);
    }
}

std::ostream& context::display_clause_detail(std::ostream& out, clause const* cls) const {
    out << "lemma: " << cls->is_lemma() << "\n";
    for (literal l : *cls) {
        display_literal(out, l);
        out << ", val: " << get_assignment(l) << ", lvl: " << get_assign_level(l)
            << ", ilvl: " << get_intern_level(l.var()) << ", var: " << l.var() << "\n"
            << mk_bounded_pp(bool_var2expr(l.var()), m, 2) << "\n\n";
    }
    return out;
}

std::ostream& context::display_clause(std::ostream& out, clause const* cls) const {
    cls->display_compact(out, m, m_bool_var2expr.data());
    return out;
}

std::ostream& context::display_clause_smt2(std::ostream& out, clause const& cls) const {
    return display_literals_smt2(out, cls.get_num_literals(), cls.begin());
}

std::ostream& context::display_clauses(std::ostream& out, ptr_vector<clause> const& v) const {
    for (clause* cp : v) {
        out << "(";
        bool first = true;
        for (auto lit : *cp) {
            if (!first) out << " ";
            first = false;
            out << lit;
        }
        out << ")\n";
    }
    return out;
}

std::ostream& context::display_binary_clauses(std::ostream& out) const {
    unsigned l_idx = 0;
    for (watch_list const& wl : m_watches) {
        literal l1 = to_literal(l_idx++);
        literal neg_l1 = ~l1;
        literal const* it2 = wl.begin_literals();
        literal const* end2 = wl.end_literals();
        for (; it2 != end2; ++it2) {
            literal l2 = *it2;
            if (l1.index() < l2.index()) {
                out << "(" << neg_l1 << " " << l2 << ")\n";
#if 0
                    expr_ref t1(m), t2(m);
                    literal2expr(neg_l1, t1);
                    literal2expr(l2, t2);
                    expr_ref disj(m.mk_or(t1, t2), m);
                    out << mk_bounded_pp(disj, m, 3) << "\n";
#endif
            }
        }
    }
    return out;
}

void context::display_assignment(std::ostream& out) const {
    if (!m_assigned_literals.empty()) {
        out << "current assignment:\n";
        unsigned level = 0;
        for (literal lit : m_assigned_literals) {
            if (level < get_assign_level(lit.var())) {
                level = get_assign_level(lit.var());
                out << "level " << level << "\n";
            }
            display_literal(out << lit << " ", lit);
            if (!is_relevant(lit)) out << " n ";
            out << ": ";
            display_verbose(out, m, 1, &lit, m_bool_var2expr.data());
            if (level > 0) {
                auto j = get_justification(lit.var());
                display(out << " ", j);
            } else
                out << "\n";
        }
    }
}

void context::display_assignment_as_smtlib2(std::ostream& out, symbol const& logic) const {
    ast_smt_pp pp(m);
    pp.set_benchmark_name("lemma");
    pp.set_status("unknown");
    pp.set_logic(logic);
    for (literal lit : m_assigned_literals) {
        expr_ref n(m);
        literal2expr(lit, n);
        pp.add_assumption(n);
    }
    pp.display_smt2(out, m.mk_true());
}

void context::display_eqc(std::ostream& out) const {
    if (m_enodes.empty())
        return;
    unsigned count = 0;
    for (enode* r : m_enodes)
        if (r->is_root())
            ++count;

    out << "equivalence classes: " << count << "\n";
    for (enode* r : m_enodes) {
        if (!r->is_root())
            continue;
        out << "#" << enode_pp(r, *this) << "\n";
        if (r->get_class_size() == 1)
            continue;
        for (enode* n : *r) {
            if (n != r)
                out << "   #" << enode_pp(n, *this) << "\n";
        }
    }
}

void context::display_app_enode_map(std::ostream& out) const {
    return;
    // mainly useless
    if (!m_e_internalized_stack.empty()) {
        out << "expression -> enode:\n";
        unsigned sz = m_e_internalized_stack.size();
        for (unsigned i = 0; i < sz; i++) {
            expr* n = m_e_internalized_stack.get(i);
            out << "(#" << n->get_id() << " -> e!" << i << ") ";
        }
        out << "\n";
    }
}

void context::display_expr_bool_var_map(std::ostream& out) const {
    if (!m_b_internalized_stack.empty()) {
        out << "expression -> bool_var:\n";
        unsigned sz = m_b_internalized_stack.size();
        for (unsigned i = 0; i < sz; i++) {
            expr* n = m_b_internalized_stack.get(i);
            bool_var v = get_bool_var_of_id(n->get_id());
            out << "(#" << n->get_id() << " -> " << literal(v, false) << ") ";
        }
        out << "\n";
    }
}

/**
\brief a mapping of an expression to its corresponding Boolean variable (a + b <= 5 --> 1);
Constructing clauses set clauses_vec(in context) and literals set _lits(in sampler)
*/
void context::expr_bool_var_map(sampler::ls_sampler* sampler) {
    std::string myString;
    if (!m_b_internalized_stack.empty()) {
        uint64_t sz = m_b_internalized_stack.size();
        // std::cout << sz << "\n";
        sampler->make_lits_space(sz);
        int new_var_num = 0;
        int if_var_num = 0;
        for (uint64_t i = 0; i < sz; i++) {
            expr* n = m_b_internalized_stack.get(i);
            bool_var v = get_bool_var_of_id(n->get_id());
            literal l_curr = get_literal(n);
            std::stringstream ss;
            ss << l_curr.var() << " ";

            // std::cout << "to_app(n)->get_decl()->get_name() = " << to_app(n)->get_decl()->get_name() << "\n";
            if (to_app(n)->get_decl()->get_name() == "=" && m.is_bool(to_app(n)->get_arg(0))) {
                expr* eq_term_a = to_app(n)->get_arg(0);
                expr* eq_term_b = to_app(n)->get_arg(1);
                bool_var A, a, b, c;
                if (to_app(eq_term_a)->get_decl()->get_name() == "not") {
                    a = -get_bool_var_of_id(to_app(eq_term_a)->get_arg(0)->get_id());
                } else {
                    a = get_bool_var_of_id(eq_term_a->get_id());
                }
                if (to_app(eq_term_b)->get_decl()->get_name() == "not") {
                    b = -get_bool_var_of_id(to_app(eq_term_b)->get_arg(0)->get_id());
                } else {
                    b = get_bool_var_of_id(eq_term_b->get_id());
                }
                A = l_curr.var();
                std::vector<int> clause_tmp;
                clause_tmp.push_back(-A);
                clause_tmp.push_back(-a);
                clause_tmp.push_back(b);  //-A or -a or b
                clauses_vec.push_back(clause_tmp);
                clause_tmp.clear();
                clause_tmp.push_back(-A);
                clause_tmp.push_back(a);
                clause_tmp.push_back(-b);  //-A or a or -b
                clauses_vec.push_back(clause_tmp);
                clause_tmp.clear();
                clause_tmp.push_back(A);
                clause_tmp.push_back(-a);
                clause_tmp.push_back(-b);  // A or -a or -b
                clauses_vec.push_back(clause_tmp);
                clause_tmp.clear();
                clause_tmp.push_back(A);
                clause_tmp.push_back(a);
                clause_tmp.push_back(b);  // A or a or b
                clauses_vec.push_back(clause_tmp);
                ss << "equal_new_var" << new_var_num++;
            } else if (to_app(n)->get_decl()->get_name() == "or") {
                std::vector<int> clause_tmp;
                clause_tmp.push_back(-l_curr.var());
                for (unsigned j = 0; j < to_app(n)->get_num_args(); j++) {
                    expr* or_term = to_app(n)->get_arg(j);
                    std::vector<int> clause_tmp_1;
                    clause_tmp_1.push_back(l_curr.var());
                    if (to_app(or_term)->get_decl()->get_name() == "not") {
                        bool_var v1 = get_bool_var_of_id(to_app(or_term)->get_arg(0)->get_id());
                        clause_tmp.push_back(-v1);
                        clause_tmp_1.push_back(v1);
                    } else {
                        bool_var v1 = get_bool_var_of_id(or_term->get_id());
                        clause_tmp.push_back(v1);
                        clause_tmp_1.push_back(-v1);
                    }
                    clauses_vec.push_back(clause_tmp_1);
                }
                clauses_vec.push_back(clause_tmp);
                ss << "or new_var" << new_var_num++;
            } else if (to_app(n)->get_decl()->get_name() == "if") {
                expr* if_term_a = to_app(n)->get_arg(0);
                expr* if_term_b = to_app(n)->get_arg(1);
                expr* if_term_c = to_app(n)->get_arg(2);
                bool_var A, a, b, c;
                if (to_app(if_term_a)->get_decl()->get_name() == "not") {
                    a = -get_bool_var_of_id(to_app(if_term_a)->get_arg(0)->get_id());
                } else {
                    a = get_bool_var_of_id(if_term_a->get_id());
                }
                if (to_app(if_term_b)->get_decl()->get_name() == "not") {
                    b = -get_bool_var_of_id(to_app(if_term_b)->get_arg(0)->get_id());
                } else {
                    b = get_bool_var_of_id(if_term_b->get_id());
                }
                if (to_app(if_term_c)->get_decl()->get_name() == "not") {
                    c = -get_bool_var_of_id(to_app(if_term_c)->get_arg(0)->get_id());
                } else {
                    c = get_bool_var_of_id(if_term_c->get_id());
                }
                A = l_curr.var();
                std::vector<int> clause_tmp;
                clause_tmp.push_back(-A);
                clause_tmp.push_back(-a);
                clause_tmp.push_back(b);  //-A or -a or b
                clauses_vec.push_back(clause_tmp);
                clause_tmp.clear();
                clause_tmp.push_back(-A);
                clause_tmp.push_back(a);
                clause_tmp.push_back(c);  //-A or a or c
                clauses_vec.push_back(clause_tmp);
                clause_tmp.clear();
                clause_tmp.push_back(A);
                clause_tmp.push_back(-a);
                clause_tmp.push_back(-b);  // A or -a or -b
                clauses_vec.push_back(clause_tmp);
                clause_tmp.clear();
                clause_tmp.push_back(A);
                clause_tmp.push_back(a);
                clause_tmp.push_back(-c);  // A or a or -c
                clauses_vec.push_back(clause_tmp);
                clause_tmp.clear();
                clause_tmp.push_back(A);
                clause_tmp.push_back(-b);
                clause_tmp.push_back(-c);  // A or -b or -c
                clauses_vec.push_back(clause_tmp);
                ss << "if if_var" << if_var_num++;
            } else {
                smt::display(ss, l_curr, m, m_bool_var2expr.data());
            }  // 将布尔变量对应的表达式存放在string中
            myString = ss.str();
            sampler->build_lits(myString);
        }
    }
#ifdef SAMPLER_DEBUG
    SAMPLER_TRACE(
        tout << "lit strings:\n";
        for (int i = 0; i < debug_myString.size(); ++i) {
            tout << i << ": " << debug_myString[i] << "\n";
        });
#endif
    SAMPLER_TRACE(
        tout << "clauses_vec:\n";
        print_clauses_vec(tout, clauses_vec););
    SAMPLER_TRACE(
        tout << "display_bool_var_defs:\n";
        display_bool_var_defs(tout););
    SAMPLER_TRACE(display_expr_bool_var_map(tout););
}

void context::print_clauses_vec(std::ostream& out, const std::vector<std::vector<int> >& vec) {
    out << "0\n"
        << vec.size() << "\n";
    int cls_num = 0;
    for (auto cl : vec) {
        out << "cls " << cls_num++ << ": (";
        for (auto l : cl) {
            out << " " << l;
        }
        out << " )\n";
    }
}

void context::display_hot_bool_vars(std::ostream& out) const {
    out << "hot bool vars:\n";
    unsigned num = get_num_bool_vars();
    for (bool_var v = 0; v < num; v++) {
        double val = get_activity(v) / m_bvar_inc;
        if (val > 10.00) {
            expr* n = m_b_internalized_stack.get(v);
            out << "#";
            out.width(5);
            out << std::left;
            out << n->get_id();
            out << "  ";
            out.width(12);
            out << std::right;
            out << get_activity(v) << "  ";
            out.width(12);
            out << val;
            out << "\n";
        }
    }
}

void context::display_relevant_exprs(std::ostream& out) const {
    m_relevancy_propagator->display(out);
}

void context::display_theories(std::ostream& out) const {
    for (theory* th : m_theory_set) {
        th->display(out);
    }
}

void context::display(std::ostream& out) const {
    get_pp_visited().reset();
    out << "Logical context:\n";
    out << "scope-lvl: " << m_scope_lvl << "\n";
    out << "base-lvl:  " << m_base_lvl << "\n";
    out << "search-lvl:  " << m_search_lvl << "\n";
    out << "inconsistent(): " << inconsistent() << "\n";
    out << "m_asserted_formulas.inconsistent(): " << m_asserted_formulas.inconsistent() << "\n";
    display_bool_var_defs(out);
    display_enode_defs(out);
    display_asserted_formulas(out);
    display_binary_clauses(out);
    if (!m_aux_clauses.empty()) {
        out << "auxiliary clauses:\n";
        display_clauses(out, m_aux_clauses);
    }
    if (!m_lemmas.empty()) {
        out << "lemmas:\n";
        display_clauses(out, m_lemmas);
    }
    display_assignment(out);
    display_eqc(out);
    m_cg_table.display_compact(out);
    m_case_split_queue->display(out);
    display_expr_bool_var_map(out);
    display_app_enode_map(out);
    display_relevant_exprs(out);
    display_theories(out);
    display_decl2enodes(out);
    display_hot_bool_vars(out);
}

void context::display_eq_detail(std::ostream& out, enode* n) const {
    SASSERT(n->is_eq());
    out << "#" << n->get_owner_id()
        << ", root: #" << n->get_root()->get_owner_id()
        << ", cg: #" << n->m_cg->get_owner_id()
        << ", val: " << get_assignment(enode2bool_var(n))
        << ", lhs: #" << n->get_arg(0)->get_owner_id()
        << ", rhs: #" << n->get_arg(1)->get_owner_id()
        << ", lhs->root: #" << n->get_arg(0)->get_root()->get_owner_id()
        << ", rhs->root: #" << n->get_arg(1)->get_root()->get_owner_id()
        << ", is_marked: " << n->is_marked()
        << ", is_relevant: " << is_relevant(n)
        << ", iscope_lvl: " << n->get_iscope_lvl() << "\n";
}

void context::display_parent_eqs(std::ostream& out, enode* n) const {
    for (enode* parent : n->get_parents()) {
        if (parent->is_eq())
            display_eq_detail(out, parent);
    }
}

void context::display_unsat_core(std::ostream& out) const {
    for (expr* c : m_unsat_core) {
        out << mk_pp(c, m) << "\n";
    }
}

void context::collect_statistics(::statistics& st) const {
    st.copy(m_aux_stats);
    st.update("conflicts", m_stats.m_num_conflicts);
    st.update("decisions", m_stats.m_num_decisions);
    st.update("propagations", m_stats.m_num_propagations + m_stats.m_num_bin_propagations);
    st.update("binary propagations", m_stats.m_num_bin_propagations);
    st.update("restarts", m_stats.m_num_restarts);
    st.update("final checks", m_stats.m_num_final_checks);
    st.update("added eqs", m_stats.m_num_add_eq);
    st.update("mk clause", m_stats.m_num_mk_clause);
    st.update("mk clause binary", m_stats.m_num_mk_bin_clause);
    st.update("del clause", m_stats.m_num_del_clause);
    st.update("dyn ack", m_stats.m_num_dyn_ack);
    st.update("interface eqs", m_stats.m_num_interface_eqs);
    st.update("max generation", m_stats.m_max_generation);
    st.update("minimized lits", m_stats.m_num_minimized_lits);
    st.update("num checks", m_stats.m_num_checks);
    st.update("mk bool var", m_stats.m_num_mk_bool_var ? m_stats.m_num_mk_bool_var - 1 : 0);
    m_qmanager->collect_statistics(st);
    m_asserted_formulas.collect_statistics(st);
    for (theory* th : m_theory_set) {
        th->collect_statistics(st);
    }
}

void context::display_statistics(std::ostream& out) const {
    ::statistics st;
    collect_statistics(st);
    st.display(out);
}

void context::display_istatistics(std::ostream& out) const {
    ::statistics st;
    collect_statistics(st);
    st.display_internal(out);
}

void context::display_lemma_as_smt_problem(std::ostream& out, unsigned num_antecedents, literal const* antecedents, literal consequent, symbol const& logic) const {
    ast_pp_util visitor(m);
    expr_ref_vector fmls(m);
    visitor.collect(fmls);
    expr_ref n(m);
    for (unsigned i = 0; i < num_antecedents; i++) {
        literal l = antecedents[i];
        literal2expr(l, n);
        fmls.push_back(std::move(n));
    }
    if (consequent != false_literal) {
        literal2expr(~consequent, n);
        fmls.push_back(std::move(n));
    }

    if (logic != symbol::null) out << "(set-logic " << logic << ")\n";
    visitor.collect(fmls);
    visitor.display_decls(out);
    visitor.display_asserts(out, fmls, true);
    out << "(check-sat)\n";
}

unsigned context::display_lemma_as_smt_problem(unsigned num_antecedents, literal const* antecedents, literal consequent, symbol const& logic) const {
    std::string name = mk_lemma_name();
    std::ofstream out(name);
    TRACE("lemma", tout << name << "\n";);
    display_lemma_as_smt_problem(out, num_antecedents, antecedents, consequent, logic);
    out.close();
    return m_lemma_id;
}

void context::display_lemma_as_smt_problem(std::ostream& out, unsigned num_antecedents, literal const* antecedents,
                                           unsigned num_eq_antecedents, enode_pair const* eq_antecedents,
                                           literal consequent, symbol const& logic, enode* x, enode* y) const {
    ast_pp_util visitor(m);
    expr_ref_vector fmls(m);
    visitor.collect(fmls);
    expr_ref n(m);
    for (unsigned i = 0; i < num_antecedents; i++) {
        literal l = antecedents[i];
        literal2expr(l, n);
        fmls.push_back(n);
    }
    for (unsigned i = 0; i < num_eq_antecedents; i++) {
        enode_pair const& p = eq_antecedents[i];
        n = m.mk_eq(p.first->get_expr(), p.second->get_expr());
        fmls.push_back(n);
    }
    if (x && y) {
        expr_ref eq(m.mk_eq(x->get_expr(), y->get_expr()), m);
        fmls.push_back(m.mk_not(eq));
    }
    if (consequent != false_literal) {
        literal2expr(~consequent, n);
        fmls.push_back(n);
    }

    if (logic != symbol::null) out << "(set-logic " << logic << ")\n";
    visitor.collect(fmls);
    visitor.display_decls(out);
    visitor.display_asserts(out, fmls, true);
    out << "(check-sat)\n";
}

std::string context::mk_lemma_name() const {
    std::stringstream strm;
#ifndef SINGLE_THREAD
    std::thread::id this_id = std::this_thread::get_id();
    strm << "lemma_" << this_id << "." << (++m_lemma_id) << ".smt2";
#else
    strm << "lemma_" << (++m_lemma_id) << ".smt2";
#endif
    return std::move(strm).str();
}

unsigned context::display_lemma_as_smt_problem(unsigned num_antecedents, literal const* antecedents,
                                               unsigned num_eq_antecedents, enode_pair const* eq_antecedents,
                                               literal consequent, symbol const& logic) const {
    std::string name = mk_lemma_name();
    std::ofstream out(name);
    TRACE("lemma", tout << name << "\n";
          display_lemma_as_smt_problem(tout, num_antecedents, antecedents, num_eq_antecedents, eq_antecedents, consequent, logic););
    display_lemma_as_smt_problem(out, num_antecedents, antecedents, num_eq_antecedents, eq_antecedents, consequent, logic);
    out.close();
    return m_lemma_id;
}

/**
   \brief Display enode definitions #n := (f #i_1 ... #i_n), where #i_k is the root
   of the k-th argument of the enode #n.
 */
void context::display_normalized_enodes(std::ostream& out) const {
    out << "normalized enodes:\n";
    for (enode* n : m_enodes) {
        out << "#";
        out.width(5);
        out << std::left << n->get_owner_id() << " #";
        out.width(5);
        out << n->get_root()->get_owner_id() << " := " << std::right;
        unsigned num = n->get_expr()->get_num_args();
        if (num > 0)
            out << "(";
        out << n->get_decl()->get_name();
        if (!n->get_decl()->private_parameters())
            display_parameters(out, n->get_decl()->get_num_parameters(), n->get_decl()->get_parameters());
        for (unsigned i = 0; i < num; i++) {
            expr* arg = n->get_expr()->get_arg(i);
            if (e_internalized(arg)) {
                enode* n = get_enode(arg)->get_root();
                out << " #" << n->get_owner_id();
            } else {
                out << " #" << arg->get_id();
            }
        }
        if (num > 0)
            out << ")";
        if (is_relevant(n))
            out << "\t*";
        out << "\n";
    }
}

void context::display_enodes_lbls(std::ostream& out) const {
    for (enode* n : m_enodes) {
        n->display_lbls(out);
    }
}

void context::display_decl2enodes(std::ostream& out) const {
    out << "decl2enodes:\n";
    unsigned id = 0;
    for (enode_vector const& v : m_decl2enodes) {
        if (!v.empty()) {
            out << "id " << id << " ->";
            for (enode* n : v) {
                out << " #" << n->get_owner_id();
            }
            out << "\n";
        }
        ++id;
    }
}

void context::display_subexprs_info(std::ostream& out, expr* n) const {
    ptr_buffer<expr> todo;
    todo.push_back(n);
    while (!todo.empty()) {
        expr* n = todo.back();
        todo.pop_back();
        out << "#";
        out.width(6);
        out << std::left << n->get_id();
        out << ", relevant: " << is_relevant(n);
        if (m.is_bool(n)) {
            out << ", val: ";
            out.width(7);
            out << std::right;
            if (lit_internalized(n))
                out << get_assignment(n);
            else
                out << "l_undef";
        }
        if (e_internalized(n)) {
            enode* e = get_enode(n);
            out << ", root: #" << e->get_root()->get_owner_id();
        }
        out << "\n";
        if (is_app(n)) {
            for (expr* arg : *to_app(n)) {
                todo.push_back(arg);
            }
        }
    }
}

std::ostream& context::display(std::ostream& out, b_justification j) const {
    switch (j.get_kind()) {
        case b_justification::AXIOM:
            out << "axiom";
            break;
        case b_justification::BIN_CLAUSE:
            out << "bin " << j.get_literal();
            break;
        case b_justification::CLAUSE: {
            clause* cls = j.get_clause();
            out << "clause ";
            if (cls) out << literal_vector(cls->get_num_literals(), cls->begin());
            // if (cls) display_literals_smt2(out << "\n", cls->get_num_literals(), cls->begin());
            break;
        }
        case b_justification::JUSTIFICATION: {
            literal_vector lits;
            const_cast<conflict_resolution&>(*m_conflict_resolution).justification2literals(j.get_justification(), lits);
            out << "justification " << j.get_justification()->get_from_theory() << ": ";
            display_literals_smt2(out, lits);
            break;
        }
        default:
            UNREACHABLE();
            break;
    }
    return out << "\n";
}

std::ostream& context::display_compact_j(std::ostream& out, b_justification j) const {
    switch (j.get_kind()) {
        case b_justification::AXIOM:
            out << "axiom";
            break;
        case b_justification::BIN_CLAUSE:
            out << "bin " << j.get_literal();
            break;
        case b_justification::CLAUSE: {
            clause* cls = j.get_clause();
            out << "clause ";
            if (cls) out << literal_vector(cls->get_num_literals(), cls->begin());
            break;
        }
        case b_justification::JUSTIFICATION: {
            literal_vector lits;
            const_cast<conflict_resolution&>(*m_conflict_resolution).justification2literals(j.get_justification(), lits);
            out << "justification " << j.get_justification()->get_from_theory() << ": ";
            out << lits;
            break;
        }
        default:
            UNREACHABLE();
            break;
    }
    return out << "\n";
}

void context::trace_assign(literal l, b_justification j, bool decision) const {
    SASSERT(m.has_trace_stream());
    std::ostream& out = m.trace_stream();
    ast_manager::suspend_trace _st(m);
    out << "[assign] ";
    display_literal(out, l);
    if (decision)
        out << " decision";
    out << " ";
    display_compact_j(out, j);
}

std::ostream& operator<<(std::ostream& out, enode_pp const& p) {
    ast_manager& m = p.ctx.get_manager();
    enode* n = p.n;
    return out << n->get_owner_id() << ": " << mk_bounded_pp(n->get_expr(), m);
}

std::ostream& operator<<(std::ostream& out, enode_eq_pp const& p) {
    return out << enode_pp(p.p.first, p.ctx) << " = " << enode_pp(p.p.second, p.ctx) << "\n";
}

void context::log_stats() {
    size_t bin_clauses = 0, bin_lemmas = 0;
    for (watch_list const& w : m_watches) {
        bin_clauses += w.end_literals() - w.begin_literals();
    }
    bin_clauses /= 2;
    for (clause* cp : m_lemmas)
        if (cp->get_num_literals() == 2)
            ++bin_lemmas;
    auto num_units = [&]() {
        if (m_scopes.empty())
            return m_assigned_literals.size();
        else
            return m_scopes[0].m_assigned_literals_lim;
    };
    std::stringstream strm;
    strm << "(smt.stats "
         << std::setw(4) << m_stats.m_num_restarts << ' '
         << std::setw(6) << m_stats.m_num_conflicts << ' '
         << std::setw(6) << m_stats.m_num_decisions << ' '
         << std::setw(6) << m_stats.m_num_propagations << ' '
         << std::setw(5) << (m_aux_clauses.size() + bin_clauses) << '/' << bin_clauses << '/' << num_units() << ' '
         << std::setw(7) << m_lemmas.size() << '/' << bin_lemmas << ' '
         << std::setw(5) << m_stats.m_num_simplifications << ' '
         << std::setw(4) << m_stats.m_num_del_clauses << ' '
         << std::setw(7) << mem_stat() << ")\n";

    std::string str = std::move(strm).str();
    svector<size_t> offsets;
    for (size_t i = 0; i < str.size(); ++i) {
        while (i < str.size() && str[i] != ' ') ++i;
        while (i < str.size() && str[i] == ' ') ++i;
        // position of first character after space
        if (i < str.size()) {
            offsets.push_back(i);
        }
    }
    bool same = m_last_positions.size() == offsets.size();
    size_t diff = 0;
    for (unsigned i = 0; i < offsets.size() && same; ++i) {
        if (m_last_positions[i] > offsets[i]) diff += m_last_positions[i] - offsets[i];
        if (m_last_positions[i] < offsets[i]) diff += offsets[i] - m_last_positions[i];
    }

    if (m_last_positions.empty() ||
        m_stats.m_num_restarts >= 20 + m_last_position_log ||
        (m_stats.m_num_restarts >= 6 + m_last_position_log && (!same || diff > 3))) {
        m_last_position_log = m_stats.m_num_restarts;
        // restarts       decisions      clauses    simplifications  memory
        //      conflicts       propagations    lemmas       deletions
        const int adjust[9] = {-3, -3, -3, -3, -3, -4, -4, -4, -1};
        char const* tag[9] = {":restarts ", ":conflicts ", ":decisions ", ":propagations ", ":clauses/bin/units ", ":lemmas ", ":simplify ", ":deletions", ":memory"};

        std::stringstream l1, l2;
        l1 << "(smt.stats ";
        l2 << "(smt.stats ";
        size_t p1 = 11, p2 = 11;
        SASSERT(offsets.size() == 9);
        for (unsigned i = 0; i < offsets.size(); ++i) {
            size_t p = offsets[i];
            if (i & 0x1) {
                // odd positions
                for (; p2 < p + adjust[i]; ++p2) l2 << " ";
                p2 += strlen(tag[i]);
                l2 << tag[i];
            } else {
                // even positions
                for (; p1 < p + adjust[i]; ++p1) l1 << " ";
                p1 += strlen(tag[i]);
                l1 << tag[i];
            }
        }
        for (; p1 + 2 < str.size(); ++p1) l1 << " ";
        for (; p2 + 2 < str.size(); ++p2) l2 << " ";
        l1 << ")\n";
        l2 << ")\n";
        IF_VERBOSE(2, verbose_stream() << l1.str() << l2.str());
        m_last_positions.reset();
        m_last_positions.append(offsets);
    }
    IF_VERBOSE(2, verbose_stream() << str);
}

};  // namespace smt
