/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    horn_tactic.h

Abstract:

    HORN as a tactic to solve Horn clauses.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-16.

Revision History:

--*/
#include "ast/ast_util.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/expr_replacer.h"
#include "tactic/tactical.h"
#include "ast/converters/model_converter.h"
#include "ast/converters/proof_converter.h"
#include "ast/converters/generic_model_converter.h"
#include "muz/fp/horn_tactic.h"
#include "muz/base/dl_context.h"
#include "muz/fp/dl_register_engine.h"
#include "muz/base/dl_rule_transformer.h"
#include "muz/transforms/dl_mk_slice.h"
#include "muz/transforms/dl_transforms.h"
#include "muz/base/fp_params.hpp"

class horn_tactic : public tactic {
    struct imp {
        ast_manager&             m;
        bool                     m_is_simplify;
        datalog::register_engine m_register_engine;
        datalog::context         m_ctx;
        smt_params               m_fparams;
        expr_free_vars           m_free_vars;

        imp(bool t, ast_manager & m, params_ref const & p):
            m(m),
            m_is_simplify(t),
            m_ctx(m, m_register_engine, m_fparams) {
            updt_params(p);
        }

        void updt_params(params_ref const & p) {
            m_ctx.updt_params(p);
        }

        void collect_param_descrs(param_descrs & r) {
            m_ctx.collect_params(r);
        }

        void reset_statistics() {
            m_ctx.reset_statistics();
        }

        void collect_statistics(statistics & st) const {
            m_ctx.collect_statistics(st);
        }

        void normalize(expr_ref& f) {
            bool is_positive = true;
            expr* e = nullptr;
            while (true) {
                if (is_forall(f) && is_positive) {
                    f = to_quantifier(f)->get_expr();
                }
                else if (is_exists(f) && !is_positive) {
                    f = to_quantifier(f)->get_expr();
                }
                else if (m.is_not(f, e)) {
                    is_positive = !is_positive;
                    f = e;
                }
                else {
                    break;
                }
            }
            if (!is_positive) {
                f = m.mk_not(f);
            }
        }

        bool is_predicate(expr* a) {
            SASSERT(m.is_bool(a));
            return is_app(a) && to_app(a)->get_decl()->get_family_id() == null_family_id;
        }

        void register_predicate(expr* a) {
            SASSERT(is_predicate(a));
            m_ctx.register_predicate(to_app(a)->get_decl(), false);
        }

        void check_predicate(ast_mark& mark, expr* a) {
            ptr_vector<expr> todo;
            todo.push_back(a);
            while (!todo.empty()) {
                a = todo.back();
                todo.pop_back();
                if (mark.is_marked(a)) {
                    continue;
                }
                mark.mark(a, true);
                if (is_quantifier(a)) {
                    a = to_quantifier(a)->get_expr();
                    todo.push_back(a);
                }
                else if (m.is_not(a) || m.is_and(a) || m.is_or(a) || m.is_implies(a)) {
                    todo.append(to_app(a)->get_num_args(), to_app(a)->get_args());
                }
                else if (m.is_ite(a)) {
                    todo.push_back(to_app(a)->get_arg(1));
                    todo.push_back(to_app(a)->get_arg(2));
                }
                else if (is_predicate(a)) {
                    register_predicate(a);
                }
            }
        }

        enum formula_kind { IS_RULE, IS_QUERY, IS_NONE };

        bool is_implication(expr* f) {
            expr* e1;
            while (is_forall(f)) {
                f = to_quantifier(f)->get_expr();
            }
            while (m.is_implies(f, e1, f)) ;
            return is_predicate(f);
        }

        formula_kind get_formula_kind(expr_ref& f) {
            expr_ref tmp(f);
            normalize(tmp);
            ast_mark mark;
            expr_ref_vector args(m), body(m);
            expr_ref head(m);
            expr* a = nullptr, *a1 = nullptr;
            flatten_or(tmp, args);
            for (unsigned i = 0; i < args.size(); ++i) {
                a = args[i].get();
                check_predicate(mark, a);
                if (m.is_not(a, a1)) {
                    body.push_back(a1);
                }
                else if (is_predicate(a)) {
                    if (head) {
                        return IS_NONE;
                    }
                    head = a;
                }
                else {
                    body.push_back(m.mk_not(a));
                }
            }
            if (head) {
                if (!is_implication(f)) {
                    f = m.mk_and(body.size(), body.data());
                    f = m.mk_implies(f, head);
                }
                return IS_RULE;
            }
            else {
                f = m.mk_and(body.size(), body.data());
                return IS_QUERY;
            }
        }

        expr_ref mk_rule(expr* body, expr* head) {
            return expr_ref(m.mk_implies(body, head), m);
        }

        void operator()(goal_ref const & g,
                        goal_ref_buffer & result) {
            tactic_report report("horn", *g);
            bool produce_proofs = g->proofs_enabled();

            if (produce_proofs) {
                if (!m_ctx.generate_proof_trace()) {
                    params_ref params = m_ctx.get_params().p;
                    params.set_bool("generate_proof_trace", true);
                    updt_params(params);
                }
            }

            unsigned sz = g->size();
            expr_ref q(m), f(m);
            expr_ref_vector queries(m);
            std::stringstream msg;
            
            check_parameters();

            m_ctx.reset();
            m_ctx.ensure_opened();

            for (unsigned i = 0; i < sz; i++) {
                f = g->form(i);
                formula_kind k = get_formula_kind(f);
                switch(k) {
                case IS_RULE:
                    m_ctx.add_rule(f, symbol::null);
                    break;
                case IS_QUERY:
                    queries.push_back(f);
                    break;
                default:
                    msg << "formula is not in Horn fragment: " << mk_pp(g->form(i), m) << "\n";
                    TRACE("horn", tout << msg.str(););
                    throw tactic_exception(msg.str());
                }
            }

            if (queries.size() != 1 || m_is_simplify) {
                q = m.mk_fresh_const("query", m.mk_bool_sort());
                register_predicate(q);
                for (unsigned i = 0; i < queries.size(); ++i) {
                    f = mk_rule(queries[i].get(), q);
                    bind_variables(f);
                    m_ctx.add_rule(f, symbol::null);
                }
                queries.reset();
                queries.push_back(q);
                generic_model_converter* mc1 = alloc(generic_model_converter, m, "horn");
                mc1->hide(q);
                g->add(mc1);
            }
            
            SASSERT(queries.size() == 1);
            q = queries[0].get();
            proof_converter_ref pc = g->pc();
            model_converter_ref mc;
            if (m_is_simplify) {
                simplify(q, g, result, mc, pc);
            }
            else {
                verify(q, g, result, mc, pc);
            }
            g->set(pc.get());
            g->add(mc.get());
        }

        void verify(expr* q,
                    goal_ref const& g,
                    goal_ref_buffer & result,
                    model_converter_ref & mc,
                    proof_converter_ref & pc) {

            lbool is_reachable = l_undef;
            try {
                is_reachable = m_ctx.query(q);
            }
            catch (default_exception& ex) {
                IF_VERBOSE(1, verbose_stream() << ex.what() << "\n";);
                throw ex;
            }
            g->inc_depth();

            bool produce_models = g->models_enabled();
            bool produce_proofs = g->proofs_enabled();

            result.push_back(g.get());
            switch (is_reachable) {
            case l_true: {
                // goal is unsat
                if (!m_ctx.is_monotone()) {
                    is_reachable = l_undef;
                }
                else if (produce_proofs) {
                    proof_ref proof = m_ctx.get_proof();
                    pc = proof2proof_converter(m, proof);
                    g->assert_expr(m.get_fact(proof), proof, nullptr);
                }
                else {
                    g->assert_expr(m.mk_false());
                }
                break;
            }
            case l_false: {
                // goal is sat
                g->reset();
                if (produce_models) {
                    model_ref md = m_ctx.get_model();
                    model_converter_ref mc2 = model2model_converter(md.get());
                    mc = mc2.get();
                    TRACE("dl", mc->display(tout << *md << "\n"););
                }
                break;
            }
            case l_undef:
                // subgoal is unchanged.
                break;
            }
        }

        void bind_variables(expr_ref& f) {
            m_free_vars.reset();
            m_free_vars(f);
            m_free_vars.set_default_sort(m.mk_bool_sort());
            if (!m_free_vars.empty()) {
                m_free_vars.reverse();
                svector<symbol> names;
                for (unsigned i = 0; i < m_free_vars.size(); ++i) {
                    names.push_back(symbol(m_free_vars.size() - i - 1));
                }
                f = m.mk_forall(m_free_vars.size(), m_free_vars.data(), names.data(), f);
            }
        }

        void simplify(expr* q,
                      goal_ref const& g,
                      goal_ref_buffer & result,
                      model_converter_ref & mc,
                      proof_converter_ref & pc) {

            expr_ref fml(m);
            func_decl* query_pred = to_app(q)->get_decl();
            m_ctx.set_output_predicate(query_pred);
            m_ctx.get_rules(); // flush adding rules.
            apply_default_transformation(m_ctx);

            if (m_ctx.xform_slice()) {
                datalog::rule_transformer transformer(m_ctx);
                datalog::mk_slice* slice = alloc(datalog::mk_slice, m_ctx);
                transformer.register_plugin(slice);
                m_ctx.transform_rules(transformer);
            }

            expr_substitution sub(m);
            sub.insert(q, m.mk_false());
            scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m, false);
            rep->set_substitution(&sub);
            g->inc_depth();
            g->reset();
            result.push_back(g.get());
            datalog::rule_set const& rules = m_ctx.get_rules();
            for (datalog::rule* r : rules) {
                m_ctx.get_rule_manager().to_formula(*r, fml);
                (*rep)(fml);
                g->assert_expr(fml);
            }
            g->set_prec(goal::UNDER_OVER);
            mc = g->mc();
        }

        void check_parameters() {
            fp_params const& p = m_ctx.get_params();
            if (p.engine() == symbol("datalog"))
                not_supported("engine=datalog");
            if (p.datalog_generate_explanations())
                not_supported("datalog.generate_explanations"); 
            if (p.datalog_magic_sets_for_queries())
                not_supported("datalog.magic_sets_for_queries");
            if (p.xform_instantiate_arrays())
                not_supported("xform.instantiate_arrays");
            if (p.xform_magic())
                not_supported("xform.magic");
            if (p.xform_quantify_arrays())
                not_supported("xform.quantify_arrays");
            if (p.xform_scale())
                not_supported("xform.scale");
        }

        void not_supported(char const* s) {
            throw default_exception(std::string("unsupported parameter ") + s);
        }

    };



    bool       m_is_simplify;
    params_ref m_params;
    statistics m_stats;
    imp *      m_imp;
public:
    horn_tactic(bool t, ast_manager & m, params_ref const & p):
        m_is_simplify(t),
        m_params(p) {
        m_imp = alloc(imp, t, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(horn_tactic, m_is_simplify, m, m_params);
    }

    ~horn_tactic() override {
        dealloc(m_imp);
    }

    char const* name() const override { return "horn"; }

    void updt_params(params_ref const & p) override {
        m_params.append(p);
        m_imp->updt_params(m_params);
    }


    void collect_param_descrs(param_descrs & r) override {
        m_imp->collect_param_descrs(r);
    }

    void operator()(goal_ref const & in,
                    goal_ref_buffer & result) override {
        (*m_imp)(in, result);
    }

    void collect_statistics(statistics & st) const override {
        m_imp->collect_statistics(st);
        st.copy(m_stats);
    }

    void reset_statistics() override {
        m_stats.reset();
        m_imp->reset_statistics();
    }

    void cleanup() override {
        ast_manager & m = m_imp->m;
        m_imp->collect_statistics(m_stats);
        dealloc(m_imp);
        m_imp = alloc(imp, m_is_simplify, m, m_params);

    }


};

tactic * mk_horn_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(horn_tactic, false, m, p));
}

tactic * mk_horn_simplify_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(horn_tactic, true, m, p));
}
