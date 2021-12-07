import tactic.interactive_expr
import tactic.ring
import tactic.abel

import common
import types
import parsers


namespace tactic.interactive
setup_tactic_parser

open tactic

meta def compute_at_hyp' (h : name) : tactic unit :=
let lo := loc.ns [h] in
do { ring_nf (some ()) tactic.ring.normalize_mode.horner lo <|>
     abel none tactic.abel.normalize_mode.term lo,
     try (norm_num [] lo),
     try (`[dsimp only]) }

meta def compute_at_goal' : tactic unit :=
do focus (tactic.iterate_at_most 3 `[refl <|> ring_nf <|> abel <|> norm_num] >>= list.mmap' (λ _, skip))

meta def Fix1 : introduced → tactic unit 
| (introduced.typed n t)   := do check_name n,
                                 et ← to_expr t,
                                 e ← intro_obj n <|> fail "There is no object to introduce here.",
                                 change_core et e
| (introduced.bare n)      := do check_name n,
                                 intro_obj n <|> fail "There is no object to introduce here.", 
                                 skip
| (introduced.related n rel e) := do check_name n,
                                 ename ← intro_obj n <|> fail "There is no object to introduce here.",
                                 n_type ← infer_type ename,
                                 E ← match rel with
                                 | intro_rel.mem := to_expr e
                                 | _ := to_expr ```(%%e : %%n_type)
                                 end,
                                 rel_expr ← match rel with
                                 | intro_rel.lt := to_expr ``(%%ename < %%E)
                                 | intro_rel.gt := to_expr ``(%%ename > %%E)
                                 | intro_rel.le := to_expr ``(%%ename ≤ %%E)
                                 | intro_rel.ge := to_expr ``(%%ename ≥ %%E)
                                 | intro_rel.mem := to_expr ``(%%ename ∈ %%E)
                                 end,
                                 let hyp_name := if e = ``(0) then
                                    match rel with
                                    | intro_rel.lt  := n.to_string ++ "_neg"
                                    | intro_rel.gt  := n.to_string ++ "_pos"
                                    | intro_rel.le  := n.to_string ++ "_neg"
                                    | intro_rel.ge  := n.to_string ++ "_pos"
                                    | intro_rel.mem := "h_" ++ n.to_string -- shouldn't happen
                                    end
                                 else 
                                    match rel with
                                    | intro_rel.lt  := n.to_string ++ "_lt"
                                    | intro_rel.gt  := n.to_string ++ "_gt"
                                    | intro_rel.le  := n.to_string ++ "_le"
                                    | intro_rel.ge  := n.to_string ++ "_ge"
                                    | intro_rel.mem := n.to_string ++ "_mem"
                                    end,
                                 EH ← tactic.intro hyp_name,
                                 change_core rel_expr EH,
                                 skip
                                 
/-- Introduces one or more objects to prove a statement starting with a universal quantifier. -/
meta def Fix (vs : parse $ with_desc "..." bracketed_intro_parser*) : tactic unit :=
vs.mmap' Fix1

/-- Annonce ce qu'on va démontrer. -/
meta def «Let's» : parse Lets_parser → tactic unit
| (Lets_args.but pe) := do e ← to_expr pe, 
                do { change_core e none } <|> 
                do { left, change_core e none} <|>
                do { right, change_core e none} <|>
                do { split, change_core e none} <|>
                do { interactive.push_neg (loc.ns [none]), 
                     do { change_core e none } <|> 
                     do { `[simp only [exists_prop]], 
                          change_core e none } <|>
                     do { `[simp only [← exists_prop]], 
                          change_core e none }
                     } <|>
                fail "This is not what should be proven."
| (Lets_args.temoin pe But) := do tactic.use [pe],
                    try `[simp only [exists_prop]],
                    t ← target,
                    match But with
                    | (some truc) := do etruc ← to_expr truc, 
                                        change_core etruc none,
                                        skip
                    | none := skip
                    end,
                    match t with
                    | `(%%P ∧ %%Q) := split >> skip
                    | _ := skip
                    end,
                    all_goals (try assumption),
                    all_goals (try interactive.refl),
                    skip

| Lets_args.ex_falso := tactic.interactive.exfalso
| (Lets_args.recur hyp pe) := focus1 (do
      check_name hyp,
      e ← to_expr pe,
      match e with
      | (expr.pi n bi t b) := if t = `(ℕ) then do
              to_expr pe >>= tactic.assert hyp,
              `[refine nat.rec _ _],
              focus' [try `[dsimp only], 
                      do { change_head_name n,
                           try `[simp_rw ← nat.add_one] },
                      do { e ← get_local hyp, 
                           tactic.try (tactic.apply e) }],
              skip
          else fail "The statement must start with a universal quantifier on a natural number."
      | _ := fail "The statement must start with a universal quantifier on a natural number."
      end)

/-- Proof action -/
meta def We : parse We_parser → tactic unit
| (We_args.exct_aply pe l) := conclude_tac pe l
| (We_args.aply pe) := focus1 (do 
    to_expr pe >>= tactic.apply,
    all_goals (do try assumption, cleanup_a_bit),
    skip)
| (We_args.aply_at pe pl) := do l ← pl.mmap to_expr,
                        l.mmap' (apply_arrow_to_hyp pe)  <|> interactive.specialize (pexpr_mk_app pe pl)
| (We_args.rwrite pe l new) := do interactive.rewrite pe (loc.ns [l]),
                          match (l, new) with
                          | (some hyp, some newhyp) := do ne ← get_local hyp, 
                                                          enewhyp ← to_expr newhyp,
                                                          infer_type ne >>= unify enewhyp
                          | (_, some n) := fail "You can't use \"which becomes\" when replacing at several places."
                          | (_, none) := skip
                          end
| (We_args.rwrite_all pe) := interactive.rewrite pe loc.wildcard
| We_args.compute_ := compute_at_goal'
| (We_args.compute_at h) := compute_at_hyp' h
| (We_args.linar le) := do le' ← le.mmap to_expr >>= split_ands,
                   tactic.linarith ff tt le' <|> fail "Combining those facts is not enough."
| (We_args.contrap push_opt) := do 
      `(%%P → %%Q) ← target | fail "Can't contrapose since the goal is not an implication",
      cp ← mk_mapp ``imp_of_not_imp_not [P, Q] <|> fail "Can't contrapose since the goal is not an implication",
      tactic.apply cp,
      if push_opt then try (tactic.interactive.push_neg (loc.ns [none])) else skip
| (We_args.discussion pe) := focus1 (do e ← to_expr pe,
                                `(%%P ∨ %%Q) ← infer_type e <|> fail "This expression is not a disjunction.",
                                tgt ← target, 
                                `[refine (or.elim %%e _ _)],
                                all_goals (try (tactic.clear e)) >> skip)
| (We_args.discussion_hyp pe) := do e ← to_expr pe, 
                        `[refine (or.elim (classical.em %%e) _ _)]
| (We_args.deplie le) := interactive.unfold le (loc.ns [none])
| (We_args.deplie_at le loca new) := do interactive.unfold le loca,
                                match (loca, new) with
                                | (loc.ns [some hyp], some newhyp) := do ne ← get_local hyp, 
                                                                         enewhyp ← to_expr newhyp,
                                                                         infer_type ne >>= unify enewhyp
                                | (_, some n) := fail "You can't use \"which becomes\" when unfolding at several places."
                                | (_, none) := skip
                                end
| (We_args.rname old new loca newhyp) := match (loca, newhyp) with
                          | (some (loc.ns [some n]), some truc) := do e ← get_local n, 
                                                                      rename_var_at_hyp old new e,
                                                                      interactive.guard_hyp_strict n truc <|>
                                                                        fail "This is not the obtained expression."
                          | (some (loc.ns [some n]), none) := do e ← get_local n, 
                                                                 rename_var_at_hyp old new e
                          | _ := rename_var_at_goal old new
                          end
| (We_args.oubli l) := clear_lst l
| (We_args.reforml n pe) := do h ← get_local n, e ← to_expr pe, change_core e (some h)
| (We_args.push_negation n new) := do interactive.push_neg (loc.ns [n]),
                              match (n, new) with
                              | (some hyp, some stuff) := do e ← get_local hyp,
                                                             enewhyp ← to_expr stuff,
                                                             infer_type e >>= unify enewhyp
                              | (none, some stuff) := fail "You can't use \"which becomes\" when pushing negations in the goal."
                              | _ := skip
                              end

/-- Obtain new object, information or goal. -/
meta def By : parse By_parser → tactic unit
| (By_args.obtenir fait args news) := focus1 (do
    news.mmap' (λ p : maybe_typed_ident, check_name p.1),
    efait ← to_expr fait,
    aplied ← mk_mapp_pexpr efait args,
    if news.length = 1 then do { -- Case where there is nothing to desctruct
         nom ← match news with
         | ((nom, some new) :: t) := do enew ← to_expr new, 
                                        infer_type aplied >>= unify enew,
                                        pure nom
         | ((nom, none) :: t) := pure nom
         | _ := fail "You need to give a name for the obtained information." -- shouldn't happen
         end,
         hyp ← note nom none aplied,
         cleanup_a_bit,
         news.mmap' verifie_type }
    else do tactic.rcases none (to_pexpr $ aplied)
                  $ rcases_patt.tuple $ news.map rcases_patt_of_maybe_typed_ident, 
            cleanup_a_bit )
| (By_args.choisir fait args news) := focus1 (do
    efait ← to_expr fait,
    aplied ← mk_mapp_pexpr efait args,
    tactic.choose tt aplied (news.map prod.fst),
    cleanup_a_bit,
    news.mmap' verifie_type)
| (By_args.appliquer fact args goals) := focus1 (do 
    efact ← to_expr fact, 
    eargs ← elab_args args, 
    egoals ← goals.mmap to_expr,
    mk_mapp_pexpr efact args >>= tactic.apply,
    actual_goals ← get_goals, 
    let pairs := list.zip actual_goals goals,
    focus' (pairs.map (λ p : expr × pexpr, do 
       `(force_type %%p _) ←  i_to_expr_no_subgoals ``(force_type %%p.2 %%p.1), skip))
    <|> fail "This isn't what needs to be proven.")

/-- Finish the proof. -/
meta def «This» (q : parse This_parser) : tactic unit :=
do tgt : expr ← target,
   match q with
   | (e, some args) := do 
                        eargs ← elab_args args,
                        let peargs := eargs.map (λ e, to_pexpr e), 
                        ee ← to_expr e, 
                        q ← mk_mapp_pexpr ee peargs, 
                        i_to_expr_strict ``(%%q : %%tgt) >>= tactic.exact
   | (e, none) := i_to_expr_strict ``(%%e : %%tgt) >>= tactic.exact
   end

private meta def assume_core (n : name) (ty : pexpr) :=
do check_name n,
   t ← target,
   when (not $ t.is_pi) whnf_target,
   t ← target,
   when (not $ t.is_arrow) $
     fail "There is nothing to assume here, the goal is not an implication.",
   ty ← i_to_expr ty,
   unify ty t.binding_domain,
   intro_core n >> skip

/-- Introduce an assumption when the goal is an implication, or initiate a 
proof by contradiction. -/
meta def Assume : parse Assume_parser → tactic unit
| (Assume_args.regular le) := do le.mmap' (λ b : pexpr, 
                               assume_core b.local_pp_name b.local_type)
| (Assume_args.absurd n hyp) := do 
    by_contradiction n, 
    try (interactive.push_neg (loc.ns [n])),
    when hyp.is_some (do 
                         Hyp ← hyp >>= to_expr,
                         let sp := simp_arg_type.symm_expr ``(exists_prop),
                         tactic.try (interactive.simp_core {} skip tt [sp] [] $ loc.ns [n]),
                         ehyp ← get_local n,
                         change_core Hyp (some ehyp))

/--
Add an intermediate statement (and prove it immediately if `by` is used).
-/
meta def Fact : parse Fact_parser → tactic unit
| (n, enonce, some prf) := do check_name n,
                              eenonce ← i_to_expr enonce,
                              assert n eenonce,
                              conclude_tac prf []
                              
| (n, enonce, none) := do check_name n,
                          i_to_expr enonce >>= tactic.assert n,
                          skip

/-- Define a new object. -/
meta def Set : parse Set_parser → tactic unit
| (Set_args.mk n t b)  := tactic.interactive.set none n t () b (some (ff, mk_simple_name $ n.to_string ++ "_def"))

end tactic.interactive
