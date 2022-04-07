/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tactic

namespace tactic
setup_tactic_parser

meta def cleanup_a_bit : tactic unit := 
do try `[dsimp only at * { eta := false, beta := true }],
   try `[simp only [exists_prop] at *]

def force_type (p : Sort*) (x : p) := p

meta def check_name (n : name) :=
success_if_fail (do hyp ← get_local n, skip) <|> 
fail ("The name " ++ n.to_string ++ " is already used.")

meta def mk_mapp_pexpr_aux : expr → expr → list pexpr → tactic expr
| fn (expr.pi n bi d b) (a::as) :=
do a ← to_expr a,
   infer_type a >>= unify d,
   fn ← head_beta (fn a),
   t ← whnf (b.instantiate_var a),
   mk_mapp_pexpr_aux fn t as
| fn _ [] := pure fn
| fn _ _ := fail "Too many arguments"

/-- Apply an expression to a pre-expressions list. -/
meta def mk_mapp_pexpr (fn : expr) (args : list pexpr) : tactic expr :=
do t ← infer_type fn >>= whnf,
   mk_mapp_pexpr_aux fn t args

/-- Apply an pre-expression to a pre-expressions list. -/
meta def pexpr_mk_app : pexpr → list pexpr → pexpr
| e []      := e
| e (x::xs) := pexpr_mk_app (e x) xs


meta def apply_arrow_to_hyp (e : pexpr) (hyp : expr) : tactic unit :=
do {
  t ← infer_type hyp,
  e_expr ← to_expr e,
  e_type ← infer_type e_expr,
  e_is_prop ← is_prop e_type,
  if e_is_prop then do
    prf ← interactive.mk_mapp' e_expr [hyp],
    clear hyp,
    hyp ← note hyp.local_pp_name none prf,
    cleanup_a_bit
  else do
    prf ← match t with
    | `(%%l = %%r) := do
          ltp ← infer_type l,
          mv ← mk_mvar,
          to_expr ``(congr_arg (%%e : %%ltp → %%mv) %%hyp)
    | _ := fail ("failed to apply " ++ to_string e ++ " at " ++ to_string hyp.local_pp_name)
    end,
    clear hyp,
    hyp ← note hyp.local_pp_name none prf,
    cleanup_a_bit
}

@[interactive]
meta def apply_arrow (q : parse texpr) (locs : parse location) 
  : tactic unit :=
match locs with
| (loc.ns l) := l.mmap' $ option.mmap $ λ h, get_local h >>= apply_arrow_to_hyp q
| wildcard   := local_context >>= list.mmap' (apply_arrow_to_hyp q)
end

example (P Q R : Prop) (h : P → Q) (h' : P) : Q :=
begin
  apply_arrow h at h',
  exact h',
end

example (f : ℕ → ℕ) (a b : ℕ) (h : a = b) : f a = f b :=
begin
  apply_arrow f at h,
  exact h
end

/-- If `e` is a conjunction then split it and return the corresponding two elements list. 
  Otherwise return `[e]`. -/
meta def split_and (e : expr) : tactic (list expr) :=
do e_type ← infer_type e >>= whnf,
   match e_type with
   | `(%%P ∧ %%Q) := do l ← tactic.cases_core e,
                        pure (l.map (λ x : name × list expr × list (name × expr), x.2.1)).join
   | _ := pure [e]
   end

/- Split all conjunctions in the expressions list. -/
meta def split_ands (hyps : list expr) : tactic (list pexpr) :=
do l ← hyps.mmap (λ e : expr, if e.is_local_constant then split_and e else pure [e]),
   pure (l.join.map to_pexpr)

meta def conclude_tac (pe : pexpr) (args : list pexpr) : tactic unit :=
focus1 (do
  let pprf := pexpr_mk_app pe args,
  tgt ← target,
  (i_to_expr_strict ``(%%pprf : %%tgt) >>= exact) <|>
  linarith ff tt [pprf] <|> 
  do { proof ← to_expr pprf, 
       split_ands [proof] >>= linarith ff tt <|> 
       apply proof >> done } <|>
  fail "This does not conclude.")

meta def intro_obj (n : name) : tactic expr :=
do t ← target,
   if expr.is_pi t ∨ expr.is_let t then do 
     e ← intro_core n,
     t ← infer_type e,
     mwhen (is_prop t) failed,
     pure e
   else do
     whnf_target,
     e ← intro_core n, 
     t ← infer_type e,
     mwhen (is_prop t) failed,
     pure e

meta def elab_args (args : list pexpr) : tactic (list expr) :=
args.mmap tactic.to_expr >>= pure

meta def change_head_name (n : name) : tactic unit :=
do tgt ← target,
   match tgt with
   | (expr.pi old bi t b) := change_core (expr.pi n bi t b) none 
   | _ := skip
   end

end tactic
