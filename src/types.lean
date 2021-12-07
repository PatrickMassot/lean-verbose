import tactic.interactive_expr

import common

open tactic interactive

@[derive has_reflect]
inductive intro_rel
| lt | gt | le | ge | mem

@[derive has_reflect]
meta inductive introduced
| typed (n : name) (e : pexpr) : introduced
| bare (n : name) : introduced
| related (n : name) (rel : intro_rel) (e : pexpr) : introduced

-- Les deux fonctions suivantes sont en chantier, le but était de permettre d'utiliser introduced
-- aussi dans on obtient

meta def introduced.related_hyp (n : name) (rel : intro_rel) (pe : pexpr) : pexpr :=
match rel with
| intro_rel.lt  := ```(n < %%pe)
| intro_rel.gt  := ```(n > %%pe)
| intro_rel.le  := ```(n ≤ %%pe)
| intro_rel.ge  := ```(n ≥ %%pe)
| intro_rel.mem := ```(n ∈ %%pe)
end

meta def introduced.related_hyp_name (n : name) (rel : intro_rel) (pe : pexpr) : name :=
if pe = ``(0) then
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
   end


meta def rcases_patt_list_of_introduced_list : list introduced → list rcases_patt
| (introduced.typed n pe :: tail) := 
    (rcases_patt.typed (rcases_patt.one n) pe) :: rcases_patt_list_of_introduced_list tail 
| (introduced.related n rel pe :: tail) := []
| (introduced.bare n  :: tail) := 
    (rcases_patt.one n) :: rcases_patt_list_of_introduced_list tail 
|_ := []


@[derive has_to_format]
meta def maybe_typed_ident := name × option pexpr

meta def verifie_type : maybe_typed_ident → tactic unit
| (n, some t) := do n_type ← get_local n >>= infer_type,
                    to_expr t >>= unify n_type  
| (n, none) := skip

meta def rcases_patt_of_maybe_typed_ident : maybe_typed_ident → rcases_patt
| (n, some pe) := rcases_patt.typed (rcases_patt.one n) pe
| (n, none)    := rcases_patt.one n

@[derive has_reflect]
meta inductive By_args 
-- Par fait (appliqué à args) on obtient news (tel que news')
| obtenir (fait : pexpr) (args : list pexpr) (news : list maybe_typed_ident) : By_args
-- Par fait (appliqué à args) on obtient news (tel que news')
| choisir (fait : pexpr) (args : list pexpr) (news : list maybe_typed_ident) : By_args
-- Par fait (appliqué à args) il suffit de montrer que buts
| appliquer (fait : pexpr) (args : list pexpr) (buts : list pexpr) : By_args 

@[derive has_reflect]
meta inductive We_args 
| exct_aply : pexpr → list pexpr → We_args -- On conclut par ... (appliqué à ...)
| aply : pexpr → We_args             -- On applique ...
| aply_at : pexpr → list pexpr → We_args  -- On applique ... à ...
| rwrite : interactive.rw_rules_t → option name → option pexpr → We_args           -- On remplace ... (dans ... (qui devient ...))
| rwrite_all : interactive.rw_rules_t → We_args -- On remplace ... partout
| compute_ : We_args                  -- On calcule
| compute_at : name → We_args        -- On calcule dans ...
| linar : list pexpr → We_args       -- On combine ...
| contrap (push : bool) : We_args    -- On contrapose (simplement)
| push_negation (hyp : option name) (new : option pexpr) : We_args   -- On pousse la négation (dans ... (qui devient ...))
| discussion : pexpr → We_args       -- On discute en utilisant ... [cases]
| discussion_hyp : pexpr → We_args       -- On discute selon que ... [by_cases]
| deplie : list name → We_args -- On déplie ...
| deplie_at : list name → loc → option pexpr → We_args -- On déplie ... dans ... (qui devient ...)
| rname : name → name → option loc → option pexpr → We_args -- On renomme ... en ... (dans ... (qui devient ...))
| oubli : list name → We_args -- pour clear
| reforml : name → pexpr → We_args -- pour change at

@[derive has_reflect]
meta inductive Assume_args
| regular : list pexpr → Assume_args
| absurd : name → option pexpr → Assume_args

@[derive has_reflect]
meta inductive Lets_args 
| but : pexpr → Lets_args    -- pour change
| temoin : pexpr → option pexpr → Lets_args -- pour use
| ex_falso : Lets_args       -- pour exfalso
| recur : name → pexpr → Lets_args       -- pour les récurrences

@[derive has_reflect]
meta structure Set_args := 
(name : name)
(typ :  option $ pexpr)
(body : pexpr)

