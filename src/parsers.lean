/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tactic.interactive_expr

import types

namespace tactic.interactive
setup_tactic_parser

open tactic lean

precedence `apply`: 0
precedence `applied`: 0
precedence `to`: 0
precedence `it`: 0
precedence `we`: 0
precedence `is`: 0
precedence `obtain`: 0
precedence `that`: 0
precedence `works`: 0
precedence `prove`: 0
precedence `suffices`: 0
precedence `such`: 0
precedence `conclude`: 0
precedence `compute`: 0
precedence `combine`: 0
precedence `replace`: 0
precedence `everywhere`: 0
precedence `contrapose`: 0
precedence `simply`: 0
precedence `push`: 0
precedence `the`: 0
precedence `negation`: 0
precedence `discuss`: 0
precedence `on`: 0
precedence `depending`: 0
precedence `rename`: 0
precedence `reformulate`: 0
precedence `forget`: 0
precedence `unfold`: 0
precedence `which`: 0
precedence `becomes`: 0
precedence `for`: 0
precedence `contradiction`: 0
precedence `find`: 0
precedence `it's`: 0
precedence `contradictory`: 0
precedence `choose`: 0
precedence `induction`: 0

meta def parse_intro_rel : lean.parser intro_rel :=
intro_rel.lt <$ tk "<" <|>
intro_rel.gt <$ tk ">" <|>
intro_rel.le <$ tk "≤" <|>
intro_rel.le <$ tk "<=" <|>
intro_rel.ge <$ tk "≥" <|>
intro_rel.ge <$ tk ">=" <|>
intro_rel.mem <$ tk "∈"

meta def intro_parser : lean.parser introduced :=
do n ← ident,
   (introduced.typed n <$> (tk ":" *> texpr)) <|>
   (introduced.related n <$> parse_intro_rel <*> texpr) <|>
   pure (introduced.bare n)

meta def bracketed_intro_parser : lean.parser introduced :=
with_desc "..." $
(brackets "(" ")" intro_parser) <|> intro_parser

meta def maybe_typed_ident_parser : lean.parser maybe_typed_ident :=
do { n ← (tk "(" *> ident), pe ← (tk ":" *> texpr <* tk ")"), return (n, some pe) } <|>
do { n ← ident,
     do { pe ← (tk ":" *> texpr), pure (n, some pe) } <|> pure (n, none) }

/-- Parse one or more new goals. -/
meta def buts_parser : lean.parser (list pexpr) :=
tk "it" *> tk "suffices" *> tk "to" *> tk "prove" *>  (tk "that")? *> pexpr_list_or_texpr

meta def on_obtient_parser : lean.parser (list maybe_typed_ident) :=
do { news ← tk "obtain" *> maybe_typed_ident_parser*,
     news' ← (tk "such" *> tk "that" *> maybe_typed_ident_parser*) <|> pure [],
     pure (news ++ news') }

/-- Parse a list of consequences for `choose`. -/
meta def on_choisit_parser : lean.parser (list maybe_typed_ident) :=
do { news ← tk "choose" *> maybe_typed_ident_parser*,
     news' ← (tk "such" *> tk "that" *> maybe_typed_ident_parser*) <|> pure [],
     pure (news ++ news') }

/-- Parse a (maybe empty) argument list. -/
meta def applied_to_parser :  lean.parser (list pexpr) :=
do { args ← tk "applied" *> tk "to" *> pexpr_list_or_texpr,
   proofs ← (tk "using" *> pexpr_list_or_texpr)?,
   pure $ match proofs with
   | some l := args ++ l
   | none := args
   end } <|> pure []

/-- Parser principal pour la tactique Par. -/
meta def By_parser : lean.parser By_args :=
with_desc "... (applied to ...) we obtain ... (such that ...) / By ... (applied to ...) it suffices to prove (that) ..." $
do e ← texpr,
   args ← applied_to_parser,
   do { _ ← tk "we",
       (By_args.obtenir e args <$> on_obtient_parser) <|>
       (By_args.choisir e args <$> on_choisit_parser) } <|>
   (By_args.appliquer e args <$> buts_parser)

meta def This_parser : lean.parser (pexpr × option _) :=
do q ← tk "is" *> texpr,
   oargs ← applied_to_parser?,
   pure (q, oargs)

meta def which_becomes_parser : lean.parser (option pexpr) := (tk "which" *> tk "becomes" *> texpr)?


/-- Parser for We tactic. -/
meta def We_parser : lean.parser We_args :=
with_desc "conclude by ... (applied to ...) / We apply ... (to ...) / We compute (at ...) / We replace ... (at ... (which becomes ...)) / We combine ... / We contrapose / We discuss depending on ... / We discuss using ... / We unfold ... (at ... (which becomes ...)) / We rename ... to ... (at ... (which becomes ...)) / We forget ... / We reformulate ... to ... / We push the negation (at ... (which becomes ...))" $
(We_args.exct_aply <$> (tk "conclude" *> tk "by" *> texpr) <*> applied_to_parser) <|>
(do { e ← tk "apply" *> texpr,
      We_args.aply_at e <$> (tk "to" *> pexpr_list_or_texpr) <|> pure (We_args.aply e)}) <|>
(tk "compute" *> (We_args.compute_at <$> (tk "at" *> ident) <|> pure We_args.compute_)) <|>
(We_args.linar <$> (tk "combine" *> pexpr_list_or_texpr)) <|>
do { rules ← tk "replace" *> interactive.rw_rules,
     We_args.rwrite_all rules <$ tk "everywhere" <|>
     We_args.rwrite rules <$> (tk "at" *> ident)? <*> which_becomes_parser } <|>
do { tk "contrapose",
     (We_args.contrap ff <$ tk "simply") <|>
     pure (We_args.contrap tt) } <|>
We_args.push_negation <$> (tk "push" *> tk "the" *> tk "negation" *> (tk "at" *> ident)?) <*> which_becomes_parser <|>
do { tk "discuss",
     We_args.discussion_hyp <$> (tk "depending" *> tk "on" *> texpr) <|>
     We_args.discussion <$> (tk "using" *> texpr) } <|>
do { ids ← tk "unfold" *> ident*,
     do { place ← tk "at" *> ident,
          We_args.deplie_at ids (loc.ns [place]) <$> which_becomes_parser } <|>
     pure (We_args.deplie ids) } <|>
do { old ← tk "rename" *> ident <* tk "to",
     new ← ident,
     do { place ← tk "at" *> ident,
          We_args.rname old new (loc.ns [place]) <$> which_becomes_parser } <|>
     pure (We_args.rname old new none none) } <|>
We_args.reforml <$> (tk "reformulate" *> ident <* tk "to") <*> texpr <|>
We_args.oubli <$> (tk "forget" *> ident*)

meta def Assume_parser : lean.parser Assume_args :=
with_desc "(that) ... / Assume for contradiction ..." $
do { _ ← tk "for", _ ← tk "contradiction",
     n ← ident,
     do { _ ← tk ":",
          hyp ← texpr,
          pure (Assume_args.absurd n (some hyp)) } <|>
     pure (Assume_args.absurd n none)} <|>
Assume_args.regular <$> ((tk "that")? *>parse_binders tac_rbp)

meta def Fact_parser : lean.parser (name × pexpr × option pexpr) :=
with_desc "... : ... (by ... (applied to ...))" $
do n ← ident <* tk ":",
   enonce ← texpr,
   do { dem ← tk "by" *> texpr,
        args ← applied_to_parser,
        pure (n, enonce, some (pexpr_mk_app dem args)) } <|>
   pure (n, enonce, none)

meta def Lets_parser : lean.parser Lets_args :=
with_desc "prove ... / Let's prove that ... works / Let's prove it's contradictory." $
do  tk "prove",
     (Lets_args.recur <$> ((tk "by" *> tk "induction") *> ident) <*> (tk ":" *> texpr)) <|>
     do { t ← (tk "that")?,
          e ← texpr,
          if t.is_some then (do { t ← tk "works",
               do { _ ← (tk ":"),
                    But ← texpr,
                    pure (Lets_args.temoin e $ some But) } <|> pure (Lets_args.temoin e none) } <|>
          pure (Lets_args.but e)) else pure (Lets_args.but e) }
    <|>
(Lets_args.ex_falso <$ (tk "it's" *> tk "contradictory"))

meta def Set_parser : lean.parser Set_args :=
with_desc "... (: ...) := ..." $
Set_args.mk <$> ident <*> ((tk ":") >> texpr)? <*> (tk ":=" *> texpr)

end tactic.interactive
