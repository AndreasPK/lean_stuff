import Lean

import Lean.Parser.Term
import Lean.Parser.Term.Basic
import Lean.Parser.Tactic

namespace WtLeanIntro

#check Lean.Syntax

open Lean

def foo : Nat -> Nat
  | 1 => (1 : Nat)
  | _ => 2

def isAdd11 : Syntax → Bool
  | `(Nat.add 1) => true
  | _ => false

-- def isAdd11 : Syntax → Bool
--   | `(Nat.add 1 1) => true
--   | _ => false

#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"]) -- true
#eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[mkIdent `foo, Syntax.mkNumLit "1"]) -- false

-- #eval isAdd11 (Syntax.mkApp (mkIdent `Nat.add) #[(Syntax.mkNumLit "1")])
-- #eval showTactic (myGrind (1:Nat))


syntax (name := add_ones_n ) "add_ones" : term

@[macro add_ones_n]
def sasdasdasd : Lean.Macro
  | `(add_ones) => `(1+1)
  | _ => Macro.throwUnsupported

-- syntax (name := by_steps_n ) "by_steps" : tactic
-- syntax (name := by_steps_n1 ) "by_steps" (term) : tactic
syntax (name := by_steps_many ) "by_steps" (term:lead)+ : tactic

set_option pp.explicit true
open Tactic

-- (Tactic.seq1
--  [(Tactic.simp "simp" (Tactic.optConfig []) [] [] [] [])
--   ";"
--   (Tactic.simpAll "simp_all" (Tactic.optConfig []) [] [] [])
--   ";"
--   (Tactic.grind "grind" (Tactic.optConfig []) [] [] [])])

-- def mahSyntax : TSyntax `tactic :=
def mkTacticSeq (tacs:List (TSyntax `tactic)) : TSyntax `tactic  :=
  let s_tacs := tacs.map TSyntax.raw
  let untyped_syn := Syntax.node (SourceInfo.none : SourceInfo) `Lean.Parser.Tactic.seq1 (List.toArray s_tacs)
  let t : TSyntax `tactic := TSyntax.mk untyped_syn
  t
  -- Tatic.seq1 sorry

@[macro by_steps_many]
def by_stepsImplMany : Lean.Macro
  | `(tactic | by_steps $t:term $ts:term*) => do
      -- let h1 : TSyntax `term := t
      -- let hs : List (TSyntax `term) := t :: ts.toList
      let mkHave (hyp:TSyntax `term) : MacroM (TSyntax `tactic)
            :=`(tactic| have _ : $hyp := by first | rfl | simp | simp[*] | grind )

      let args := t :: ts.toList
      let hyps : List (TSyntax `tactic) <- args.mapM mkHave

      -- causes "str" tactic not implemented error
      let s_hyps : TSyntax `tactic := TSyntax.mk $ Syntax.mkSep (hyps.map TSyntax.raw).toArray (Syntax.mkStrLit ";")
      dbg_trace s!"{s_hyps}"

      let s1 <- mkHave t
      pure s1

  | _ => Macro.throwUnsupported

-- #check by_stepsImplMany (Syntax.mkApp (mkIdent `by_steps) #[TSyntax.mk $ mkAtom "true"])

set_option pp.rawOnError true

-- #check expandMacro? (Syntax.mkApp (mkIdent `by_steps) #[TSyntax.mk $ mkAtom "true"])

-- def foob :=

theorem foo2 : 1 + 1 = 2 := by
  -- simp[]
  -- have _ : true = true := by grind
  by_steps
    (true = true)
    (true = true)
    -- grind


-- (Tactic.tacticHave__
--  "have"
--  (Term.letConfig [])
--  (Term.letDecl
--   (Term.letIdDecl
--    (Term.letId (Term.hole "_"))
--    []
--    [(Term.typeSpec
--      ":"
--      (Term.paren (Term.hygienicLParen "(" (hygieneInfo `[anonymous])) («term_=_» `true "=" `true) ")"))]
--    ":="
--    (Term.byTactic
--     "by"
--     (Tactic.tacticSeq
--      (Tactic.tacticSeq1Indented
--       [(Tactic.grind "grind" (Tactic.optConfig []) [] [] [])
--        ";"
--        (Tactic.tacticHave__
--         "have"
--         (Term.letConfig [])
--         (Term.letDecl
--          (Term.letIdDecl
--           (Term.letId `__a._@.WtLeanIntro.Tmp.1115644075._hygCtx._hyg.12)
--           []
--           [(Term.typeSpec
--             ":"
--             («term_=_»
--              `false._@.WtLeanIntro.Tmp.1115644075._hygCtx._hyg.12
--              "="
--              `true._@.WtLeanIntro.Tmp.1115644075._hygCtx._hyg.12))]
--           ":="
--           (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.tacticSorry "sorry")]))))))]))))))
