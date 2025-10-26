import Lean

abbrev Name := String

abbrev Env := Std.HashMap Name Nat
abbrev InScopeVars := Std.HashSet Name

open Std

-- The expression is valid in the given scope
inductive Expr: (scope:InScopeVars) -> Type where
  | lit {scope} : Nat -> Expr scope
  | e_op {scope} : (Nat->Nat->Nat) -> Expr scope -> Expr scope -> Expr scope
  | e_let {scope} : (n:Name) -> Expr scope -> Expr (scope.insert n) -> Expr scope
  | e_var {scope} : (n:Name) -> (n ∈ scope) -> Expr scope

def myExpr : Expr (HashSet.ofList ["x"]):= Expr.e_var "x" (by exact HashSet.mem_ofList.mpr rfl)

def myClosedExpr: Expr (HashSet.emptyWithCapacity) := Expr.e_let "x" (Expr.lit 42) (.e_var "x" (by exact HashSet.mem_insert_self))

theorem names_in_keys_in_env {names: InScopeVars} {env: Env}: names.toList ⊆ Std.HashMap.keys env → (k ∈ names →  k ∈ env)
  := by
    intro names_ss_keys
    intro x_elem_names
    have h1 : k ∈ names.toList := by exact HashSet.mem_toList.mpr x_elem_names
    -- have h2 : k ∈ env.keys := by exact names_ss_keys h1
    exact HashMap.mem_of_mem_keys (names_ss_keys h1)

abbrev HM := Std.HashMap

theorem hm_mem_insert_mem {names:InScopeVars} {env:Env} :
                          (names.toList ⊆ Std.HashMap.keys env) → ((names.insert k).toList ⊆ (Std.HashMap.insert env k v).keys) :=
  by
    intro ss_env
    have s1 {e} : (e ∈ env) → (e ∈ (env.insert k v)) := by intro elem_env ;simp[elem_env]
    have s2 {e}: (e ∈ env.keys) → (e ∈ (env.insert k v).keys) := by grind
    grind

def eval {names:InScopeVars} (expr : Expr names) (env : Env) (names_in_env: names.toList ⊆ Std.HashMap.keys env): Nat :=
  match expr with
    | .lit n => n
    | .e_op op l r =>
        let l2 : Nat := (eval l env names_in_env)
        let r2 : Nat := (eval r env names_in_env)
        op l2 r2
    | .e_let n rhs body =>
        let val := (eval rhs env names_in_env)
        let body_env := Std.HashMap.insert env n val
        let body_names := names.insert n
        let body': Expr body_names := body
        have h_scoped: body_names.toList ⊆ body_env.keys := by
            apply hm_mem_insert_mem names_in_env

        eval body' body_env (h_scoped)
    | .e_var n h =>
        have name_mem: n ∈ env := by exact names_in_keys_in_env names_in_env h
        env[n]


-- def addFvs
--             (expr: Expr scope_in)
--             (h_ss_in: scope_in ⊆ scope_out)
--             : Expr scope_out
--             :=
--     match expr with
--     | .lit n => .lit n
--     | .e_op op l r => .e_op op (addFvs l h_ss_in) (addFvs r h_ss_in)
--     | .e_let bndr e_rhs e_body => .e_let bndr (addFvs e_rhs h_ss_in) (addFvs e_body h_ss_in)
--     | .e_var v h_in_scope => .e_var v (by simp[h_in_scope, h_ss_in])

-- def inlineVar {scopeRhs: InScopeVars} {scopeBody: InScopeVars}
--               (name:Name)
--               (rhs:Expr [])
--               (body:Expr [name])
--               -- name will no longer be free after inlining
--               (h_rhs_fv: True)
--               : Expr [] :=
--   match body with
--     | .lit n => .lit n
--     | .e_op op l r => .e_op op (inlineVar name rhs l h_rhs_fv) (inlineVar name rhs l h_rhs_fv)
--     | .e_let n let_rhs let_body =>
--         sorry
--         -- if n == name
--         --   then .e_let n let_rhs let_body --shadowing
--         --   else .e_let n (inlineVar name rhs let_rhs fv_h) (inlineVar name rhs let_body fv_h)
--     | .e_var n h =>
--         if is_name: n == name
--             then
--                 rhs
--             else
                -- _


#eval eval myClosedExpr Std.HashMap.emptyWithCapacity (by simp)
-- def myVal : Expr := .plus (.lit 42) (.lit 1)

-- #eval eval myVal

-- theorem expr_comm_pls :
--   eval ( .plus l r ) = eval ( .plus r l) := by
--     simp[eval]
--     exact Nat.add_comm (eval l) (eval r)

-- theorem expr_dist : eval ( .mul a (.plus b c)) = eval ( (Expr.mul a b).plus (.mul a c)) := by
--   simp[eval]
--   exact Nat.mul_add (eval a) (eval b) (eval c)
