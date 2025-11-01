import Lean

import WtLeanIntro.NameGen

theorem addList : (ys = (name :: xs)) → name ∈ ys := by
  intro app_h
  have s1 : name ∈ (name :: xs) := by exact List.mem_cons_self
  simp[s1,app_h]

theorem lem_insert_hm {env:Std.HashMap Name Nat} {name:Name} {x:Nat} :
                      (env = Std.HashMap.insert old_env name x) → (name ∈ env) := by
  intro upd_h
  simp[upd_h]

-- def foo := Std.HashMap.get
def addLet (env: Std.HashMap Name Nat) (name:Name) (val: Nat ) : Env :=
    Std.HashMap.insert env name val

def foo (env:Env) (name:Name) (val:Nat) : Nat :=
    let e2 := Std.HashMap.insert env name val
    have lem_el: name ∈ e2 := by exact lem_insert_hm rfl
    let r := e2[name]
    r
