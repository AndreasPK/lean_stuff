import Lean

abbrev Name := String

abbrev Env := Std.HashMap Name Nat
abbrev InScopeVars := Std.HashSet Name

open Std

-- theorem term_fresh {n:Nat}: (n != 0) → (sizeOf n - 1 < sizeOf n) := by
--   intro h_succ
--   induction n with
--     | zero => simp[]
--               grind
--     | succ n h_n =>
--         simp

def findName (n:Nat) (fvs: InScopeVars) (try_name:Name) (h_sz: n = fvs.size): (Name) :=
      if n_zero: n = 0 then
        have _h1 : fvs.size == 0 := by rw[← h_sz]; simp[n_zero]
        -- have _h2 : fvs.isEmpty = (fvs.size == 0) := by
        --   exact Std.HashMap.isEmpty_eq_size_eq_zero
        have _empty_helper : fvs.isEmpty := by exact _h1

        try_name
      else
        if is_elem: try_name ∈ fvs
          then
            have sz2 : (n - 1 = (HashSet.erase fvs try_name).size)
                      := by simp[h_sz]
                            simp[Std.HashSet.size_erase,is_elem]
            let fvs2 := fvs.erase try_name
            let next_try_name := try_name.append "_x"
            findName (n-1) fvs2 next_try_name sz2
          else try_name
  termination_by n

theorem findName_fresh: (findName n fvs try_name h_sz = f_name) → ((f_name = try_name) → (f_name ∉ fvs)) := by
  intro fn
  intro name_eq
  fun_induction findName with
    | case1 h_sz_zero _ empty_hlp =>
        -- have h1: fvs.isEmpty := by exact empty_hlp
        (expose_names; exact HashSet.not_mem_of_isEmpty _h1)
    | case2 fvs try_name h_try_elem ind_fvs ind_fresh_name fvs_non_empty
        sz_erased
        i_h =>
            have h1: f_name ∉ fvs.erase try_name := by grind

        -- rw[name_eq]
        -- simp[h_try_elem]

    | case3 fvs try_name try_n_in _es => rw[name_eq]; simp[try_n_in]

def freshName (all_fvs: InScopeVars) : (Name × InScopeVars) :=
    let name := findName (all_fvs.size) all_fvs "x" (by exact rfl)
    (name,all_fvs.insert name)

theorem hs_size_erase_mem {try_name : Name} {fresh_name:Name} {m:InScopeVars}
    : ((m.erase try_name).size = m.size - 1)
    → (try_name ∈ m)
    → (fresh_name ∉ m.erase try_name)
    → (fresh_name ∉ m)
    := by intro h_sz
          intro h_k_mem
          intro h_x_n_mem
          have h1: (m.erase try_name).insert try_name = m := by sorry
          have h2: try_name ∉ m.erase try_name := by simp
          if h_eq: try_name = fresh_name
            then
              grind
            else
              grind

theorem find_fresh {sz try_name} {fvs:InScopeVars} {h_sz: sz = fvs.size} : (findName sz fvs try_name h_sz) ∉ fvs := by
  fun_induction findName with
    | case1 fv2 try_name h_sz =>
        have h1 : fv2.size == 0 := by exact beq_iff_eq.mpr h_sz
        -- have h2 : fv2.isEmpty := by exact h1
        have h3 : try_name ∉ fv2 := by exact HashSet.not_mem_of_isEmpty h1
        exact h3
    | case2 fv2 try_name h_try_name_elem
            h_size_not_null
            h_sz_smaller
            h_ind
             =>
        let fresh_name := findName (HashSet.size fv2 - 1) (HashSet.erase fv2 try_name) (String.append try_name "_x") h_sz_smaller
        have h1: findName (HashSet.size fv2 - 1) (HashSet.erase fv2 try_name) (String.append try_name "_x") h_sz_smaller = fresh_name := by rfl
        rw[h1]
        have simp_h_ind : (fresh_name ∉ (HashSet.erase fv2 try_name)) := by simp[h_ind,h1,fresh_name]

        -- have h2: fresh_name ≠ try_name := by



    | case3 => sorry

-- theorem fresh_fresh {scope:InScopeVars} : ((freshName scope).fst) ∉ scope := by
--   fun_induction findName with

theorem fresh_contains_new {scope:InScopeVars} :
      (freshName scope) = expanded → ((expanded.fst ∈ expanded.snd) ) := by
  sorry

theorem fresh_not_contains_old {scope:InScopeVars} :
      (freshName scope) = expanded → ((expanded.fst ∉ scope) ) := by
  sorry
