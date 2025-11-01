import Lean

abbrev Name := String

abbrev Env := Std.HashMap Name Nat
abbrev InScopeVars := Std.HashSet Name

open Std

-- First some helpers for common things

/-- Attaching _x to a name makes it longer -/
@[simp,grind.]
theorem name_grows {nm:Name} : nm.length < (nm ++ "_x").length := by
  have h3: "_x".length = 2 := by rfl
  simp[*]

/-- Attaching "_x" to a name doesn't preserve equality -/
@[simp]
theorem name_append_neq : (x = y ++ "_x") → ¬ x = y := by
  intro append
  have _ : x = y → x.toList = y.toList := by exact fun a => congrArg String.toList a
  cases Classical.em (¬ x = y) with
    | inl neq => exact neq
    | inr eq =>
        have h_1 : y ++ "_x" = x := by grind
        have h_2 : (y ++ "_x").length = y.length + "_x".length := by simp[String.length_append]
        have h_3 : y.length < (y ++ "_x").length := by exact name_grows
        have h_4 : y.length ≠ (y ++ "_x").length := by exact Nat.ne_of_lt h_3
        have h_5 : y.length = (y ++ "_x").length := by simp_all
        solve_by_elim

/-- Attaching "_x" to a name doesn't preserve equality -/
@[simp]
theorem name_append_neq2 : (x = y ++ "_x") → ¬ x = y := by
  intro append
  have _ : x = y → x.toList = y.toList := by exact fun a => congrArg String.toList a
  if h: ¬ (x = y)
    then exact h
    else
        have h_1 : y ++ "_x" = x := by grind
        have h_2 : (y ++ "_x").length = y.length + "_x".length := by simp[String.length_append]
        have h_3 : y.length < (y ++ "_x").length := by exact name_grows
        have h_4 : y.length ≠ (y ++ "_x").length := by exact Nat.ne_of_lt h_3
        have h_5 : y.length = (y ++ "_x").length := by simp_all
        solve_by_elim

/-- Empty set as shown by size=0 has no members -/
@[simp,grind.]
theorem emptySet_not_mem {x} {s : InScopeVars}: s.size = 0 → x ∉ s := by
    intro sz_zero
    have h1 : s.size == 0 := by exact beq_iff_eq.mpr (by exact sz_zero)
    have h3 : x ∉ s := by exact HashSet.not_mem_of_isEmpty h1
    simp[h3]

def findName (n:Nat) (fvs: InScopeVars) (try_name:Name) (h_sz: n = fvs.size): (Name) :=
      if n_zero: n = 0 then
        have _h1 : fvs.size == 0 := by rw[← h_sz]; simp[n_zero]
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

/- findName takes in a name suggestion, and variables in scope.
   It returns a name not yet in scope.
-/
def findFreshName (fvs:InScopeVars) (try_name:Name) : Name :=
  findName (fvs.size) fvs try_name (by rfl)

/-- If the suggested name is not in scope it will be used. -/
theorem findName_not_elem_eq_try : try_name ∉ fvs → (findName n fvs try_name h_sz = try_name) := by
  fun_induction findName with
    | case1 _ _a _ =>
        simp_all
    | case3 => simp_all
    | case2 fvs try_name elem_fvs fvs2 next_try_name sz_not_zero
            sz2 i_hyp  =>
        have h1: next_try_name = try_name ++ "_x" := by rfl
        have h2: ¬ next_try_name = try_name := by exact name_append_neq h1
        simp_all

/-- Either the suggestion wasn't in scope and we just use it,
    Or we pick a new name that is:
      * Not what the user suggested.
      * Longer than the suggestion.
      * "Fresh" (Not in scope already)
      * Since the original suggestion was in scope
     -/
@[simp,grind.]
theorem findName_given_or_longer:
      (findName n fvs try_name h_sz = f_name) →
      (try_name ∉ fvs ∨
          (f_name ≠ try_name ∧
           f_name.length > try_name.length ∧
           f_name ∉ fvs ∧
           try_name ∈ fvs)) := by
  intro f_name_result
  cases Classical.em (try_name ∉ fvs) with
    | inl try_not_elem_fvs =>
      -- argument used, was not in scope
      fun_induction findName <;> simp[try_not_elem_fvs]

    | inr nn_try_name_elem_fvs =>
      have try_name_elem_fvs : try_name ∈ fvs := by simp_all

      fun_induction findName with
        |case1 fvs try_name _ sz_0 h_empty =>
            have h_not_contains : fvs.contains try_name = false := by refine HashSet.contains_of_isEmpty h_empty
            have h_not_elem_fvs : try_name ∉ fvs := by simp_all

            contradiction --fvs are empty / in set

        |case3 => contradiction -- in fvs/not in fvs

        |case2 fvs try_name h_try_name_elem fvs2 next_try_name sz_fv sz2_fv ind_h  =>
            have _ : try_name ∈ fvs := by simp[*]
            have _ : fvs2 = (HashSet.erase fvs try_name) := by grind
            have h2 : (HashSet.erase fvs try_name).size = fvs2.size := rfl
            have h_pc : findName (HashSet.size fvs - 1 ) fvs2 next_try_name sz2_fv = f_name := by grind
            have h_ind_facts: ¬next_try_name      ∈ fvs2 ∨
                                                      f_name ≠ next_try_name ∧
                                                      f_name.length > next_try_name.length ∧
                                                      f_name ∉ fvs2 := by grind

            cases Classical.em (¬next_try_name ∈ fvs2) with
              |inl next_not_elem =>
                  have h_1 : ¬next_try_name      ∈ fvs2 := by exact next_not_elem
                  have h_2: next_try_name = try_name ++ "_x" := by rfl
                  have h_3: ¬ next_try_name = try_name := by exact name_append_neq h_2
                  have h_5 : next_try_name      ∉  fvs2 := by exact next_not_elem

                  simp_all

                  have h3 : f_name = next_try_name := by
                    rw[← h_pc]
                    exact findName_not_elem_eq_try (by grind)
                  have h8 : next_try_name = String.append try_name "_x" := by rfl
                  have h8 : next_try_name = try_name ++ "_x" := by rfl
                  have h9 : next_try_name ≠ try_name := by exact name_append_neq h8
                  have h9 : f_name ≠ try_name := by simp_all
                  have h10 : ¬ f_name = try_name := by simp_all
                  simp[h10]

                  -- String.length try_name < String.length f_name := by sorry
                  have h11 : try_name.length < (try_name ++ "_x").length := by exact name_grows
                  have h12: f_name = (try_name ++ "_x") := by simp[*]
                  have h13 : try_name.length < f_name.length := by rw [h12]; exact name_grows
                  simp[h13]
                  grind

              |inr next_not_elem =>
                  -- the recursive case!
                  have h1 : f_name ≠ next_try_name ∧ String.length f_name > next_try_name.length := by grind
                  have h2 : next_try_name = try_name ++ "_x" := by rfl
                  have h3 : f_name.length > next_try_name.length := by simp_all
                  have h4 : try_name.length < (try_name ++ "_x").length := by exact name_grows
                  have h5 : try_name.length < next_try_name.length := by exact name_grows
                  have h6 : next_try_name.length < f_name.length := by exact h3
                  have h7 : try_name.length < f_name.length := by exact Nat.lt_trans h4 h3
                  have h8 : try_name ≠ f_name := by grind
                  have h9 : f_name ≠ try_name := by grind
                  have h10 : ¬ f_name = try_name := by grind

                  simp [h_try_name_elem, h10,h7]
                  have h11 : ¬ f_name ∈ fvs := by grind

                  simp[h11]

-- theorem findName_fresh: (findName n fvs try_name h_sz = f_name) → (f_name ∉ fvs) := by
theorem findName_fresh: (findName n fvs try_name h_sz = f_name) → (f_name ∉ fvs) := by
  intro name_result
  have _ : (try_name ∉ fvs ∨
            (f_name ≠ try_name ∧
            f_name.length > try_name.length ∧
            f_name ∉ fvs ∧
            try_name ∈ fvs)) := by exact findName_given_or_longer name_result
  cases Classical.em (try_name ∉ fvs) with
    |inl n_elem =>
      have h2: (findName n fvs try_name h_sz = try_name) := by exact findName_not_elem_eq_try n_elem
      have h3 : f_name = try_name := by grind
      simp_all
    |inr =>
      have h2: (f_name ≠ try_name ∧
            f_name.length > try_name.length ∧
            f_name ∉ fvs ∧
            try_name ∈ fvs) := by grind
      simp[h2]
