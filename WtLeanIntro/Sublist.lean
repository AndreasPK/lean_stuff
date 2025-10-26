import Lean

set_option trace.Elab.info true
-- set_option diagnostics true

def filter (p : a → Prop) [DecidablePred p] (xs : List a) : List a :=
  match xs with
  | [] => []
  | y :: ys => if p y then y :: filter p ys else filter p ys

inductive All {a : Type} (p : a → Prop) : List a → Prop where
  | nil  : All p []
  | cons {x : a} : p x → All p xs → All p (x :: xs)

inductive Sublist {a : Type} : List a → List a → Prop where
  | nil : Sublist [] []
  | skip : Sublist xs ys → Sublist xs (_ :: ys)
  | pick {x : a} : Sublist xs ys → Sublist (x :: xs) (x :: ys)

theorem filter_true {p:(a->Prop)} (h: (p x = True)) [DecidablePred p]:
                              filter p (x::xs) = x :: (filter p xs) :=
  by induction xs with
    | nil => calc
        filter p (x::[]) = [x]                  := by simp[filter,h]
        _                = x :: (filter p [])   := by simp[filter]
    | cons x xs tail_hy => simp[filter,h]

theorem filter_false {p:(a->Prop)} (h: (p x = False)) [DecidablePred p]:
                              filter p (x::xs) = (filter p xs) :=
  by simp[filter,h]


theorem filter_sublist {a} (p : a → Prop) (xs : List a) [DecidablePred p] :
  Sublist (filter p xs) xs :=
  by
    induction xs with
      | nil =>
          have s1 : filter p [] = [] := by rfl
          have s2 : Sublist (filter p []) [] = Sublist (a := a) [] [] := by rw[s1]
          simp[s2, Sublist.nil]

      | cons x xs tail_hyp =>
          have tail : Sublist (filter p xs) xs := by exact tail_hyp
          let ys := filter p xs
          unfold filter
          split
          case cons.isTrue p_true =>
            have s1 : Sublist ys xs := by simp[ys,tail_hyp]
            have s2: Sublist (x::ys) (x::xs) := by simp[s1,Sublist.pick]
            exact s2

          case cons.isFalse p_false =>
            have s1 : Sublist ys xs := by simp[ys,tail_hyp]
            have s2: Sublist (ys) (x::xs) := by simp[s1,Sublist.skip]
            exact s2

theorem filter_all (p : a → Prop) (xs : List a) [DecidablePred p] :
  All p (filter p xs) :=
  by induction xs with
    | nil => simp[All.nil, filter]
    | cons x xs tail_h =>
      if p_true: (p x)
        then
          have s2 : p x = True := by simp[p_true]
          have s1 : filter p (x::xs) = x :: (filter p xs) := by rw[filter_true s2]
          have s3 : All p (x :: filter p xs) := by exact All.cons p_true tail_h
          simp[s1, s3]

        else simp[p_true, tail_h,filter]

theorem mem : x ∈ xs → x ∈ (y::xs) := by exact fun a => List.mem_cons_of_mem y a

theorem filter_complete {a} (p : a → Prop) (x : a) (xs : List a) [DecidablePred p] :
  p x → x ∈ xs → x ∈ filter p xs :=
  if p_true : (p x)
    then
      by  simp[p_true]
          exact fun is_elem =>
            by induction is_elem with
              | head xs2 =>
                  have s1 : filter p (x :: xs2) = x :: (filter p xs2) := by simp[filter_true,p_true]
                  have s2 : x ∈ (filter p (x::xs2)) := by simp[s1]
                  exact s2
              | tail b mem_tail a_hyp =>
                  expose_names
                  if p2 : (p b)
                    then
                      have p3 : p b = True := by simp[p2]
                      have s1 : filter p (b :: as) = b :: (filter p as) := by exact filter_true p3
                      have s2 : x ∈ b :: (filter p as) := by exact mem a_hyp
                      simp[s1,s2]
                    else

                      -- have s3 : p b = False := by simp[p2]
                      -- have s1 : filter p (b :: as) = (filter p as) := by exact filter_false s3
                      have s2 : x ∈ filter p (as) → x ∈ filter p (b :: as) := by simp[filter,p2]
                      exact s2 a_hyp
                    --   simp[s1,s2]


  else by exact fun a_1 a_2 => False.elim (p_true a_1)
