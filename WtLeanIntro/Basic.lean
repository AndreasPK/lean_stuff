import Lean

namespace WtLeanIntro

def hello :String
  := "world"

def number: Nat := 42

#eval number
#check number
#check Nat
#check Type
#check Type 1

def aList := [1,2,3]

#eval aList[2]
#eval getElem aList 2 (by get_elem_tactic)

def double1 := fun n => n * 2

def double2 : Nat -> Nat :=
  λ n => n * 2

def double3 (n:Nat) : Nat
  := n * 2

#print double3

def foo := (42 : Nat)
def bar := (foo -2 : Int)

inductive Tree (a : Type) where
  | leaf : a -> Tree a
  | node : Tree a -> Tree a -> Tree a

def myTree : Tree Nat := Tree.node (Tree.leaf 42) (.leaf 41)

def size1 {a} (t : Tree a) : Nat :=
  sorry

def size2 {a} (t : Tree a) : Nat := size1 t

def mul {a : Type}  [mulDict : HMul a a a] (x:a) (y:a) :a := x*y

def size3 (t:Tree a) : Nat :=
  match t with
  | .leaf _ => 1
  | .node l r => size3 l + size3 r

def size4 {a:Type} : Tree a -> Nat
  | .leaf _ => 1
  | .node l r => (size4 l) + (size4 r)

def reverse : Tree a -> Tree a
  | .leaf x => .leaf x
  | .node l r => .node (reverse r) (reverse l)

#eval (size4 myTree)

def size {a:Type} : Tree a -> Nat
  | .leaf _ => 1
  | .node l r => (size l) + (size r)

example: size4 myTree = 2 := by rfl
example: size4 myTree = 2 := by decide

def choose (_x: a) (y: b) := by assumption
def choose1 (x: a) (_y: b) :a := by assumption
def choose2 (_x: a) (y: b) :b := by assumption

#check choose

theorem reverse_reverse {a} (t:Tree a) : reverse (reverse t) = t :=
  by induction t with
  -- | leaf x => rfl
  | leaf x => simp [reverse] --simplify proof, allow use of reverse implementation
  -- | node l r ihl ihr =>
  --   simp only [reverse]
  --   rw [ihl]
  --   rw [ihr]

  | node l r ihl ihr =>
    calc
      reverse (reverse (.node l r)) = .node (reverse (reverse l)) (reverse (reverse r)) := by simp[reverse]
      Tree.node (reverse (reverse l)) (reverse (reverse r)) = .node l (reverse (reverse r)) := by rw [ihl]
      Tree.node l (reverse (reverse r)) = Tree.node l r := by rw [ihr]

theorem reverse_reverse2 {a} (t:Tree a) : reverse (reverse t) = t :=
  match t with
    | Tree.leaf _ => by exact rfl
    | Tree.node l r =>
      have ihl : reverse (reverse l) = l := reverse_reverse2 l
      have ihr : reverse (reverse r) = r := reverse_reverse2 r
      have step1: reverse (reverse (.node l r)) = Tree.node (reverse (reverse l)) (reverse $ reverse r) := by simp[reverse]
      have step2: Tree.node (reverse (reverse l)) (reverse $ reverse r) = Tree.node (l) (r) :=
        by rw[ihl,ihr]
      show reverse (reverse $ Tree.node l r) = Tree.node l r from
        Eq.trans step1 step2
      -- sorry

theorem reverse_reverse3 {a} (t:Tree a) : reverse (reverse t) = t :=
  by induction t <;> grind [reverse]

theorem reverse_size {a} (t: Tree a) : size (reverse t) = size t
  := by induction t with
  | leaf x =>
        rfl
  | node l r lih rih =>
      calc
          size (reverse (Tree.node l r)) = size (Tree.node (reverse r) (reverse l)) := by simp[reverse]
          _ = size (reverse r) + size (reverse l) := by simp[size]
          _ = size r + size l := by rw[lih,rih]
          _ = size l + size r := by exact Nat.add_comm (size r) (size l)
          size l + size r = size (Tree.node l r) := by simp[size]

#check Functor

def mapTree {a b} (f : a -> b) (t: Tree a) : (Tree b) :=
  match t with
    | .leaf x => .leaf $ f x
    | .node l r => Tree.node (mapTree f l) (mapTree f r)

instance : Functor Tree where
  map := mapTree

#check LawfulFunctor

theorem id_map_tree (x : Tree a) : mapTree (fun a => a) x = x :=
  by induction x with
    | leaf x => rfl
    | node tree e_t a_id a_iht => simp[mapTree,a_id,a_iht]

#check comp_map

theorem comp_map_tree (g : a → b) (h : b → c) (x : Tree a) :
                                  mapTree (h ∘ g) x = mapTree h (mapTree g x) :=
  by induction x with
    | leaf => rfl
    | node tree ele a_1 a2 => simp[mapTree,a_1,a2]

instance : LawfulFunctor Tree where
  map_const := rfl
  id_map := id_map_tree
  comp_map := comp_map_tree


def treeToList {a:Type} (t: Tree a) : List a :=
  match t with
    | Tree.leaf x => [x]
    | Tree.node l r => treeToList l ++ treeToList r

#eval treeToList (Tree.node (.leaf 41) (.node (.leaf 42) (.leaf 43)))
#eval treeToList (Tree.node (.leaf [1]) (.leaf []))
#eval [[1],[2,3]].length
#check ite

theorem tree_list_size : size (t) = List.length (treeToList t) :=
  by induction t with
    | leaf => rfl
    -- | node t e a_t a_e =>
    | node l r a_t a_e =>
      have s1 : treeToList (l.node r) = treeToList l ++ treeToList r := by exact rfl
      simp[size,a_t,a_e,s1]

theorem min_tree : size (t : Tree a) > 0 :=
  by induction t with
    | leaf => simp[size]
    | node l r a1 a2 =>
        have s1 : size (Tree.node l r) = size l + size r := by simp[size]
        grind

-- def getElemTree {a:Type} (xs : Tree a) (i : Nat) (valid:size xs > i): a :=
--   if valid then (treeToList xs)[i] else sorry

#check getElem

def getTreeElem (t:Tree a) (n:Nat) (valid:n < size t): a :=
  have v_t : n < (treeToList t).length := by grind[tree_list_size]
  getElem (treeToList t) n v_t

-- theorem filter_complete (p : a -> Prop) (xs: List a)
-- getTreeLem


-- instance : GetElem (List α) Nat α fun as i => i < as.length where
--   getElem as i h := as.get ⟨i, h⟩
