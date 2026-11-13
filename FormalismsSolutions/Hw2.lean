section Part1
-- Type of elements and its total order
variable {α : Type}
variable (leα : α → α → Bool)
local infix:50 " ≼ " => leα
axiom le_total (a b : α) : (a ≼ b) ∨ (b ≼ a)
axiom le_trans (a b c : α) : a ≼ b → b ≼ c → a ≼ c

-- Uninterpreted functions for sorting
opaque sort : List α → List α
opaque odd : List α → List α
opaque even : List α → List α
opaque merge : List α → List α → List α

-- Axioms

-- Correction! There were missing bases cases for `sort`
axiom A0 :
  sort ([] : List α) = []
axiom A0' (a : α) :
  sort ([a] : List α) = [a]

axiom A1 (a b : α) (x : List α) :
  sort (a :: b :: x) = merge (sort (odd (a :: b :: x))) (sort (even (a :: b :: x)))

axiom A2 :
  odd ([] : List α) = []

axiom A3 :
  even ([] : List α) = []

axiom A4 (a : α) (x : List α) :
  odd (a :: x) = a :: even x

axiom A5 (a : α) (x : List α) :
  even (a :: x) = odd x

axiom A6 (y : List α) :
  merge [] y = y

axiom A7 (a : α) (x : List α) :
  merge (a :: x) [] = a :: x

axiom A8 (a b : α) (x y : List α) :
  merge (a :: x) (b :: y) =
    if a ≼ b then a :: merge x (b :: y)
    else b :: merge (a :: x) y


-- Specification of `ordered`
opaque ordered : List α → Bool
axiom O1 :
  ordered ([] : List α)
axiom O2 (a : α) :
  ordered (a :: [])
axiom O3 (a b : α) (x : List α) :
  ordered (a :: b :: x) = (a ≼ b ∧ ordered (b :: x))

-- Specification of `permutation`
opaque permutation : List α → List α → Bool
axiom P1 :
  permutation ([] : List α) [] = true
axiom P2 (a : α) (x y z : List α) :
  permutation (a :: x) (y ++ a :: z) = permutation x (y ++ z)
axiom P3 (a : α) (x y : List α) (h : a ∉ y) :
  permutation (a :: x) y = false
-- Transitivity and symmetry is not provable and needs to be axiomatized.
-- Instead, I could add more axioms describing permutation to also describe what is NOT a permutation.
-- Here, we will just state the positive cases (+ P3).
axiom P4 (x y z : List α) : permutation x y -> permutation y z -> permutation x z
axiom P5 (x y : List α) : permutation x y = permutation y x


-- Theorem G1: every sorted input is ordered

-- If cons is ordered then so is the tail
include leα
theorem ordered_cons (a : α) (x : List α)
    (h : ordered (a :: x)) :
    ordered x := by
  cases x with
  | nil => rw [O1]
  | cons h t => rw [O3 leα] at h; exact h.2

-- If an element is before every element in the tail, we can order it
theorem ordered_head (a : α) (x : List α)
    (hx : ordered x) (h : ∀e ∈ x, a ≼ e) :
    ordered (a :: x) := by
  cases x with
  | nil => rw [O2]
  | cons b xs =>
    rw [O3 leα]
    exact ⟨h b (List.Mem.head _), hx⟩

-- If cons is ordered, the head is before any element in tail
theorem ordered_before (a e : α) (x : List α)
    (h : ordered (a :: x)) :
    e ∈ x → a ≼ e := by
  induction x generalizing a with intro hin
  | nil => contradiction
  | cons b xs ih =>
    rw [O3 leα] at h
    cases hin with
    | head => exact h.1
    | tail _ hmem => exact le_trans leα a b e h.1 (ih _ h.2 hmem)

-- If something is in a merge, it is either in the left or right
include leα
theorem merge_in (e : α) (x y : List α)
    (h : e ∈ merge x y) :
    e ∈ x ∨ e ∈ y := by
  induction x generalizing y with
  | nil =>
    rw [A6] at h
    exact Or.inr h
  | cons a xs ih_x =>
    induction y with
    | nil =>
      rw [A7] at h
      exact Or.inl h
    | cons b ys ih_y =>
      rw [A8 leα] at h
      split at h
      · cases h with
        | head => exact Or.inl (List.Mem.head _)
        | tail _ h2 =>
          rcases ih_x (b :: ys) h2 with h1 | h1
          · exact Or.inl (List.Mem.tail a h1)
          · exact Or.inr h1
      · cases h with
        | head => exact Or.inr (List.Mem.head _)
        | tail _ h2 =>
          rcases ih_y h2 with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (List.Mem.tail b h1)

-- Merging ordered lists gives an ordered list
include leα
theorem merge_ordered (x y : List α)
    (hx : ordered x) (hy : ordered y) :
    ordered (merge x y) := by
  -- double induction on both lists
  induction x generalizing y with
  | nil => rw [A6, hy]
  | cons a xs ih_x =>
    induction y with
    | nil => rw [A7, hx]
    | cons b ys ih_y =>
      rw [A8 leα]
      split
      case isTrue hab =>
        apply ordered_head leα
        · apply ih_x
          · exact ordered_cons leα (h:=hx)
          · exact hy
        · intro e hin
          rcases merge_in leα _ _ _ hin with hin | hin
          · apply ordered_before leα _ _ _ hx hin
          · apply ordered_before leα _ _ _ _ hin
            rw [O3 leα]
            constructor <;> assumption
      case isFalse hab =>
        -- since a ≼ b is not true and ≼ is a total order, then b ≼ a
        have hba : b ≼ a := by
          cases le_total leα a b with
          | inl h => contradiction
          | inr h => exact h
        apply ordered_head leα
        · apply ih_y
          exact ordered_cons leα (h:=hy)
        · intro e hin
          rcases merge_in leα _ _ _ hin with hin | hin
          · apply ordered_before leα _ _ _ _ hin
            · rw [O3 leα]; constructor <;> assumption
          · apply ordered_before leα _ _ _ hy hin

-- Relate the lengths of odd and even lists
omit leα
theorem odd_even_length (x : List α) : (even x).length + (odd x).length = x.length := by
  induction x with
  | nil => rw [A2, A3]; rfl
  | cons c xs ih => rw [A4, A5, List.length_cons, List.length_cons]; omega

include leα
theorem G1 (x : List α) : ordered (sort x) := by
  have ⟨n, hn⟩ : ∃n, x.length = n := exists_eq'
  -- we use strong induction on the length of the list
  induction n using Nat.strongRecOn generalizing x with
  | ind n ih =>
    -- if list is empty or a singleton, follows directly from axioms
    cases x with
    | nil => rw [A0, O1]
    | cons a x' =>
      cases x' with
      | nil => rw [A0', O2]
      | cons b xs =>
        rw [A1]
        -- we are merging two ordered lists
        apply merge_ordered leα
        -- the left is ordered
        · apply ih (m := (odd (a :: b :: xs)).length) <;> try rfl
          subst n
          rw (config := {occs := .pos [2]}) [<-odd_even_length]
          rw [A5]
          rw (config := {occs := .pos [2]}) [A4]
          rw [List.length_cons]
          omega
        -- the right is ordered
        · apply ih (m := (even (a :: b :: xs)).length) <;> try rfl
          subst n
          rw (config := {occs := .pos [2]}) [<-odd_even_length]
          rw [A4]
          rw [List.length_cons]
          omega


-- Theorem G2: every sorted input is a permutation of the input

-- Permutation is reflexive
omit leα
theorem permutation_rfl (x : List α) : permutation x x := by
  induction x with
  | nil => exact P1
  | cons a xs ih =>
    rw (config := {occs := .pos [2]}) [<-List.nil_append (a :: xs)]
    rw [P2]
    exact ih

-- We can pop the heads in a permutation
theorem permutation_cons (a : α) (l1 l2 : List α) :
  permutation (a :: l1) (a :: l2) = permutation l1 l2 := by
  rw [<-List.nil_append (a :: l2), P2]
  rfl

-- Merge is a permutation of append
include leα
theorem permutation_merge (x y : List α) : permutation (merge x y) (x ++ y) := by
  induction x generalizing y with
  | nil =>
    rw [A6]
    exact permutation_rfl _
  | cons a xs ih_x =>
    induction y with
    | nil =>
      rw [A7, List.append_nil]
      exact permutation_rfl _
    | cons b ys ih_y =>
      rw [A8 leα]
      split
      case isTrue =>
        -- heads are the same + IH
        rw [List.cons_append, permutation_cons, ih_x]
      case isFalse =>
        rw [P2, ih_y]


-- Append of x y is a permutation of append of y x
omit leα
theorem permutation_append (x y : List α) : permutation (x ++ y) (y ++ x) := by
  induction x generalizing y with
  | nil =>
    rw [List.append_nil, List.nil_append, permutation_rfl]
  | cons a xs ih =>
    rw [List.cons_append, P2, ih]

-- Append of odd even is a permutation of x
omit leα
theorem permutation_odd_even (x : List α) : permutation (odd x ++ even x) x := by
  induction x with
  | nil =>
    rw [A2, A3]
    exact P1
  | cons a xs ih =>
    rw [A4, A5, List.cons_append, <-List.nil_append (a :: xs), P2]
    exact P4 _ _ _ (permutation_append (even xs) (odd xs)) ih

-- Inversion lemma for the nil case
theorem permutation_nil_inv (x : List α)
    (h : permutation [] x) : x = [] := by
  cases x with
  | nil => rfl
  | cons a z =>
    rw [P5, P3] at h
    · contradiction
    · intro h
      contradiction

-- Inversion lemma for the step case
theorem permutation_cons_inv (a : α) (x w : List α)
    (h : permutation (a :: x) w) :
    ∃ u v, w = u ++ a :: v ∧ permutation x (u ++ v) := by
  by_cases ha : a ∈ w
  · obtain ⟨u, v, rfl⟩ := List.append_of_mem ha
    rw [P2] at h
    exact ⟨u, v, rfl, h⟩
  · rw [P3 _ _ _ ha] at h
    contradiction

-- Permutation is preserved under appends
omit leα
theorem permutation_append_preserve (x x' y y' : List α)
    (hx : permutation x x') (hy : permutation y y') : permutation (x ++ y) (x' ++ y') := by
  induction x generalizing x' y y' with
  | nil =>
    rw [permutation_nil_inv _ hx]
    exact hy
  | cons a xs ih =>
    obtain ⟨u, v, rfl, h_sub⟩ := permutation_cons_inv a xs x' hx
    rw [List.cons_append, List.append_assoc, List.cons_append, P2, <-List.append_assoc]
    exact ih _ _ _ h_sub hy

include leα
theorem G2 (x : List α) : permutation (sort x) x = true := by
  have ⟨n, hn⟩ : ∃ n, x.length = n := exists_eq'
  induction n using Nat.strongRecOn generalizing x with
  | ind n ih =>
    cases x with
    | nil => rw [A0, P1]
    | cons a xs =>
      cases xs with
      | nil => rw [A0', permutation_rfl]
      | cons b xs =>
        rw [A1]
        -- setup one big transitive
        have h_split := permutation_odd_even (a :: b :: xs)
        have h_odd := ih (m := (odd (a :: b :: xs)).length) (by
          subst n
          rw (config := {occs := .pos [2]}) [<-odd_even_length]
          rw [A5, A4, List.length_cons, A4]
          simp) (odd (a :: b :: xs)) rfl
        have h_even := ih (m := (even (a :: b :: xs)).length) (by
          subst n
          rw (config := {occs := .pos [2]}) [<-odd_even_length]
          rw [A4, List.length_cons]
          omega) (even (a :: b :: xs)) rfl
        have h_merge := permutation_merge leα (sort (odd (a :: b :: xs))) (sort (even (a :: b :: xs)))
        have h_odd_even : permutation (sort (odd (a :: b :: xs)) ++ sort (even (a :: b :: xs))) (odd (a :: b :: xs) ++ even (a :: b :: xs)) := permutation_append_preserve _ _ _ _ h_odd h_even

        apply P4 _ _ _ h_merge
        apply P4 _ _ _ h_odd_even
        exact h_split

end Part1

section Part2

variable {α : Type}
-- Uninterpreted functions
variable (childOf : α → α → Bool)
variable (h : α → Bool)
variable (m : α → Bool)
-- Descendant
variable (desc : α → α → Prop)
axiom desc_wf : WellFounded desc

-- Axioms
axiom A9 (x y : α) : desc x y ↔ childOf x y ∨ (∃ z, desc x z ∧ childOf z y)
axiom A10 (x : α) : h x ∨ m x

-- A child is a descendant
theorem child_of_desc (x y : α)
  (h : childOf x y) : desc x y := by
  rw [A9 childOf desc]
  left
  exact h

-- If a human is a descendant of a monkey, then there exists a human that is a child of a monkey
theorem G3 :
  (∃ x y, desc x y ∧ h x ∧ m y) →
  (∃ x y, childOf x y ∧ h x ∧ m y) := by
  intro ⟨x, y, hxy, hx, hy⟩
  -- we induct on the anscestors
  induction y using (desc_wf desc).induction generalizing x with
  | h y ih =>
    -- are we in the inductive or base case?
    rcases (A9 childOf desc x y).mp hxy with hchild | ⟨z, hxz, hzy⟩
    · exact ⟨x, y, hchild, hx, hy⟩
    · -- is the intermediate a human or a monkey?
      rcases A10 h m z with hz | hz
      · exact ⟨z, y, hzy, hz, hy⟩
      · -- still monkey...
        exact ih z (child_of_desc childOf desc _ _ hzy) x hxz hx hz

end Part2
