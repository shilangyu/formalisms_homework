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
-- axiom P1 :
--   permutation ([] : List α) = true
-- axiom O2 (a : α) :
--   ordered (a :: []) = true
-- axiom O3 (a b : α) (x : List α) :
--   ordered (a :: b :: x) = (a ≤ b ∧ ordered (b :: x))


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
