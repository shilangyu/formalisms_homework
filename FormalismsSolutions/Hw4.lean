/-!
# Knaster–Tarski in Lean

Useful Tactics

* `apply le_trans h`, for chains of `⊑` (c.f. warm-up §6 and 7.3), and
* `apply` with a lemma of your own, e.g. `apply le_gfp`, which leaves you to prove its hypothesis.

Put the cursor anywhere inside a proof to see the current goal (in VS Code: the *Lean Infoview*
panel; in the browser: the right-hand pane). Lines such as `inst✝ : CompleteLattice A` in the goal
are the instances in scope; ignore them.

-/

namespace KT

section Theory

variable {A : Type}

/-! ## 1. Posets and bounds

A subset of `A` is a predicate `B : A → Prop`: `B x` says that `x` is in `B`. So "`x` is an upper
bound of `B`" is `∀ y, B y → y ⊑ x`, and the set of all postfixpoints of `F` is
`fun x => x ⊑ F x`.

A `class` (warm-up §7) bundles a structure on a type: `[Poset A]` reads "let `A` carry a partial
order". The fields are the poset axioms, and you use them by name: `le_refl x : x ⊑ x`,
`le_antisymm h₁ h₂ : x = y`, `le_trans h₁ h₂ : x ⊑ z`. -/

class Poset (A : Type) where
  le : A → A → Prop
  le_refl : ∀ x, le x x
  le_antisymm : ∀ {x y}, le x y → le y x → x = y
  le_trans : ∀ {x y z}, le x y → le y z → le x z

infix:50 " ⊑ " => Poset.le

export Poset (le_refl le_antisymm le_trans)

section Bounds

variable [Poset A]

abbrev Subset (A : Type) := A → Prop

def IsUpperBound (B : Subset A) (x : A) : Prop := ∀ y, B y → y ⊑ x

def IsLowerBound (B : Subset A) (x : A) : Prop := ∀ y, B y → x ⊑ y

def IsLUB (B : Subset A) (x : A) : Prop := IsUpperBound B x ∧ ∀ y, IsUpperBound B y → x ⊑ y

def IsGLB (B : Subset A) (x : A) : Prop := IsLowerBound B x ∧ ∀ y, IsLowerBound B y → y ⊑ x

/-- **Warm-up.** Lecture 2: a set has at most one least upper bound — which is what licenses
writing `sSup B` for *the* lub below.

`hx.1` and `hx.2` are the two halves of `hx : IsLUB B x`. Because the theorem is called
`IsLUB.unique`, it can also be used as `hx.unique hy`. -/
theorem IsLUB.unique {B : Subset A} {x y : A} (hx : IsLUB B x) (hy : IsLUB B y) : x = y := by
  have ⟨hx, hxy⟩ := hx
  have ⟨hy, hyx⟩ := hy
  apply le_antisymm
  · exact hxy _ hy
  · exact hyx _ hx

end Bounds

/-! ## 2. Complete lattices and fixpoints

A complete lattice is a poset in which every subset `B` has a lub `sSup B` (the lecture's `⨆B`)
and a glb `sInf B` (`⨅B`). The four fields below say exactly that: `sSup B` is an upper bound of
`B` (`le_sSup`) and below every other one (`sSup_le`); dually for `sInf B`. These four are the
whole interface — you will not need anything else about `sSup` and `sInf`.

    le_sSup : B x → x ⊑ sSup B                  sInf_le : B x → sInf B ⊑ x
    sSup_le : (∀ y, B y → y ⊑ z) → sSup B ⊑ z   le_sInf : (∀ y, B y → z ⊑ y) → z ⊑ sInf B

`extends Poset A`: a complete lattice *is* a poset, plus these four facts. -/

class CompleteLattice (A : Type) extends Poset A where
  sSup : Subset A → A
  sInf : Subset A → A
  le_sSup : ∀ {B : Subset A} {x : A}, B x → x ⊑ sSup B
  sSup_le : ∀ {B : Subset A} {z : A}, (∀ y, B y → y ⊑ z) → sSup B ⊑ z
  sInf_le : ∀ {B : Subset A} {x : A}, B x → sInf B ⊑ x
  le_sInf : ∀ {B : Subset A} {z : A}, (∀ y, B y → z ⊑ y) → z ⊑ sInf B

export CompleteLattice (sSup sInf le_sSup sSup_le sInf_le le_sInf)

section Fixpoints

variable [Poset A]

/-- `hF : Monotone F` is used as a function: given `h : x ⊑ y`, `hF h : F x ⊑ F y`. -/
def Monotone (F : A → A) : Prop := ∀ {x y}, x ⊑ y → F x ⊑ F y

/-- `Prefixpoint F x` unfolds to `F x ⊑ x`. `apply` and `exact` see through that;
`change F x ⊑ x` shows it. -/
def Prefixpoint (F : A → A) (x : A) : Prop := F x ⊑ x

def Postfixpoint (F : A → A) (x : A) : Prop := x ⊑ F x

/-- As in the lecture notes: both a pre- and a postfixpoint. -/
def Fixpoint (F : A → A) (x : A) : Prop := Prefixpoint F x ∧ Postfixpoint F x

end Fixpoints

section Extremal

variable [CompleteLattice A]

/-- `ŷ` in the lecture notes. -/
def gfp (F : A → A) : A := sSup (fun x => x ⊑ F x)

/-- `ẑ` in the lecture notes. -/
def lfp (F : A → A) : A := sInf (fun x => F x ⊑ x)

end Extremal

/-! ## 3. Knaster–Tarski

**Theorem.** Let `(A, ⊑)` be a complete lattice and `F` monotone on `A`. Let
`ŷ = ⨆{x | x ⊑ F x}` and `ẑ = ⨅{x | F x ⊑ x}`. Then
  1. `ŷ` and `ẑ` are fixpoints of `F`, and
  2. for every fixpoint `x` of `F`, `ẑ ⊑ x ⊑ ŷ`.

-/

section KnasterTarski

variable [CompleteLattice A] {F : A → A}

/-- Every postfixpoint is below `ŷ`. (No monotonicity needed.) -/
theorem le_gfp {x : A} (h : x ⊑ F x) : x ⊑ gfp F := by
  apply le_sSup
  exact h

/-- `ẑ` is below every prefixpoint. This is the principle of induction: `lfp F` is contained in
every set closed under the rules `F`. -/
theorem lfp_le {x : A} (h : F x ⊑ x) : lfp F ⊑ x := by
  apply sInf_le
  exact h

/-- `ŷ ⊑ F ŷ`. -/
theorem postfixpoint_gfp (hF : Monotone F) : Postfixpoint F (gfp F) := by
  apply sSup_le
  intro y hy
  apply le_trans hy
  apply hF
  apply le_gfp hy

/-- `F ŷ ⊑ ŷ`. -/
theorem prefixpoint_gfp (hF : Monotone F) : Prefixpoint F (gfp F) := by
  apply le_gfp
  apply hF
  apply postfixpoint_gfp hF

/-- `F ẑ ⊑ ẑ`. -/
theorem prefixpoint_lfp (hF : Monotone F) : Prefixpoint F (lfp F) := by
  apply le_sInf
  intro y hy
  apply le_trans _ hy
  apply hF
  apply lfp_le hy

/-- `ẑ ⊑ F ẑ`. -/
theorem postfixpoint_lfp (hF : Monotone F) : Postfixpoint F (lfp F) := by
  apply sInf_le
  apply hF
  apply prefixpoint_lfp hF

/-- **Knaster–Tarski**, as stated in lecture 2. -/
theorem knaster_tarski (hF : Monotone F) :
    Fixpoint F (gfp F) ∧ Fixpoint F (lfp F) ∧
    ∀ x, Fixpoint F x → lfp F ⊑ x ∧ x ⊑ gfp F := by
  constructor
  · constructor
    · exact prefixpoint_gfp hF
    · exact postfixpoint_gfp hF
  · constructor
    · constructor
      · exact prefixpoint_lfp hF
      · exact postfixpoint_lfp hF
    · intro x h
      constructor
      · exact lfp_le h.left
      · exact le_gfp h.right

end KnasterTarski

section Optional

variable [Poset A] {F : A → A}

/-- **Optional.** The lecture's definition of fixpoint agrees with Mathlib's `F x = x`. -/
theorem fixpoint_iff {x : A} : Fixpoint F x ↔ F x = x := by
  constructor <;> intro h
  · exact le_antisymm h.left h.right
  · unfold Fixpoint Prefixpoint Postfixpoint
    rw [h]
    exact ⟨le_refl _, le_refl _⟩

end Optional

end Theory
