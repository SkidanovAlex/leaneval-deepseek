import Mathlib

/-!
# Definitions and basic lemmas for `interval_connected`

We prove that on an interval of integers of length at least `A + B - 2`, the graph whose
edges connect integers differing by `± A` or `± B` is connected, whenever `A, B ≥ 2` are
coprime (witnessed by a Bezout relation).

This file contains the shared vocabulary: the (symmetric, two-sided) step relation `S` on
an interval, its asymmetric "one-sided" version `IRel` (the relation of the target theorem),
and the elementary facts that `S` is symmetric and that reachability in `S` is symmetric.

We also introduce the residue orbit `orb A B n = (n * B) % A`, the carrier of the
combinatorial argument.
-/

namespace Work.OROneRel

/-- The step relation of the target statement: from `x` one may move to `y` if `y` lies in
`[lo,hi]` and `y = x ± A` or `y = x ± B`.  Note that it is *not* symmetric (it does not
assert that `x` lies in the interval). -/
def IRel (lo hi A B : ℤ) (x y : ℤ) : Prop :=
  lo ≤ y ∧ y ≤ hi ∧ (y = x + A ∨ y = x - A ∨ y = x + B ∨ y = x - B)

/-- The symmetric two-sided step relation: both endpoints lie in `[lo,hi]` and differ by
`± A` or `± B`. -/
def S (lo hi A B : ℤ) (x y : ℤ) : Prop :=
  lo ≤ x ∧ x ≤ hi ∧ lo ≤ y ∧ y ≤ hi ∧
    (y = x + A ∨ y = x - A ∨ y = x + B ∨ y = x - B)

/-- Every `S`-step is an `IRel`-step. -/
lemma S_le_IRel {lo hi A B : ℤ} : S lo hi A B ≤ IRel lo hi A B :=
  fun _ _ h => ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- `S` is symmetric. -/
lemma S_symm {lo hi A B x y : ℤ} (h : S lo hi A B x y) : S lo hi A B y x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h3, h4, h1, h2, ?_⟩
  rcases h5 with h5 | h5 | h5 | h5
  · right; left; omega
  · left; omega
  · right; right; right; omega
  · right; right; left; omega

/-- Reachability in the symmetric relation `S` is symmetric. -/
lemma rtg_symm {lo hi A B x y : ℤ}
    (h : Relation.ReflTransGen (S lo hi A B) x y) :
    Relation.ReflTransGen (S lo hi A B) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih => exact ih.head (S_symm hbc)

/-- A single `S`-step, phrased with all four membership conditions. -/
lemma S.of {lo hi A B x y : ℤ} (h1 : lo ≤ x) (h2 : x ≤ hi) (h3 : lo ≤ y) (h4 : y ≤ hi)
    (h5 : y = x + A ∨ y = x - A ∨ y = x + B ∨ y = x - B) : S lo hi A B x y :=
  ⟨h1, h2, h3, h4, h5⟩

/-- The residue orbit `orb A B n = (n * B) % A`. -/
def orb (A B : ℤ) (n : ℕ) : ℤ := ((n : ℤ) * B) % A

end Work.OROneRel
