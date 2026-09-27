import Mathlib
import Submission.Mostow.GapADefs

/-!
# Setup for the geodesic stratum (`k = 1` case of GAP-A)

Vocabulary for the `Work.Mostow.geodStratum` chapter: the setwise stabiliser of the standard
geodesic `stdTG 1 m ⊆ E (1+m)` (as a subgroup), its pointwise part, the *Margulis region* of the
pointwise part (the set of points where some non-identity element of the pointwise part is
near-identity), and the cardinality of the pointwise part.

The chapter proves, for `m ≥ 4` even, that a discrete `Λ ≤ PO (1+m) 1` with a fundamental domain
of volume `≤ V`, a point `z` at which some non-identity element of `Λ` is `η`-near the identity
(`η ≤ η₀(V)`, `V` the covolume bound), has an *infinite-order* element with
`hdist z (γ • z) ≤ C η`, where `C` is a constant depending only on `m`.
-/

noncomputable section

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- The **setwise stabiliser of the standard geodesic** `stdTG 1 m` as a subgroup of `PO (1+m) 1`. -/
def stabStdGeod (m : ℕ) (hA : POActionProp (1 + m)) : Subgroup (PO (1 + m) 1) where
  carrier := SetStabStd 1 m
  mul_mem' := by
    intro a b ha hb u
    rw [hA.2.2.2.2.1 a b u]
    exact (hb u).trans (ha (b • u))
  one_mem' := by
    intro u
    rw [hA.2.2.2.1 u]
  inv_mem' := by
    intro a ha u
    have h := ha (a⁻¹ • u)
    rw [← hA.2.2.2.2.1 a a⁻¹ u, mul_inv_cancel, hA.2.2.2.1 u] at h
    exact h.symm

/-- The part of `Λ` that preserves the standard geodesic setwise. -/
def geodStab (m : ℕ) (hA : POActionProp (1 + m)) (Λ : Subgroup (PO (1 + m) 1)) :
    Subgroup (PO (1 + m) 1) :=
  Λ ⊓ stabStdGeod m hA

/-- The **Margulis region** of the pointwise stabiliser of the standard geodesic: the set of points
at which some non-identity element of `Λ` fixing `stdTG 1 m` pointwise is `η₁`-near the identity. -/
def margRegion (m : ℕ) (Λ : Subgroup (PO (1 + m) 1)) (η₁ : ℝ) : Set (E (1 + m)) :=
  {u | ∃ a : PO (1 + m) 1,
    a ∈ Λ ∧ a ∈ SetStabStd 1 m ∧ resStd 1 m a = 1 ∧ a ≠ 1 ∧ NearIdAt a u η₁}

/-- The cardinality of the pointwise stabiliser of the standard geodesic inside `Λ`. -/
def geodPtCard (m : ℕ) (Λ : Subgroup (PO (1 + m) 1)) : ℕ :=
  Nat.card {c : PO (1 + m) 1 // c ∈ Λ ∧ c ∈ SetStabStd 1 m ∧ resStd 1 m c = 1}

end Work.Mostow

end
