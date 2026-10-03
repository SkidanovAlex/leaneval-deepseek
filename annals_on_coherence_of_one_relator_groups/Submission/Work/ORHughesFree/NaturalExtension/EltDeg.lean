/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Degree bounds for elements of `U[t^{±1};τ]`

Element-level counterparts of `lowerDeg`/`upperDeg` from
`Submission.Work.ORHughesFree.NaturalExtension.Defs`: for an element `f` of the skew Laurent
polynomial ring `U[t^{±1};τ]` we record bounds `lowDeg f` and `upDeg f` on the degrees of the
coefficients occurring in `f`.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix

section EltDeg

variable {U : Type u} [AddMonoid U]

/-- A bound `d` such that all coefficients `f_k` of `f` with `k < -d` vanish. -/
def lowDeg (f : SkewL U) : ℕ :=
  f.support.sup fun g => Int.toNat (-(Multiplicative.toAdd g))

/-- A bound `d` such that all coefficients `f_k` of `f` with `k > d` vanish. -/
def upDeg (f : SkewL U) : ℕ :=
  f.support.sup fun g => Int.toNat (Multiplicative.toAdd g)

theorem coeffElt_eq_zero_of_lt_lowDeg (f : SkewL U) {k : ℤ} (h : k < -(lowDeg f : ℤ)) :
    coeffElt f k = 0 := by
  by_contra hk
  have hmem : Multiplicative.ofAdd k ∈ f.support :=
    (Finsupp.mem_support_iff).mpr (by simpa [coeffElt] using hk)
  have h1 : Int.toNat (-(Multiplicative.toAdd (Multiplicative.ofAdd k))) ≤ lowDeg f :=
    Finset.le_sup (f := fun g => Int.toNat (-(Multiplicative.toAdd g))) hmem
  have h2 : -(k : ℤ) ≤ (lowDeg f : ℤ) := by simpa using Int.toNat_le.mp h1
  omega

theorem coeffElt_eq_zero_of_gt_upDeg (f : SkewL U) {k : ℤ} (h : (upDeg f : ℤ) < k) :
    coeffElt f k = 0 := by
  by_contra hk
  have hmem : Multiplicative.ofAdd k ∈ f.support :=
    (Finsupp.mem_support_iff).mpr (by simpa [coeffElt] using hk)
  have h1 : Int.toNat (Multiplicative.toAdd (Multiplicative.ofAdd k)) ≤ upDeg f :=
    Finset.le_sup (f := fun g => Int.toNat (Multiplicative.toAdd g)) hmem
  have h2 : (k : ℤ) ≤ (upDeg f : ℤ) := by simpa using Int.toNat_le.mp h1
  omega

theorem coeffElt_eq_zero_of_notMem_Icc (f : SkewL U) {k : ℤ}
    (h : k ∉ Finset.Icc (-(lowDeg f : ℤ)) (upDeg f : ℤ)) : coeffElt f k = 0 := by
  rw [Finset.mem_Icc, not_and_or] at h
  rcases h with h | h
  · exact coeffElt_eq_zero_of_lt_lowDeg f (lt_of_not_ge h)
  · exact coeffElt_eq_zero_of_gt_upDeg f (lt_of_not_ge h)

/-- Every element of the support of `f` lies in the interval of its degree bounds. -/
theorem support_subset_Icc_image (f : SkewL U) {L K : ℕ} (hL : lowDeg f ≤ L)
    (hK : upDeg f ≤ K) :
    f.support ⊆ (Finset.Icc (-(L : ℤ)) (K : ℤ)).image Multiplicative.ofAdd := by
  intro a ha
  rw [Finset.mem_image]
  refine ⟨Multiplicative.toAdd a, ?_, by simp⟩
  rw [Finset.mem_Icc]
  refine ⟨?_, ?_⟩
  · have h1 : Int.toNat (-(Multiplicative.toAdd a)) ≤ lowDeg f :=
      Finset.le_sup (f := fun g => Int.toNat (-(Multiplicative.toAdd g))) ha
    have h2 : -(Multiplicative.toAdd a) ≤ (L : ℤ) :=
      le_trans (Int.toNat_le.mp h1) (by exact_mod_cast hL)
    omega
  · have h1 : Int.toNat (Multiplicative.toAdd a) ≤ upDeg f :=
      Finset.le_sup (f := fun g => Int.toNat (Multiplicative.toAdd g)) ha
    have h2 : (Multiplicative.toAdd a) ≤ (K : ℤ) :=
      le_trans (Int.toNat_le.mp h1) (by exact_mod_cast hK)
    omega

end EltDeg

end Work.ORHughesFree.NaturalExtension
