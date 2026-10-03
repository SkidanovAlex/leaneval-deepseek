import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.rank_ge_const_coeff
import Submission.Work.ORHughesFree.LacNatExt.rank_one_add_polyT

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-!
# Faithfulness of the natural extension of a faithful rank function

Let `R` be a von Neumann regular ring, `τ` the twist encoded by a
`MulSemiringAction (Multiplicative ℤ) R`, and `rk` a faithful Sylvester matrix rank function on
`R`.  If `rkE` is a natural extension of `rk` to the skew Laurent polynomial ring
`R[t^{±1};τ] = SkewL R` (in the sense of `IsNaturalExtension`), then `rkE` is again faithful.

The mathematical content is this.  Suppose `a ∈ R[t^{±1};τ]` is non-zero and `rkE a = 0`.  Let
`p` be the minimal exponent in the support of `a` (it exists since the support is a finite
non-empty subset of `ℤ`).  Right multiplication by the unit `t^{-p}` shifts the coefficients so
that `b = a·t^{-p}` is a *polynomial* (all negative coefficients vanish) whose constant
coefficient is `a_p ≠ 0`, and rank is unchanged by multiplication with a unit.  By
`rank_ge_const_coeff` the rank of the constant coefficient is at most the rank of the polynomial,
hence `rk (a_p) = 0`; faithfulness of `rk` forces `a_p = 0`, a contradiction.

The hypothesis `∀ n A, rkE (I_n + A t) = n` of `IsNaturalExtension` is converted into the
hypothesis `rkE (1 + B·diag t) = n` for polynomial matrices `B` by `lacrank_one_add_polyT`.
-/

section Helpers

variable {R : Type} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

/-- Coefficient of a right multiple by the monomial `t^{-p}`: the coefficient indices are shifted
up by `p`.  (No twist occurs, since the monomial is on the right.) -/
theorem coeffElt_mul_single_neg (a : SkewL R) (p k : ℤ) :
    coeffElt (a * SkewMonoidAlgebra.single (Multiplicative.ofAdd (-p)) (1 : R)) k =
      coeffElt a (k + p) := by
  rw [coeffElt, SkewMonoidAlgebra.coeff_mul_single, coeffElt]
  have hx : Multiplicative.ofAdd k * (Multiplicative.ofAdd (-p))⁻¹ =
      Multiplicative.ofAdd (k + p) := by
    rw [← ofAdd_neg, neg_neg, ← ofAdd_add]
  rw [hx, smul_one, mul_one]

end Helpers

section MinCoeff

variable {R : Type} [Ring R]

/-- The exponents occurring in a non-zero element of `R[t^{±1};τ]` have a minimum. -/
theorem exists_min_coeff (a : SkewL R) (ha : a ≠ 0) :
    ∃ p : ℤ, coeffElt a p ≠ 0 ∧ ∀ k : ℤ, coeffElt a k ≠ 0 → p ≤ k := by
  have hne : (a.support.image Multiplicative.toAdd).Nonempty := by
    rw [Finset.image_nonempty]
    exact Finset.nonempty_iff_ne_empty.mpr fun h => ha (SkewMonoidAlgebra.support_eq_empty.mp h)
  refine ⟨(a.support.image Multiplicative.toAdd).min' hne, ?_, ?_⟩
  · obtain ⟨g, hg, hg'⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
    have h1 : coeffElt a (Multiplicative.toAdd g) ≠ 0 := by
      rw [coeffElt, ofAdd_toAdd]
      exact SkewMonoidAlgebra.mem_support_iff.mp hg
    rwa [hg'] at h1
  · intro k hk
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨Multiplicative.ofAdd k,
      SkewMonoidAlgebra.mem_support_iff.mpr hk, toAdd_ofAdd k⟩)

end MinCoeff

theorem isFaithful_of_isNaturalExtension {R : Type} [Ring R] [VonNeumannRegularRing R]
    [MulSemiringAction (Multiplicative ℤ) R] (rk : Work.ORHughesFree.SylvesterRank R)
    (hrk : rk.IsFaithful) {rkE : Work.ORHughesFree.SylvesterRank
      (Work.ORHughesFree.NaturalExtension.SkewL R)}
    (h : Work.ORHughesFree.IsNaturalExtension rk rkE) : rkE.IsFaithful := by
  intro a ha
  by_contra hne
  -- The minimal exponent `p` of the support of `a` and the unit `u = t^{-p}`.
  obtain ⟨p, hp_ne, hp_min⟩ := exists_min_coeff a hne
  set u : SkewL R := SkewMonoidAlgebra.single (Multiplicative.ofAdd (-p)) (1 : R) with hu
  -- The polynomial-matrix hypothesis for `rank_ge_const_coeff`, from `IsNaturalExtension`.
  have hb : ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) (SkewL R)),
      (∀ i j, ∀ k : ℤ, k < 0 → coeffElt (B i j) k = 0) →
      rkE.rk n n ((1 : Matrix (Fin n) (Fin n) (SkewL R)) +
        B * Matrix.diagonal (fun _ => (skewLaurentT : SkewL R))) = (n : ℝ) :=
    fun n B hB => lacrank_one_add_polyT rkE h.2 B hB
  -- The shifted element `a * u` is a polynomial with non-zero constant coefficient.
  have hshift : ∀ k : ℤ, coeffElt (a * u) k = coeffElt a (k + p) := by
    intro k
    rw [hu]
    exact coeffElt_mul_single_neg a p k
  have hpoly : ∀ k : ℤ, k < 0 → coeffElt (a * u) k = 0 := by
    intro k hk
    rw [hshift k]
    by_contra hc
    have := hp_min (k + p) hc
    omega
  have hconst : coeffElt (a * u) 0 ≠ 0 := by
    rw [hshift 0, zero_add]
    exact hp_ne
  -- `u` is a unit.
  have hu_inv : u * SkewMonoidAlgebra.single (Multiplicative.ofAdd p) (1 : R) = 1 := by
    rw [hu, SkewMonoidAlgebra.single_mul_single, ← ofAdd_add, neg_add_cancel]
    simp
  have hstep : rkE.rk 1 1 (oneByOne (a * u)) = rkE.rk 1 1 (oneByOne a) := by
    rw [← oneByOne_mul_eq]
    refine SylvesterRank.rk_eq_of_mul_right_inverse rkE (oneByOne a) (oneByOne u)
      (oneByOne (SkewMonoidAlgebra.single (Multiplicative.ofAdd p) (1 : R))) ?_
    rw [oneByOne_mul_eq, hu_inv]
    exact one_matrix_one_eq.symm
  -- The constant coefficient of `a * u` has rank at most that of `a * u`, which is zero.
  have hle := rank_ge_const_coeff rkE hb (a * u) hpoly
  have hzero : rkE.rk 1 1
      (oneByOne (SkewMonoidAlgebra.single 1 (coeffElt (a * u) 0))) = 0 := by
    refine le_antisymm ?_ (rkE.rk_nonneg 1 1 _)
    calc rkE.rk 1 1 (oneByOne (SkewMonoidAlgebra.single 1 (coeffElt (a * u) 0)))
        ≤ rkE.rk 1 1 (oneByOne (a * u)) := hle
      _ = rkE.rk 1 1 (oneByOne a) := hstep
      _ = 0 := ha
  -- Faithfulness of `rk` now gives `coeffElt (a * u) 0 = 0`, contradicting `hconst`.
  have hc_zero : coeffElt (a * u) 0 = 0 := by
    apply hrk
    have hSc : skewLaurentConst 1 1 (oneByOne (coeffElt (a * u) 0)) =
        oneByOne (SkewMonoidAlgebra.single 1 (coeffElt (a * u) 0)) := by
      ext i j
      simp [skewLaurentConst, oneByOne]
    rw [← h.1 1 1 (oneByOne (coeffElt (a * u) 0)), hSc]
    exact hzero
  exact hconst hc_zero

end Work.ORHughesFree.NaturalExtension
