import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BdExt.Basic

/-!
# `spatTheta`: the spatial part of `A · (ξ,1)` points along `bdO A ξ`

For `A ∈ O(n,1)` and `ξ` on the boundary sphere, let
`w = mat A *ᵥ theta ξ` be the image of the null vector `theta ξ = (ξ,1)`.  Then

`dirv (tsign A • spat w) = bdO A ξ`

i.e. the Euclidean direction of the spatial part of `tsign A • w`, normalised so that
it has positive `(n+1)`-st coordinate, is exactly the image of `ξ` under the boundary
action `bdO A`.

The proof is a two-line computation once two facts are known.

* `w` is a *null* vector (`mform w w = 0`, from the invariance of the Minkowski form under
  `O(n,1)`), so `‖spat w‖ = |w (Sum.inr 0)|`;
* the sign of the time coordinate of `w` is the sign of `tsign A`: the last row `(c, a)` of
  `mat A` satisfies `‖a‖² = c² - 1`, hence `|⟪a,ξ⟫| ≤ √(c²-1) < |c|` for `‖ξ‖ = 1`, and
  `w (Sum.inr 0) = c + ⟪a,ξ⟫` has the sign of `c = mat A (Sum.inr 0) (Sum.inr 0)`, which is
  exactly `tsign A`.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

lemma spatTheta_tsign_abs_one (A : O1 n) : |tsign A| = 1 := by
  rcases Hyper.tsign_eq_one_or A with h | h <;> rw [h] <;> norm_num

/-- The time coordinate of `mat A *ᵥ theta ξ` is `A₀₀ + ⟪row₀, ξ⟫`. -/
lemma spatTheta_time_mulVec_theta (A : O1 n) (ξ : E n) :
    ((mat A).mulVec (theta ξ)) (Sum.inr 0) =
      mat A (Sum.inr 0) (Sum.inr 0) +
        inner ℝ (WithLp.toLp 2 fun i => mat A (Sum.inr 0) (Sum.inl i)) ξ := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_one, Work.Mostow.inner_eq_sum]
  simp [Work.Mostow.theta]
  ring

/-- The sign of the time coordinate of `mat A *ᵥ theta ξ` is `tsign A`. -/
lemma spatTheta_tsign_mul_time (A : O1 n) {ξ : E n} (hξ : ξ ∈ Sph n) :
    tsign A * ((mat A).mulVec (theta ξ)) (Sum.inr 0) =
      |((mat A).mulVec (theta ξ)) (Sum.inr 0)| := by
  have hξnorm : ‖ξ‖ = 1 := (mem_Sph_iff ξ).1 hξ
  -- Cauchy–Schwarz for the last row of `mat A`
  have hle : |inner ℝ (WithLp.toLp 2 fun i => mat A (Sum.inr 0) (Sum.inl i)) ξ| ≤
      Real.sqrt (mat A (Sum.inr 0) (Sum.inr 0) ^ 2 - 1) := by
    have h := Hyper.abs_inner_row_le A ξ
    rwa [hξnorm, mul_one] at h
  have hs : Real.sqrt (mat A (Sum.inr 0) (Sum.inr 0) ^ 2 - 1) <
      |mat A (Sum.inr 0) (Sum.inr 0)| := by
    have h1 : Real.sqrt (mat A (Sum.inr 0) (Sum.inr 0) ^ 2 - 1) ^ 2 <
        |mat A (Sum.inr 0) (Sum.inr 0)| ^ 2 := by
      rw [Real.sq_sqrt (by have := O1_tt_sq_ge_one A; linarith), sq_abs]
      have := O1_tt_sq_ge_one A
      linarith
    have h2 := sq_lt_sq.mp h1
    rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_abs] at h2
  have htime := spatTheta_time_mulVec_theta A ξ
  rcases lt_trichotomy (mat A (Sum.inr 0) (Sum.inr 0)) 0 with hneg | hzero | hpos
  · have hw : ((mat A).mulVec (theta ξ)) (Sum.inr 0) < 0 := by
      rw [htime]
      have h1 : inner ℝ (WithLp.toLp 2 fun i => mat A (Sum.inr 0) (Sum.inl i)) ξ ≤
          |inner ℝ (WithLp.toLp 2 fun i => mat A (Sum.inr 0) (Sum.inl i)) ξ| := le_abs_self _
      have h2 : |mat A (Sum.inr 0) (Sum.inr 0)| =
          -mat A (Sum.inr 0) (Sum.inr 0) := abs_of_neg hneg
      linarith
    rw [abs_of_neg hw, (tsign_eq_neg_one_iff A).mpr hneg]
    ring
  · exact absurd hzero (O1_tt_ne_zero A)
  · have hw : 0 < ((mat A).mulVec (theta ξ)) (Sum.inr 0) := by
      rw [htime]
      have h1 : -|inner ℝ (WithLp.toLp 2 fun i => mat A (Sum.inr 0) (Sum.inl i)) ξ| ≤
          inner ℝ (WithLp.toLp 2 fun i => mat A (Sum.inr 0) (Sum.inl i)) ξ := neg_abs_le _
      have h2 : |mat A (Sum.inr 0) (Sum.inr 0)| =
          mat A (Sum.inr 0) (Sum.inr 0) := abs_of_pos hpos
      linarith
    rw [abs_of_pos hw, (tsign_eq_one_iff A).mpr hpos]
    ring

theorem spatTheta (n : ℕ) (A : Submission.Mostow.O1 n) (ξ : Submission.Mostow.E n)
    (hξ : ξ ∈ Submission.Mostow.Sph n) :
    Work.Mostow.BdExt.dirv (Submission.Mostow.tsign A •
        Submission.Mostow.Hyper.spat (Matrix.mulVec (Submission.Mostow.mat A) (Work.Mostow.theta ξ)))
      = Submission.Mostow.bdO A ξ := by
  set w : Fin n ⊕ Fin 1 → ℝ := (mat A).mulVec (theta ξ) with hw
  -- `w` is a null vector, so `‖spat w‖ = |w (Sum.inr 0)|`
  have hnull : mform w w = 0 := by rw [hw, mform_mat_mulVec, theta_mform_self hξ]
  have hsum : ∑ i, w (Sum.inl i) ^ 2 = w (Sum.inr 0) ^ 2 := by
    have h := hnull
    rw [mform_self_apply] at h
    linarith
  have hnrm : ‖Hyper.spat w‖ = |w (Sum.inr 0)| := by
    have h : ‖Hyper.spat w‖ ^ 2 = w (Sum.inr 0) ^ 2 := by
      rw [norm_sq_eq_sum]
      exact hsum
    have h2 := congrArg Real.sqrt h
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq_eq_abs] at h2
  have hsign : tsign A * w (Sum.inr 0) = |w (Sum.inr 0)| := by
    simpa [hw] using spatTheta_tsign_mul_time A hξ
  have ht : w (Sum.inr 0) ≠ 0 := by rw [hw]; exact mat_mulVec_theta_ne_zero A hξ
  have htsq : tsign A * tsign A = 1 := tsign_sq A
  have habs : |tsign A| = 1 := spatTheta_tsign_abs_one A
  have hnorm_smul : ‖tsign A • Hyper.spat w‖ = ‖Hyper.spat w‖ := by
    rw [norm_smul, Real.norm_eq_abs, habs, one_mul]
  ext i
  rw [bdO_apply]
  rw [← hw]
  show ‖tsign A • Hyper.spat w‖⁻¹ * (tsign A • Hyper.spat w).ofLp i =
    w (Sum.inl i) / w (Sum.inr 0)
  rw [WithLp.ofLp_smul, hnorm_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  -- `tsign A * ‖spat w‖⁻¹ = (w (Sum.inr 0))⁻¹` because the two signs agree
  have hkey : ‖Hyper.spat w‖⁻¹ = (w (Sum.inr 0))⁻¹ * tsign A := by
    rw [hnrm, ← hsign, mul_inv, inv_eq_of_mul_eq_one_right htsq]
    ring
  rw [hkey, div_eq_mul_inv]
  calc (w (Sum.inr 0))⁻¹ * tsign A * (tsign A * w (Sum.inl i))
      = (w (Sum.inr 0))⁻¹ * (tsign A * tsign A) * w (Sum.inl i) := by ring
    _ = (w (Sum.inr 0))⁻¹ * 1 * w (Sum.inl i) := by rw [htsq]
    _ = w (Sum.inl i) * (w (Sum.inr 0))⁻¹ := by ring

end

end Work.Mostow.BdExt
