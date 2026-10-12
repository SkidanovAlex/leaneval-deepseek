import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseK15.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.corpusChi_zero_near`

A full ball of radius `ℓ/20` inside the box `Λ(ℓ) = ℓ • [-1/2,1/2]³` on which the corpus
localization function `χ_Λ` vanishes identically.

The corpus χ (`Submission.BoseGases.chi`) is supported in the **ball** of radius `1/2`,
whereas the box `Λ(ℓ)` is the cube `[-ℓ/2,ℓ/2]³`.  So there is plenty of room near a corner
of the cube: take

  `x₁ = (9ℓ/20)·(1,1,1)`,

the centre of the little cube `[2ℓ/5, ℓ/2]³`, whose diameter is `ℓ/5`, so the ball of
radius `ℓ/20` around `x₁` stays in the corner region.  Every point `x` of that ball has

* all coordinates `> 9ℓ/20 − ℓ/20 = 2ℓ/5` and `< 9ℓ/20 + ℓ/20 = ℓ/2`, so `x ∈ Λ(ℓ)`; and
* `‖x‖² > 3·(2ℓ/5)² = 12ℓ²/25 > ℓ²/4`, so `‖ℓ⁻¹ • x‖ > 1/2` and
  `χ_Λ(x) = χ(ℓ⁻¹ • x) = 0` by `Submission.BoseGases.chi_eq_zero_of_norm_gt`.
-/

open scoped Pointwise
open MeasureTheory

namespace Work.BoseBoxFock

/-- **The corpus χ vanishes on a ball of radius `ℓ/20` inside the box.** -/
theorem corpusChi_zero_near {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ x₁ : EuclideanSpace ℝ (Fin 3),
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x - x₁‖ < ℓ / 20 →
        x ∈ Work.BoseB4.BoxData.boxL Work.BoseK15.corpusBox ℓ ∧
        Work.BoseK15.corpusBox.chiLam ℓ x = 0 := by
  refine ⟨EuclideanSpace.single 0 (9 / 20 * ℓ) + EuclideanSpace.single 1 (9 / 20 * ℓ)
      + EuclideanSpace.single 2 (9 / 20 * ℓ), ?_⟩
  intro x hx
  set x₁ : EuclideanSpace ℝ (Fin 3) :=
    EuclideanSpace.single 0 (9 / 20 * ℓ) + EuclideanSpace.single 1 (9 / 20 * ℓ)
      + EuclideanSpace.single 2 (9 / 20 * ℓ) with hx₁def
  -- the coordinates of `x₁` are all `9ℓ/20`
  have hx₁ : ∀ i : Fin 3, x₁ i = 9 / 20 * ℓ := by
    intro i
    fin_cases i <;> simp [hx₁def]
  -- the coordinates of `x` are within `ℓ/20` of `9ℓ/20`
  have hcoord : ∀ i : Fin 3, |x i - 9 / 20 * ℓ| < ℓ / 20 := by
    intro i
    have h1 : |(x - x₁) i| ≤ ‖x - x₁‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (x - x₁) i
    have h2 : (x - x₁) i = x i - 9 / 20 * ℓ := by
      simp [hx₁ i]
    rw [h2] at h1
    linarith
  -- hence `|x i| ≤ ℓ/2`
  have habs : ∀ i : Fin 3, |x i| ≤ ℓ / 2 := by
    intro i
    have h := hcoord i
    have hsplit : x i = (x i - 9 / 20 * ℓ) + 9 / 20 * ℓ := by ring
    rw [hsplit]
    calc |(x i - 9 / 20 * ℓ) + 9 / 20 * ℓ|
        ≤ |x i - 9 / 20 * ℓ| + |9 / 20 * ℓ| := abs_add_le _ _
      _ ≤ ℓ / 20 + 9 / 20 * ℓ := by
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 9 / 20 * ℓ)]
          linarith
      _ = ℓ / 2 := by ring
  constructor
  · -- `x` lies in the box `Λ(ℓ)`
    show x ∈ (ℓ : ℝ) • Work.BoseK15.corpusBox.cell
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ)]
    show ℓ⁻¹ • x ∈ Work.BoseB4.unitCell
    intro i
    rw [PiLp.smul_apply, smul_eq_mul, abs_mul,
      abs_of_nonneg (le_of_lt (inv_pos.mpr hℓ))]
    have h := habs i
    have hmul := mul_le_mul_of_nonneg_left h (le_of_lt (inv_pos.mpr hℓ))
    have hc : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by field_simp
    linarith
  · -- `χ_Λ` vanishes there
    rw [Work.BoseB4.BoxData.chiLam_apply, Work.BoseK15.corpusBox_chi]
    refine Submission.BoseGases.chi_eq_zero_of_norm_gt _ ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (inv_pos.mpr hℓ))]
    have hxnorm : ℓ / 2 < ‖x‖ := by
      have hsq : (ℓ / 2) ^ 2 < ‖x‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        calc (ℓ / 2) ^ 2 < (2 / 5 * ℓ) ^ 2 * 3 := by nlinarith [hℓ]
          _ = ∑ _i : Fin 3, (2 / 5 * ℓ) ^ 2 := by
                simp [Finset.sum_const, Fintype.card_fin, mul_comm]
          _ < ∑ i : Fin 3, ‖x.ofLp i‖ ^ 2 := by
                apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
                intro i _
                have h := hcoord i
                rw [abs_lt] at h
                have hlt : 2 / 5 * ℓ < x.ofLp i := by linarith [h.1]
                have hnn : (0 : ℝ) < 2 / 5 * ℓ := by linarith
                have hsq2 : (2 / 5 * ℓ) ^ 2 < (x.ofLp i) ^ 2 := by nlinarith
                rwa [Real.norm_eq_abs, sq_abs]
      have h := (sq_lt_sq.mp hsq)
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ ℓ / 2), abs_of_nonneg (norm_nonneg x)] at h
      exact h
    have hmul := mul_lt_mul_of_pos_left hxnorm (inv_pos.mpr hℓ)
    have hc : ℓ⁻¹ * (ℓ / 2) = 1 / 2 := by field_simp
    linarith

end Work.BoseBoxFock
