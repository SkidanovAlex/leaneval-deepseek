import Mathlib
import Submission.Work.BourgainPlan.Maximal.dyadicMaximal

/-!
# The `ℓ²`-valued (per-component) dyadic maximal function: endpoint bounds

For a finite family `f : Fin n → ℝ → ℝ`, put

`ell2Max f x = Σ_t (dyMax (‖f t ·‖) x)²`,   `ell2Sq f x = Σ_t ‖f t x‖ₑ²`.

Here we prove the two *easy* endpoints of the vector-valued (Fefferman--Stein) maximal inequality

`‖ (Σ_t (M f_t)^2)^{1/2} ‖_{L^p} ≤ C_p ‖ (Σ_t |f_t|^2)^{1/2} ‖_{L^p}` `(1 < p < ∞)`:

* the `L²(ℓ²)` bound (sum of the scalar `L²` bounds of `dyMax`), and
* the trivial `L^∞(ℓ²)` bound.

The weak-`(1,1)` bound (the Calderón--Zygmund stopping-time argument) and the interpolation are
the remaining two steps; see `WINDOW_WEAK_TYPE_STATUS_S9.md`.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- `Σ_t ‖f t x‖ₑ²`, the square of the `ℓ²`-norm of `f · x`. -/
noncomputable def ell2Sq {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑ t, ‖f t x‖ₑ ^ (2 : ℝ)

/-- `Σ_t (dyMax (‖f t ·‖ₑ) x)²`, the square of the `ℓ²`-norm of the componentwise dyadic maximal
function. -/
noncomputable def ell2Max {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) : ℝ≥0∞ :=
  ∑ t, (dyMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)

lemma ell2Max_measurable {n : ℕ} (f : Fin n → ℝ → ℝ) : Measurable (ell2Max f) := by
  unfold ell2Max
  refine Finset.measurable_sum _ fun t _ => ?_
  exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp (dyMax_measurable _)

/-- The dyadic maximal function is bounded by the supremum of the function. -/
lemma dyMax_le_iSup (φ : ℝ → ℝ≥0∞) (x : ℝ) : dyMax φ x ≤ ⨆ y, φ y := by
  unfold dyMax
  refine iSup_le fun n => iSup_le fun k => iSup_le fun _ => ?_
  have h1 : ∫⁻ y in dyCell n k, φ y ≤ ENNReal.ofReal ((2 : ℝ) ^ n) * ⨆ z, φ z := by
    calc ∫⁻ y in dyCell n k, φ y
        ≤ ∫⁻ _y in dyCell n k, (⨆ z, φ z) := lintegral_mono fun y => le_iSup φ y
      _ = (⨆ z, φ z) * volume (dyCell n k) := setLIntegral_const _ _
      _ = (⨆ z, φ z) * ENNReal.ofReal ((2 : ℝ) ^ n) := by
            rw [dyCell, Real.volume_Ico, dyCell_len]
      _ = ENNReal.ofReal ((2 : ℝ) ^ n) * (⨆ z, φ z) := mul_comm _ _
  calc ENNReal.ofReal ((2 : ℝ) ^ n)⁻¹ * ∫⁻ y in dyCell n k, φ y
      ≤ ENNReal.ofReal ((2 : ℝ) ^ n)⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ n) * ⨆ z, φ z) :=
        mul_le_mul_right h1 _
    _ = ⨆ z, φ z := by
        rw [ENNReal.ofReal_inv_of_pos (zpow_two_pos n), ← mul_assoc,
          ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (zpow_two_pos n)).ne'
            ENNReal.ofReal_ne_top, one_mul]

/-- The trivial `ℓ^∞(ℓ²)` endpoint. -/
lemma ell2Max_le_sup {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) :
    ell2Max f x ≤ ∑ t, (⨆ y, ‖f t y‖ₑ) ^ (2 : ℝ) := by
  unfold ell2Max
  exact Finset.sum_le_sum fun t _ =>
    ENNReal.rpow_le_rpow (dyMax_le_iSup _ x) (by norm_num)

/-- **The `L²(ℓ²)` endpoint** of the vector-valued dyadic maximal inequality: it is the sum of the
scalar `L²` bounds of `dyMax`. -/
theorem lintegral_ell2Max_le {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Fin n → ℝ → ℝ), (∀ t, Measurable (f t)) →
      ∫⁻ x, ell2Max f x ≤ ENNReal.ofReal (C ^ (2 : ℝ)) * ∫⁻ x, ell2Sq f x := by
  obtain ⟨C, hC, hb⟩ := dyMax_strong_type 2 (by norm_num : (1 : ℝ) < 2)
  refine ⟨C, hC, fun f hf => ?_⟩
  have hsum : ∫⁻ x, ell2Max f x
      = ∑ t : Fin n, ∫⁻ x, (dyMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ) := by
    unfold ell2Max
    rw [MeasureTheory.lintegral_finsetSum]
    intro t _
    exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp
      (dyMax_measurable _)
  have hSq : ∫⁻ x, ell2Sq f x = ∑ t : Fin n, ∫⁻ x, ‖f t x‖ₑ ^ (2 : ℝ) := by
    unfold ell2Sq
    rw [MeasureTheory.lintegral_finsetSum]
    intro t _
    exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp (hf t).enorm
  rw [hsum, hSq, Finset.mul_sum]
  exact Finset.sum_le_sum fun t _ => hb (f t)

end Work.BourgainPlan.Maximal
