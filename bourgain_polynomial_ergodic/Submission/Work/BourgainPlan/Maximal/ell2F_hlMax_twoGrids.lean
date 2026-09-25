import Mathlib
import Submission.Work.BourgainPlan.Maximal.ell2Maximal
import Submission.Work.BourgainPlan.Maximal.ell2MaxAux
import Submission.Work.BourgainPlan.Maximal.hlMaxTwoDyadic
import Submission.Work.BourgainPlan.Maximal.ell2Max_rpow_half_add_le
import Submission.Work.BourgainPlan.Maximal.dyMax_le_two_dyMaxShift

/-!
# The `ℓ²`-valued (`per-component`) Hardy--Littlewood maximal function is controlled by the two
# dyadic grids

Mirek--Stein--Trojan's input `(eq:47)` (the classical *vector-valued* maximal estimate for smooth
dilations) is, via `sup_r |Φ_r * f| ≤ ‖Φ‖_∞ · (ball maximal)(f)` and `hlMax` = the centred
Hardy--Littlewood maximal function, the *per-component* `ℓ²`-valued maximal inequality for `hlMax`:

`‖ (Σ_t (hlMax f_t)²)^{1/2} ‖_{L^p} ≤ C_p ‖ (Σ_t f_t²)^{1/2} ‖_{L^p}`   (`1 < p < ∞`).

Here we record the pointwise reduction of that statement to the **two** dyadic grids: the standard
grid (`dyMax`) and the half-shifted grid (`dyMaxShift (1/2)`), via the scalar two-grid transfer
`hlMaxTwoDyadic` and the `ℓ²` triangle inequality (`ENNReal_sum_sq_rpow_half_add_le`):

`(Σ_t (hlMax f_t)²)^{1/2} ≤ 4 · ( (Σ_t (dyMax f_t)²)^{1/2} + (Σ_t (dyMaxShift (1/2) f_t)²)^{1/2} )`.

Consequently the `L^p` form of the vector-valued `hlMax` inequality follows from its two dyadic-grid
instances; the standard-grid instance in the range `1 < p < 2` is `ell2MaxLpLtTwo'`, and the
half-shifted grid (a *non-laminar* grid: a level-`n` cell `[(k+1/2)2^n, (k+3/2)2^n)` straddles the
level-`n+1` boundaries) is the genuinely new object — see `WINDOW_WEAK_TYPE_STATUS_S10.md` §4.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Work.BourgainPlan.Maximal

/-- `(16 * Y) ^ (1/2) = 4 * Y ^ (1/2)` in `ℝ≥0∞` (extracting the dilation factor `4`). -/
private lemma sixteen_mul_rpow_half (Y : ℝ≥0∞) :
    (16 * Y) ^ ((1 : ℝ) / 2) = 4 * Y ^ ((1 : ℝ) / 2) := by
  have h2 : ((4 : ℝ≥0∞) * Y ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = 16 * Y := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show ((Y : ℝ≥0∞) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = Y by
      rw [← ENNReal.rpow_mul]
      norm_num]
    norm_num
  rw [← h2]
  exact (eq_rpow_half_sq _).symm

/-- **Pointwise reduction of the `ℓ²`-valued `hlMax` maximal function to the two dyadic grids.** -/
theorem ell2F_hlMax_le_twoGrids {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) :
    (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ 4 * (∑ t, ((dyMax (fun y => ‖f t y‖ₑ) x)
            + dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  set c : Fin n → ℝ≥0∞ :=
    fun t => (dyMax (fun y => ‖f t y‖ₑ) x) + dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x
  have hle : ∀ t, Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x ≤ 4 * c t :=
    fun t => hlMaxTwoDyadic _ x
  have hterm : ∀ t, (4 * c t) ^ (2 : ℝ) = 16 * (c t) ^ (2 : ℝ) := by
    intro t
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsum : (∑ t, (4 * c t) ^ (2 : ℝ)) = 16 * ∑ t, (c t) ^ (2 : ℝ) := by
    rw [Finset.sum_congr rfl (fun t _ => hterm t), Finset.mul_sum]
  calc (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ (∑ t, (4 * c t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
        refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun t _ => ?_) (by norm_num)
        exact ENNReal.rpow_le_rpow (hle t) (by norm_num)
    _ = (16 * ∑ t, (c t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by rw [hsum]
    _ = 4 * (∑ t, (c t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := sixteen_mul_rpow_half _

/-- **The separated form**: the `ℓ²`-valued `hlMax` maximal function is controlled by the two
dyadic-grid `ℓ²`-valued maximal functions separately (Minkowski in `ℝ≥0∞`). -/
theorem ell2F_hlMax_le_twoGrids_sep {n : ℕ} (f : Fin n → ℝ → ℝ) (x : ℝ) :
    (∑ t, (Commons.Analysis.Maximal.hlMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
      ≤ 4 * ((∑ t, (dyMax (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
            + (∑ t, (dyMaxShift (1 / 2) (fun y => ‖f t y‖ₑ) x) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) := by
  refine (ell2F_hlMax_le_twoGrids f x).trans ?_
  refine mul_le_mul_right ?_ 4
  exact ENNReal_sum_sq_rpow_half_add_le _ _

end Work.BourgainPlan.Maximal

namespace Work.BourgainPlan.Maximal

/-- **Every half-shifted dyadic cell average is dominated by the centred maximal function**: a
shifted cell `dyCellShift α n k` is an interval containing `x`, so its average of `φ` is at most
`hlMax φ x`.  Together with `hlMaxTwoDyadic` (`hlMax ≤ 4(dyMax + dyMaxShift 1/2)`) and
`dyMax_le_two_dyMaxShift` (`dyMax ≤ 2 dyMaxShift 1/2`), this identifies the *frontier* object of the
vector-valued maximal inequality: `hlMax ≍ dyMaxShift (1/2)` up to the universal constants
`1 ≤ · ≤ 12`. -/
theorem dyMaxShift_le_hlMax (α : ℝ) (φ : ℝ → ENNReal) (x : ℝ) :
    dyMaxShift α φ x ≤ Commons.Analysis.Maximal.hlMax φ x := by
  unfold dyMaxShift
  refine iSup_le fun n => iSup_le fun k => iSup_le fun hx => ?_
  have hlen : ((((k : ℝ) + α) + 1) * (2 : ℝ) ^ n) - (((k : ℝ) + α) * (2 : ℝ) ^ n)
      = (2 : ℝ) ^ n := by ring
  have hsub : dyCellShift α n k
      ⊆ Set.Icc (((k : ℝ) + α) * (2 : ℝ) ^ n) ((((k : ℝ) + α) + 1) * (2 : ℝ) ^ n) :=
    fun y hy => ⟨hy.1, hy.2.le⟩
  have hmono : ∫⁻ y in dyCellShift α n k, φ y
      ≤ ∫⁻ y in Set.Icc (((k : ℝ) + α) * (2 : ℝ) ^ n)
          ((((k : ℝ) + α) + 1) * (2 : ℝ) ^ n), φ y :=
    MeasureTheory.lintegral_mono_set hsub
  have hw : ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹)
      = ENNReal.ofReal ((((((k : ℝ) + α) + 1) * (2 : ℝ) ^ n)
          - (((k : ℝ) + α) * (2 : ℝ) ^ n))⁻¹) := by rw [hlen]
  rw [hw]
  refine (mul_le_mul_right hmono _).trans ?_
  exact Commons.Analysis.Maximal.hlMax_le_of_mem φ hx.1 hx.2.le

end Work.BourgainPlan.Maximal

namespace Work.BourgainPlan.Maximal

/-- **`hlMax` is the half-shifted dyadic maximal function up to the universal constant `12`.**
This is the sharp form of the identification of the frontier object: combining
`hlMaxTwoDyadic` (`hlMax ≤ 4(dyMax + dyMaxShift 1/2)`) with `dyMax_le_two_dyMaxShift`
(`dyMax ≤ 2 dyMaxShift 1/2`) and `dyMaxShift_le_hlMax` (`dyMaxShift ≤ hlMax`). -/
theorem hlMax_le_twelve_dyMaxShift (φ : ℝ → ENNReal) (x : ℝ) :
    Commons.Analysis.Maximal.hlMax φ x ≤ 12 * dyMaxShift (1 / 2) φ x := by
  calc Commons.Analysis.Maximal.hlMax φ x
      ≤ 4 * (dyMax φ x + dyMaxShift (1 / 2) φ x) := hlMaxTwoDyadic φ x
    _ ≤ 4 * (2 * dyMaxShift (1 / 2) φ x + dyMaxShift (1 / 2) φ x) := by
        refine mul_le_mul_right ?_ 4
        exact add_le_add (dyMax_le_two_dyMaxShift φ x) le_rfl
    _ = 12 * dyMaxShift (1 / 2) φ x := by ring

end Work.BourgainPlan.Maximal
