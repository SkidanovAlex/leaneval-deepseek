import Mathlib
import Submission.Work.BW.minkowski_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Volume of the weighted `ℓ¹` ball

For `c : Fin n → ℝ` with `c i > 0`, the body `{x : Fin n → ℝ | ∑ i, c i * |x i| ≤ 1}`
has Lebesgue measure `2 ^ n / (n! * ∏ i, c i)`.

This is the first ingredient of `Work.BW.minkowski_basis` (BW §6: the volume of the
convex body `{F < 1}` for the weighted `ℓ¹` functional `F(x) = ∑ᵢ cᵢ|xᵢ|`).

The computation is split into two classical facts:

* the volume of the (unweighted) `ℓ¹` unit ball `{y | ∑ i, |y i| ≤ 1}` is `2 ^ n / n!`
  (the closed `L¹` ball of radius `1` is `2^n` copies of the standard `n`-simplex,
  or equivalently it is read off from `MeasureTheory.volume_sum_rpow_le` at `p = 1`), and
* the diagonal linear map `x ↦ (cᵢ xᵢ)` rescales Lebesgue measure by `|∏ᵢ cᵢ|`
  (`Real.map_matrix_volume_pi_eq_smul_volume_pi`).
-/

open MeasureTheory MeasureTheory.Measure Matrix

namespace Work.BW

/-- The volume of the (closed) unit ball of `∑ i, |x i|` on `ℝⁿ` is `2 ^ n / n!`. -/
lemma volume_l1_ball {n : ℕ} :
    (volume : Measure (Fin n → ℝ)) {x | ∑ i, |x i| ≤ 1} = ENNReal.ofReal (2 ^ n / n.factorial) := by
  rcases n with _ | n
  · -- `Fin 0 → ℝ` is a point and the condition `∑ i, |x i| ≤ 1` is vacuous.
    have : {x : Fin 0 → ℝ | ∑ i, |x i| ≤ 1} = Set.univ := by
      ext x; simp
    rw [this, MeasureTheory.volume_pi, Measure.pi_empty_univ]
    norm_num
  · have h := MeasureTheory.volume_sum_rpow_le (Fin (n+1)) (p := (1:ℝ)) le_rfl (1:ℝ)
    rw [show ({x : Fin (n+1) → ℝ | (∑ i, |x i| ^ (1:ℝ)) ^ (1/(1:ℝ)) ≤ 1})
        = {x | ∑ i, |x i| ≤ 1} by ext x; simp [Real.rpow_one]] at h
    rw [h, ENNReal.ofReal_one, one_pow, one_mul]
    congr 1
    have hG1 : Real.Gamma ((1:ℝ)/1 + 1) = 1 := by
      rw [show (1:ℝ)/1 + 1 = (2:ℝ) by norm_num,
          show (2:ℝ) = ((1:ℕ):ℝ) + 1 by norm_num,
          Real.Gamma_nat_eq_factorial 1]
      norm_num
    rw [Fintype.card_fin, hG1]
    rw [show (((n+1 : ℕ) : ℝ) / 1 + 1) = ((n+1 : ℕ) : ℝ) + 1 by rw [div_one]]
    rw [Real.Gamma_nat_eq_factorial (n+1)]
    ring

theorem vol_wl1_ball {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    MeasureTheory.volume.real {x : Fin n → ℝ | Work.BW.wl1 c x ≤ 1} =
      2 ^ n / ((n.factorial : ℝ) * ∏ i, c i) := by
  have hpos : 0 < ∏ i, c i := Finset.prod_pos (fun i _ => hc i)
  have hdet : (Matrix.diagonal c).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (hc i))
  -- `x ↦ (cᵢ xᵢ)` rescales Lebesgue measure by `|∏ᵢ cᵢ|`.
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  have hmeas : Measurable (Matrix.toLin' (Matrix.diagonal c)) :=
    (Matrix.toLin' (Matrix.diagonal c)).continuous_of_finiteDimensional.measurable
  have hSmeas : MeasurableSet {x : Fin n → ℝ | ∑ i, |x i| ≤ 1} := by
    apply isClosed_le _ continuous_const |>.measurableSet
    fun_prop
  -- the weighted `ℓ¹` ball is the preimage of the unweighted one.
  have hpre : Matrix.toLin' (Matrix.diagonal c) ⁻¹' {x : Fin n → ℝ | ∑ i, |x i| ≤ 1}
      = {x : Fin n → ℝ | Work.BW.wl1 c x ≤ 1} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Work.BW.wl1, Matrix.toLin'_apply]
    have hsum : (∑ i, |(diagonal c *ᵥ x) i|) = ∑ i, c i * |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mulVec_diagonal, abs_mul, abs_of_pos (hc i)]
    rw [hsum]
  rw [MeasureTheory.measureReal_def, ← hpre]
  rw [← Measure.map_apply hmeas hSmeas, hmap, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_mul, Matrix.det_diagonal, abs_of_pos (inv_pos.mpr hpos),
    ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hpos)),
    volume_l1_ball, ENNReal.toReal_ofReal (by positivity)]
  field_simp

end Work.BW
