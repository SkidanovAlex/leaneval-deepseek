import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.NK.NUV2.Minkowski.volume_thickening_box_image_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.Minkowski

open scoped Classical Pointwise
open MeasureTheory

/-- **Minkowski content of a Lipschitz image of the unit box.** Let `g : (ι → ℝ) → (η → ℝ)`
be `L`-Lipschitz on the unit box `[0,1]^ι ⊆ ι → ℝ`, and suppose
`Fintype.card ι + k = Fintype.card η`. Then the `ε`-neighbourhood of the image of the unit box
has volume `≤ C · ε ^ k` for all `0 < ε ≤ 1`, with `C` independent of `ε`.

This is the `E = η → ℝ`, `[a,b] = [0,1]` specialisation of
`volume_thickening_box_image_le` (whose conclusion is stated with `.toReal`), together with the
observation that the thickening of the image is bounded, hence of finite volume, so that the
`ENNReal`-valued statement follows from the real-valued one. -/
theorem volume_thickening_unitBox_image_le
    {ι η : Type*} [Fintype ι] [Fintype η] {k : ℕ} (hk : Fintype.card ι + k = Fintype.card η)
    (g : (ι → ℝ) → (η → ℝ)) (L : NNReal)
    (hL : LipschitzOnWith L g (Set.univ.pi fun _ : ι => Set.Icc (0:ℝ) 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      volume {x : η → ℝ | ∃ q ∈ (Set.univ.pi fun _ : ι => Set.Icc (0:ℝ) 1), ‖x - g q‖ ≤ ε}
        ≤ ENNReal.ofReal (C * ε ^ k) := by
  classical
  have hle : Fintype.card ι ≤ Module.finrank ℝ (η → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card]
    omega
  obtain ⟨C, hCpos, hC⟩ :=
    volume_thickening_box_image_le (E := η → ℝ) (a := fun _ : ι => (0 : ℝ))
      (b := fun _ : ι => 1) (fun _ => zero_lt_one) hle g L hL
  have hexp : (Module.finrank ℝ (η → ℝ) : ℝ) - (Fintype.card ι : ℝ) = (k : ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, ← hk]
    push_cast
    ring
  refine ⟨C, hCpos, fun ε hε hε1 => ?_⟩
  have hfin : volume {x : η → ℝ | ∃ q ∈ (Set.univ.pi fun _ : ι => Set.Icc (0:ℝ) 1),
      ‖x - g q‖ ≤ ε} ≠ ⊤ := by
    have hsub : {x : η → ℝ | ∃ q ∈ (Set.univ.pi fun _ : ι => Set.Icc (0:ℝ) 1),
        ‖x - g q‖ ≤ ε} ⊆ Metric.closedBall (g 0) ((L : ℝ) + 1) := by
      rintro x ⟨q, hq, hxq⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hq1 : ‖q‖ ≤ 1 := by
        rw [pi_norm_le_iff_of_nonneg zero_le_one]
        intro i
        have hi := Set.mem_univ_pi.mp hq i
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [hi.1], hi.2⟩
      have h0mem : (0 : ι → ℝ) ∈ Set.univ.pi fun _ : ι => Set.Icc (0:ℝ) 1 := by
        rw [Set.mem_univ_pi]
        intro i
        exact ⟨le_refl (0 : ℝ), zero_le_one⟩
      have hlip : ‖g q - g 0‖ ≤ (L : ℝ) := by
        have h1 := hL.dist_le_mul q hq (0 : ι → ℝ) h0mem
        rw [dist_eq_norm, dist_eq_norm] at h1
        have hq0 : ‖q - 0‖ ≤ 1 := by simpa only [sub_zero] using hq1
        calc ‖g q - g 0‖ ≤ (L : ℝ) * ‖q - 0‖ := h1
          _ ≤ (L : ℝ) * 1 := mul_le_mul_of_nonneg_left hq0 L.coe_nonneg
          _ = (L : ℝ) := mul_one _
      calc ‖x - g 0‖ ≤ ‖x - g q‖ + ‖g q - g 0‖ := by
            rw [show x - g 0 = (x - g q) + (g q - g 0) by abel]
            exact norm_add_le _ _
        _ ≤ ε + (L : ℝ) := add_le_add hxq hlip
        _ ≤ (L : ℝ) + 1 := by linarith
    exact ne_of_lt (lt_of_le_of_lt (measure_mono hsub)
      (isCompact_closedBall (g 0) ((L : ℝ) + 1)).measure_lt_top)
  have h := hC ε hε hε1
  rw [hexp, Real.rpow_natCast] at h
  exact (ENNReal.le_ofReal_iff_toReal_le hfin (mul_nonneg hCpos.le (pow_nonneg hε.le k))).mpr h

end NK.NUV2.Minkowski
