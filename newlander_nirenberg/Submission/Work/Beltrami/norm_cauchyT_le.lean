import Mathlib
import Submission.Work.Beltrami.Cauchy

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff
open scoped Real
open Work.Beltrami

noncomputable section

/-- The unit disc in `ℂ` (identified with `ℝ²`) has measure `π`. -/
lemma volume_real_ball_one : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
  rw [Measure.real, Complex.volume_ball]
  norm_num

/-- `w ↦ ‖w‖⁻¹` is integrable on every ball, being `L¹` at the origin in the plane. -/
lemma integrableOn_norm_inv_ball (a : ℂ) (R : ℝ) :
    IntegrableOn (fun w : ℂ => ‖w‖⁻¹) (Metric.ball a R) := by
  have hsub : Metric.ball a R ⊆ Metric.ball (0:ℂ) (R + ‖a‖) := by
    apply Metric.ball_subset_ball'; simp
  refine IntegrableOn.mono_set ?_ hsub
  rw [show (fun w : ℂ => ‖w‖⁻¹) = (fun w => (fun y : ℝ => y⁻¹) ‖w‖) from rfl]
  rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ) (f := fun y : ℝ => y⁻¹)
    (r := R + ‖a‖)]
  rw [Complex.finrank_real_complex]
  norm_num
  refine IntegrableOn.congr_fun (f := fun _ : ℝ => (1:ℝ)) ?_ ?_ measurableSet_Ioo
  · exact integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top.ne) (by simp)
  · intro y hy
    rw [Set.mem_Ioo] at hy
    change (1:ℝ) = y * y⁻¹
    exact (mul_inv_cancel₀ (ne_of_gt hy.1)).symm

/-- The function `‖·‖⁻¹`, cut off by the indicator of a ball, is integrable. -/
lemma integrable_indicator_norm_inv (a : ℂ) (R : ℝ) :
    Integrable ((Metric.ball a R).indicator (fun w : ℂ => ‖w‖⁻¹)) := by
  rw [integrable_indicator_iff Metric.isOpen_ball.measurableSet]
  exact integrableOn_norm_inv_ball a R

/-- **Polar-coordinate computation.**  `∫_{‖w‖ ≤ ρ} ‖w‖⁻¹ dA(w) = 2πρ` for `ρ ≥ 0`,
where `dA` is Lebesgue measure on `ℂ ≅ ℝ²`.  The normalization `dA = 2π r dr dθ`
is exactly `dim_ℝ ℂ = 2` and `volume (ball 0 1) = π`. -/
lemma integral_ball_norm_inv (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∫ w in Metric.ball (0:ℂ) ρ, ‖w‖⁻¹ = 2 * Real.pi * ρ := by
  classical
  rw [← integral_indicator Metric.isOpen_ball.measurableSet]
  have hfun : (fun w : ℂ => (Metric.ball (0:ℂ) ρ).indicator (fun w => ‖w‖⁻¹) w)
      = (fun w : ℂ => (fun y : ℝ => if y < ρ then y⁻¹ else 0) ‖w‖) := by
    funext w
    rw [Set.indicator_apply]
    change (if w ∈ Metric.ball (0:ℂ) ρ then ‖w‖⁻¹ else 0) = (if ‖w‖ < ρ then ‖w‖⁻¹ else 0)
    have hmem : (w ∈ Metric.ball (0:ℂ) ρ) ↔ ‖w‖ < ρ := by
      simp [Metric.mem_ball, dist_eq_norm]
    by_cases h : ‖w‖ < ρ
    · rw [if_pos h, if_pos (hmem.mpr h)]
    · rw [if_neg h, if_neg (fun hc => h (hmem.mp hc))]
  rw [hfun, integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun y : ℝ => if y < ρ then y⁻¹ else 0)]
  rw [Complex.finrank_real_complex, volume_real_ball_one]
  have hinner : ∫ y in Set.Ioi (0:ℝ), y ^ (2 - 1) • (if y < ρ then y⁻¹ else 0)
      = ∫ y in Set.Ioi (0:ℝ), (if y < ρ then (1:ℝ) else 0) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    rw [Set.mem_Ioi] at hy
    change y ^ (2 - 1) • (if y < ρ then y⁻¹ else 0) = (if y < ρ then (1:ℝ) else 0)
    have h2 : (2 - 1 : ℕ) = 1 := rfl
    rw [h2, pow_one, smul_eq_mul]
    by_cases h : y < ρ
    · rw [if_pos h, if_pos h, mul_inv_cancel₀ (ne_of_gt hy)]
    · rw [if_neg h, if_neg h, mul_zero]
  rw [hinner]
  rw [show ∫ y in Set.Ioi (0:ℝ), (if y < ρ then (1:ℝ) else 0) = ρ from ?_]
  · simp only [nsmul_eq_mul, smul_eq_mul]; ring
  · rw [← integral_indicator measurableSet_Ioi]
    have hfun2 : (Set.Ioi (0:ℝ)).indicator (fun y : ℝ => if y < ρ then (1:ℝ) else 0)
        = (Set.Ioo (0:ℝ) ρ).indicator (fun _ => (1:ℝ)) := by
      funext y
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hy : y ∈ Set.Ioi (0:ℝ)
      · rw [if_pos hy]
        rw [Set.mem_Ioi] at hy
        have hmem : (y ∈ Set.Ioo (0:ℝ) ρ) ↔ y < ρ := by
          rw [Set.mem_Ioo]; exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
        by_cases h : y < ρ
        · rw [if_pos h, if_pos (hmem.mpr h)]
        · rw [if_neg h, if_neg (fun hc => h (hmem.mp hc))]
      · rw [if_neg hy]
        have hmem : ¬ (y ∈ Set.Ioo (0:ℝ) ρ) := by
          intro hc; exact hy (Set.mem_Ioi.mpr (Set.mem_Ioo.mp hc).1)
        rw [if_neg hmem]
    rw [hfun2, integral_indicator_const (1:ℝ) measurableSet_Ioo, Measure.real, Real.volume_Ioo]
    rw [sub_zero, ENNReal.toReal_ofReal hρ, smul_eq_mul, mul_one]

/-- Integrability of the Cauchy kernel cut off by a disc *not* centred at the singularity:
the translate of the previous integrand. -/
lemma integrable_indicator_norm_sub_inv (z : ℂ) (ρ : ℝ) :
    Integrable (fun ζ : ℂ => (Metric.ball (0:ℂ) ρ).indicator (fun ζ => ‖ζ - z‖⁻¹) ζ) := by
  classical
  haveI : (volume : Measure ℂ).IsAddRightInvariant :=
    MeasureTheory.IsAddLeftInvariant.isAddRightInvariant
  have hG : Integrable ((Metric.ball (-z) ρ).indicator (fun w : ℂ => ‖w‖⁻¹)) :=
    integrable_indicator_norm_inv (-z) ρ
  have hcomp : Integrable
      (fun ζ : ℂ => (Metric.ball (-z) ρ).indicator (fun w : ℂ => ‖w‖⁻¹) (ζ - z)) :=
    hG.comp_sub_right z
  refine hcomp.congr ?_
  filter_upwards with ζ
  rw [Set.indicator_apply, Set.indicator_apply]
  have hmem : (ζ - z ∈ Metric.ball (-z) ρ) ↔ ζ ∈ Metric.ball (0:ℂ) ρ := by
    simp only [Metric.mem_ball, dist_eq_norm]
    rw [show ζ - z - (-z) = ζ - 0 from by ring]
  by_cases h : ζ ∈ Metric.ball (0:ℂ) ρ
  · rw [if_pos (hmem.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hmem.mp hc)), if_neg h]

/-- **Uniform bound for the Cauchy potential kernel.**  The integral of `‖w‖⁻¹` over an
arbitrary disc of radius `R` is bounded by `3π(1 + R)`, uniformly in the centre: the part
of the disc meeting the unit disc around the origin contributes at most the centred
integral `2π(1+R)`, and the rest at most `(1+R)⁻¹ · πR² ≤ π(1+R)`. -/
lemma integral_ball_norm_inv_le (a : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∫ w in Metric.ball a R, ‖w‖⁻¹ ≤ 3 * Real.pi * (1 + R) := by
  classical
  have hpos : (0:ℝ) < 1 + R := by linarith
  have hind_int : Integrable ((Metric.ball a R).indicator (fun _ : ℂ => (1:ℝ))) := by
    rw [integrable_indicator_iff Metric.isOpen_ball.measurableSet]
    exact integrableOn_const measure_ball_lt_top.ne (by simp)
  have hg1_int : Integrable ((Metric.ball (0:ℂ) (1+R)).indicator (fun w : ℂ => ‖w‖⁻¹)) :=
    integrable_indicator_norm_inv 0 (1+R)
  have hg2_int : Integrable
      (fun w : ℂ => (1+R)⁻¹ * ((Metric.ball a R).indicator (fun _ : ℂ => (1:ℝ)) w)) :=
    hind_int.const_mul _
  have hle : ∀ w : ℂ, (Metric.ball a R).indicator (fun w => ‖w‖⁻¹) w ≤
      (Metric.ball (0:ℂ) (1+R)).indicator (fun w => ‖w‖⁻¹) w
        + (1+R)⁻¹ * ((Metric.ball a R).indicator (fun _ : ℂ => (1:ℝ)) w) := by
    intro w
    by_cases hw : w ∈ Metric.ball a R
    · rw [Set.indicator_of_mem hw]
      by_cases h2 : w ∈ Metric.ball (0:ℂ) (1+R)
      · rw [Set.indicator_of_mem h2, Set.indicator_of_mem hw]
        have h3 : 0 ≤ (1+R)⁻¹ := by positivity
        nlinarith [norm_nonneg w]
      · rw [Set.indicator_of_notMem h2, Set.indicator_of_mem hw, zero_add, mul_one]
        have hge : 1 + R ≤ ‖w‖ := by
          rw [Metric.mem_ball, not_lt, dist_eq_norm] at h2
          simpa [sub_zero] using h2
        exact (inv_le_inv₀ (by linarith : (0:ℝ) < ‖w‖) hpos).mpr hge
    · rw [Set.indicator_of_notMem hw]
      apply add_nonneg
      · exact Set.indicator_nonneg (fun _ _ => by positivity) w
      · exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => by positivity) w)
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun w => Set.indicator_nonneg (fun _ _ => by positivity) w))
    (hg1_int.add hg2_int) (Filter.Eventually.of_forall hle)
  simp only [Pi.add_apply] at hmono
  rw [integral_add hg1_int hg2_int] at hmono
  have hg1_val : ∫ w, (Metric.ball (0:ℂ) (1+R)).indicator (fun w : ℂ => ‖w‖⁻¹) w
      = 2 * Real.pi * (1+R) := by
    rw [integral_indicator Metric.isOpen_ball.measurableSet]
    exact integral_ball_norm_inv (1+R) (by linarith)
  have hg2_val : ∫ w, (1+R)⁻¹ * ((Metric.ball a R).indicator (fun _ : ℂ => (1:ℝ)) w)
      = (1+R)⁻¹ * (R^2 * Real.pi) := by
    rw [integral_const_mul]
    congr 1
    rw [integral_indicator_const (1:ℝ) Metric.isOpen_ball.measurableSet]
    rw [show (volume : Measure ℂ).real (Metric.ball a R) = R^2 * Real.pi from by
      rw [Measure.real, Complex.volume_ball, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hR]
      simp]
    rw [smul_eq_mul, mul_one]
  rw [hg1_val, hg2_val] at hmono
  rw [integral_indicator Metric.isOpen_ball.measurableSet] at hmono
  have hbound : (1+R)⁻¹ * (R^2 * Real.pi) ≤ Real.pi * (1+R) := by
    rw [← div_eq_inv_mul, div_le_iff₀ hpos]
    nlinarith [Real.pi_pos, hR, sq_nonneg R, sq_nonneg (1+R)]
  linarith [hmono, hbound]

/-- **Translation identity for the Cauchy kernel.**  Integrating `ζ ↦ ‖ζ - z‖⁻¹` over the
disc of radius `R` centred at `0` is the same as integrating `w ↦ ‖w‖⁻¹` over the disc of
radius `R` centred at `-z`. -/
lemma integral_ball_sub_norm_inv (z : ℂ) (R : ℝ) :
    ∫ ζ in Metric.ball (0:ℂ) R, ‖ζ - z‖⁻¹ = ∫ w in Metric.ball (-z) R, ‖w‖⁻¹ := by
  classical
  haveI : (volume : Measure ℂ).IsAddRightInvariant :=
    MeasureTheory.IsAddLeftInvariant.isAddRightInvariant
  rw [← integral_indicator Metric.isOpen_ball.measurableSet (f := fun ζ => ‖ζ - z‖⁻¹),
      ← integral_indicator Metric.isOpen_ball.measurableSet (f := fun w : ℂ => ‖w‖⁻¹)]
  rw [← integral_add_right_eq_self
    (fun ζ : ℂ => (Metric.ball (0:ℂ) R).indicator (fun ζ => ‖ζ - z‖⁻¹) ζ) z]
  congr 1
  funext w
  rw [Set.indicator_apply, Set.indicator_apply]
  change (if w + z ∈ Metric.ball (0:ℂ) R then ‖(w + z) - z‖⁻¹ else 0)
      = (if w ∈ Metric.ball (-z) R then ‖w‖⁻¹ else 0)
  have hmem : (w + z ∈ Metric.ball (0:ℂ) R) ↔ w ∈ Metric.ball (-z) R := by
    simp only [Metric.mem_ball, dist_eq_norm]
    rw [show w + z - 0 = w - (-z) from by ring]
  rw [show ‖(w + z) - z‖⁻¹ = ‖w‖⁻¹ from by rw [show w + z - z = w from by ring]]
  by_cases h : w ∈ Metric.ball (-z) R
  · rw [if_pos (hmem.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hmem.mp hc)), if_neg h]

/-- The potential kernel bound on the disc `‖ζ‖ < R + 1` around the origin: replacing `R`
by `R + 1` makes the region contain the closed disc of radius `R`, which is what the
support hypothesis needs. -/
lemma integral_ball_norm_sub_inv_le (z : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∫ ζ in Metric.ball (0:ℂ) (R+1), ‖ζ - z‖⁻¹ ≤ 6 * Real.pi * (1 + R) := by
  rw [integral_ball_sub_norm_inv z (R+1)]
  have h2 : ∫ w in Metric.ball (-z) (R+1), ‖w‖⁻¹ ≤ 3 * Real.pi * (1 + (R+1)) :=
    integral_ball_norm_inv_le (-z) (R+1) (by linarith)
  have h3 : (3:ℝ) * Real.pi * (1 + (R+1)) ≤ 6 * Real.pi * (1 + R) := by
    nlinarith [Real.pi_pos]
  linarith

/-- **Potential bound for the Cauchy transform.**  If `f` is continuous, bounded by `M` and
supported in the disc of radius `R ≥ 0`, then the Cauchy potential `cauchyT f` is bounded by
`C * M * (1 + R)` uniformly on `ℂ`, with `C` independent of `f`, `M`, `R`.
The proof is the elementary kernel estimate `∫_{‖ζ‖ ≤ R} ‖ζ - z‖⁻¹ dA(ζ) ≤ C (1 + R)`,
the kernel `ζ ↦ (ζ - z)⁻¹` being locally integrable in the plane. -/
theorem norm_cauchyT_le (f : ℂ → ℂ) (hf : Continuous f) {M R : ℝ} (hR : 0 ≤ R)
    (hM : ∀ z, ‖f z‖ ≤ M) (hsupp : ∀ z, R < ‖z‖ → f z = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ z, ‖cauchyT f z‖ ≤ C * M * (1 + R) := by
  classical
  refine ⟨6, by norm_num, ?_⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (f 0)) (hM 0)
  intro z
  have hstep1 : ‖cauchyT f z‖ = (Real.pi)⁻¹ * ‖∫ ζ, (ζ - z)⁻¹ * f ζ ∂volume‖ := by
    rw [cauchyT_apply, norm_smul]
    congr 1
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (inv_nonneg.mpr Real.pi_pos.le)]
  have hle : ∀ ζ : ℂ, ‖(ζ - z)⁻¹ * f ζ‖ ≤
      M * (Metric.ball (0:ℂ) (R+1)).indicator (fun ζ => ‖ζ - z‖⁻¹) ζ := by
    intro ζ
    by_cases h : ζ ∈ Metric.ball (0:ℂ) (R+1)
    · rw [Set.indicator_of_mem h]
      rw [show ‖(ζ - z)⁻¹ * f ζ‖ = ‖f ζ‖ * ‖ζ - z‖⁻¹ from by
        rw [norm_mul, norm_inv, mul_comm]]
      exact mul_le_mul_of_nonneg_right (hM ζ) (inv_nonneg.mpr (norm_nonneg _))
    · rw [Set.indicator_of_notMem h]
      have hf0 : f ζ = 0 := hsupp ζ (by
        rw [Metric.mem_ball, not_lt, dist_eq_norm] at h
        have : R + 1 ≤ ‖ζ‖ := by simpa [sub_zero] using h
        linarith)
      simp [hf0]
  have hint : Integrable
      (fun ζ : ℂ => M * (Metric.ball (0:ℂ) (R+1)).indicator (fun ζ => ‖ζ - z‖⁻¹) ζ) :=
    (integrable_indicator_norm_sub_inv z (R+1)).const_mul M
  have hJ0 := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun ζ => norm_nonneg _))
    hint (Filter.Eventually.of_forall hle)
  rw [integral_const_mul] at hJ0
  rw [integral_indicator Metric.isOpen_ball.measurableSet] at hJ0
  have hJ : ∫ ζ, ‖(ζ - z)⁻¹ * f ζ‖ ∂volume ≤ M * (6 * Real.pi * (1 + R)) := by
    have hp := integral_ball_norm_sub_inv_le z R hR
    nlinarith [hJ0, mul_le_mul_of_nonneg_left hp hM0]
  rw [hstep1]
  calc (Real.pi)⁻¹ * ‖∫ ζ, (ζ - z)⁻¹ * f ζ ∂volume‖
      ≤ (Real.pi)⁻¹ * ∫ ζ, ‖(ζ - z)⁻¹ * f ζ‖ ∂volume :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
          (inv_nonneg.mpr Real.pi_pos.le)
    _ ≤ (Real.pi)⁻¹ * (M * (6 * Real.pi * (1 + R))) :=
        mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr Real.pi_pos.le)
    _ = 6 * M * (1 + R) := by
        have hp : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp

end

end Work.Beltrami
