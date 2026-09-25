import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace Commons.Analysis.ExpLog

/-- Elementary growth bound: for `a ≥ 1 ≤ u`, the tenth power `(u/a)^10` is
dominated by `40^10 · exp ((u − a)/4)`.

Proof: `10·log(x/40) ≤ 10·(x/40 − 1) = x/4 − 10 ≤ (x−1)/4` (with `x = u/a`),
then exponentiate. -/
private lemma pow_le_exp_four (a u : ℝ) (ha1 : 1 ≤ a) (hau : a ≤ u) :
    (u / a) ^ 10 ≤ (40 : ℝ) ^ 10 * Real.exp ((u - a) / 4) := by
  let x : ℝ := u / a
  have ha_pos : 0 < a := by linarith
  have hu_pos : 0 < u := by linarith
  have hxpos : 0 < x := by
    dsimp [x]
    exact div_pos hu_pos ha_pos
  have hlog : Real.log (x / 40) ≤ x / 40 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity : 0 < x / 40)
  have h1 : 10 * Real.log (x / 40) ≤ 10 * (x / 40 - 1) := by
    exact mul_le_mul_of_nonneg_left hlog (by norm_num)
  have h2 : 10 * (x / 40 - 1) ≤ (x - 1) / 4 := by
    ring_nf
    linarith
  have hExp : Real.exp (10 * Real.log (x / 40)) ≤ Real.exp ((x - 1) / 4) := by
    exact Real.exp_le_exp_of_le (le_trans h1 h2)
  have hEq : Real.exp (10 * Real.log (x / 40)) = (x / 40) ^ 10 := by
    have h10 : (10 : ℝ) = ((10 : ℕ) : ℝ) := by norm_num
    rw [h10, Real.exp_nat_mul]
    rw [Real.exp_log (by positivity : 0 < x / 40)]
  have hlow : (x / 40) ^ 10 ≤ Real.exp ((x - 1) / 4) := by
    exact (le_of_eq hEq.symm).trans hExp
  have hc : (0 : ℝ) ≤ (40 : ℝ) ^ 10 := by positivity
  have hxeq : x ^ 10 = (40 : ℝ) ^ 10 * (x / 40) ^ 10 := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hX : x ^ 10 ≤ (40 : ℝ) ^ 10 * Real.exp ((x - 1) / 4) := by
    calc
      x ^ 10 = (40 : ℝ) ^ 10 * (x / 40) ^ 10 := hxeq
      _ ≤ (40 : ℝ) ^ 10 * Real.exp ((x - 1) / 4) := by
        exact mul_le_mul_of_nonneg_left hlow hc
  have harg : (x - 1) / 4 = (u - a) / (4 * a) := by
    dsimp [x]
    field_simp [ha_pos.ne']
  have harg2 : (u - a) / (4 * a) ≤ (u - a) / 4 := by
    have hdiv : (1 : ℝ) / a ≤ 1 := (div_le_iff₀ ha_pos).mpr (by simpa using ha1)
    have hua : 0 ≤ u - a := sub_nonneg.mpr hau
    have h : (u - a) / a ≤ u - a := by
      calc
        (u - a) / a = (u - a) * (1 / a) := by ring
        _ ≤ (u - a) * 1 := mul_le_mul_of_nonneg_left hdiv hua
        _ = u - a := by ring
    calc
      (u - a) / (4 * a) = ((u - a) / a) / 4 := by field_simp [ha_pos.ne']
      _ ≤ (u - a) / 4 := div_le_div_of_nonneg_right h (by norm_num)
  have hArg : (x - 1) / 4 ≤ (u - a) / 4 := by
    rw [harg]
    exact harg2
  calc
    (u / a) ^ 10 = x ^ 10 := by rfl
    _ ≤ (40 : ℝ) ^ 10 * Real.exp ((x - 1) / 4) := hX
    _ ≤ (40 : ℝ) ^ 10 * Real.exp ((u - a) / 4) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le hArg)
        (by positivity : (0 : ℝ) ≤ (40 : ℝ) ^ 10)

/-- Pointwise domination of the integrand: for `a ≥ 1 ≤ u`,
`u^10 · e^{−u/2} ≤ 40^10 · a^10 · e^{−a/2} · e^{−(u−a)/4}`. -/
private lemma tail_pointwise (a u : ℝ) (ha1 : 1 ≤ a) (hau : a ≤ u) :
    u ^ 10 * Real.exp (-(u / 2)) ≤
      (40 : ℝ) ^ 10 * a ^ 10 * Real.exp (-(a / 2)) * Real.exp (-((u - a) / 4)) := by
  have hp := pow_le_exp_four a u ha1 hau
  have ha_pos : 0 < a := by linarith
  have ha0 : a ≠ 0 := ne_of_gt ha_pos
  have hratio : (u / a) ^ 10 * a ^ 10 = u ^ 10 := by
    rw [← mul_pow]
    rw [div_mul_cancel₀ u ha0]
  have hc2 : 0 ≤ Real.exp (-(u / 2)) := Real.exp_nonneg (-(u / 2))
  have hmul : (u / a) ^ 10 * a ^ 10 * Real.exp (-(u / 2)) ≤
      ((40 : ℝ) ^ 10 * Real.exp ((u - a) / 4)) * a ^ 10 * Real.exp (-(u / 2)) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hp (pow_nonneg ha_pos.le 10)) hc2
  have hexp : Real.exp ((u - a) / 4) * Real.exp (-(u / 2)) = Real.exp (-(u + a) / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  have hexp2 : Real.exp (-(a / 2)) * Real.exp (-((u - a) / 4)) = Real.exp (-(u + a) / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring_nf
  have hRHS : (40 : ℝ) ^ 10 * Real.exp ((u - a) / 4) * a ^ 10 * Real.exp (-(u / 2)) =
      (40 : ℝ) ^ 10 * a ^ 10 * Real.exp (-(a / 2)) * Real.exp (-((u - a) / 4)) := by
    calc
      (40 : ℝ) ^ 10 * Real.exp ((u - a) / 4) * a ^ 10 * Real.exp (-(u / 2))
          = (40 : ℝ) ^ 10 * a ^ 10 * (Real.exp ((u - a) / 4) * Real.exp (-(u / 2))) := by ring
      _ = (40 : ℝ) ^ 10 * a ^ 10 * Real.exp (-(u + a) / 4) := by rw [hexp]
      _ = (40 : ℝ) ^ 10 * a ^ 10 * Real.exp (-(a / 2)) * Real.exp (-((u - a) / 4)) := by
          rw [hexp2.symm]
          ring
  calc
    u ^ 10 * Real.exp (-(u / 2)) = (u / a) ^ 10 * a ^ 10 * Real.exp (-(u / 2)) := by
      rw [← hratio]
    _ ≤ (40 : ℝ) ^ 10 * a ^ 10 * Real.exp (-(a / 2)) * Real.exp (-((u - a) / 4)) := by
      rw [← hRHS]
      exact hmul

/-- `e^{−u/4}` is integrable on `(a, ∞)`. -/
private lemma integrableOn_exp_div4 (a : ℝ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (-(u / 4))) (Set.Ioi a) := by
  have h := integrableOn_exp_mul_Ioi (a := -(1 / 4 : ℝ)) (by norm_num) (c := a)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro u hu
  dsimp only
  congr 1
  ring

/-- `e^{−(u−a)/4}` is integrable on `(a, ∞)`. -/
private lemma integrableOn_exp_shift_div4 (a : ℝ) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (-((u - a) / 4))) (Set.Ioi a) := by
  have h2 := integrableOn_exp_div4 a
  have hcm : MeasureTheory.Integrable (fun u : ℝ => Real.exp (a / 4) * Real.exp (-(u / 4)))
      (volume.restrict (Set.Ioi a)) :=
    MeasureTheory.Integrable.const_mul (𝕜 := ℝ) h2 (Real.exp (a / 4))
  have hcmOn : MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (a / 4) * Real.exp (-(u / 4)))
      (Set.Ioi a) := hcm
  refine hcmOn.congr_fun ?_ measurableSet_Ioi
  intro u hu
  dsimp only
  rw [← Real.exp_add]
  congr 1
  ring_nf

/-- `∫_a^∞ e^{−u/4} du = 4·e^{−a/4}`. -/
private lemma integral_exp_div4 (a : ℝ) :
    (∫ u : ℝ in Set.Ioi a, Real.exp (-(u / 4))) = 4 * Real.exp (-(a / 4)) := by
  have h' := integral_exp_mul_Ioi (a := -(1 / 4 : ℝ)) (by norm_num) (c := a)
  have harg_a : Real.exp ((-(1 / 4)) * a) = Real.exp (-(a / 4)) := by
    congr 1
    ring
  calc
    (∫ u : ℝ in Set.Ioi a, Real.exp (-(u / 4)))
        = ∫ u : ℝ in Set.Ioi a, Real.exp ((-(1 / 4)) * u) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro u hu
            dsimp only
            congr 1
            ring
    _ = 4 * Real.exp (-(a / 4)) := by
            rw [h', harg_a]
            ring_nf

/-- `∫_a^∞ e^{−(u−a)/4} du = 4`, independent of `a`. -/
private lemma integral_exp_shift_div4 (a : ℝ) :
    (∫ u : ℝ in Set.Ioi a, Real.exp (-((u - a) / 4))) = 4 := by
  have h := integral_exp_div4 a
  calc
    (∫ u : ℝ in Set.Ioi a, Real.exp (-((u - a) / 4)))
        = ∫ u : ℝ in Set.Ioi a, Real.exp (a / 4) * Real.exp (-(u / 4)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro u hu
            dsimp only
            rw [← Real.exp_add]
            congr 1
            ring_nf
    _ = Real.exp (a / 4) * (∫ u : ℝ in Set.Ioi a, Real.exp (-(u / 4))) := by
            exact MeasureTheory.integral_const_mul (Real.exp (a / 4))
              (fun u : ℝ => Real.exp (-(u / 4)))
    _ = 4 := by
            rw [h]
            have harg : Real.exp (a / 4) * Real.exp (-(a / 4)) = 1 := by
              rw [← Real.exp_add]
              ring_nf
              simp
            calc
              Real.exp (a / 4) * (4 * Real.exp (-(a / 4)))
                  = 4 * (Real.exp (a / 4) * Real.exp (-(a / 4))) := by ring
              _ = 4 * 1 := by rw [harg]
              _ = 4 := by ring

theorem tail_pow_exp_neg_bound_exists :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℝ, 1 ≤ a →
      (∫ u : ℝ in Set.Ioi a, u ^ 10 * Real.exp (-(u / 2))) ≤
        K * a ^ 10 * Real.exp (-(a / 2)) := by
  refine ⟨4 * (40 : ℝ) ^ 10, ?_, ?_⟩
  · positivity
  · intro a ha1
    let K : ℝ := 4 * (40 : ℝ) ^ 10
    let c : ℝ := (40 : ℝ) ^ 10 * a ^ 10 * Real.exp (-(a / 2))
    let f : ℝ → ℝ := fun u => u ^ 10 * Real.exp (-(u / 2))
    let g : ℝ → ℝ := fun u => c * Real.exp (-((u - a) / 4))
    have ha_pos : 0 < a := by linarith
    -- pointwise inequality f ≤ g on (a, ∞)
    have hpt : ∀ u : ℝ, u ∈ Set.Ioi a → f u ≤ g u := by
      intro u hu
      dsimp [f, g, c]
      exact tail_pointwise a u ha1 (le_of_lt hu)
    -- integrability of g
    have hb := integrableOn_exp_shift_div4 a
    have hgI : MeasureTheory.Integrable
        (fun u : ℝ => c * Real.exp (-((u - a) / 4))) (volume.restrict (Set.Ioi a)) :=
      MeasureTheory.Integrable.const_mul (𝕜 := ℝ) hb c
    have hg_in : MeasureTheory.IntegrableOn g (Set.Ioi a) := by
      dsimp [g]
      exact hgI
    -- f is continuous hence measurable
    have hf_cont : Continuous f := by
      dsimp [f]
      fun_prop
    have hf_meas : MeasureTheory.AEStronglyMeasurable f (volume.restrict (Set.Ioi a)) :=
      hf_cont.aestronglyMeasurable
    -- norm domination ‖f‖ ≤ ‖g‖ a.e. on (a, ∞)
    have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioi a)), ‖f u‖ ≤ ‖g u‖ := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have hptu : f u ≤ g u := hpt u hu
      have hau : a < u := Set.mem_Ioi.mp hu
      have hu0 : 0 ≤ u := by linarith
      have hf0 : 0 ≤ f u := by
        dsimp [f]
        exact mul_nonneg (pow_nonneg hu0 10) (Real.exp_nonneg (-(u / 2)))
      have hg0 : 0 ≤ g u := by
        dsimp [g]
        exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) 10)
          (pow_nonneg ha_pos.le 10)) (Real.exp_nonneg (-(a / 2)))) (Real.exp_nonneg (-((u - a) / 4)))
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_nonneg hf0, abs_of_nonneg hg0]
      exact hptu
    have hf_in : MeasureTheory.Integrable f (volume.restrict (Set.Ioi a)) :=
      MeasureTheory.Integrable.mono hg_in hf_meas hbound
    -- a.e. inequality for the integrals
    have hle_ae : f ≤ᵐ[volume.restrict (Set.Ioi a)] g := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      exact hpt u hu
    have hmono : (∫ u : ℝ in Set.Ioi a, f u) ≤ (∫ u : ℝ in Set.Ioi a, g u) := by
      exact MeasureTheory.integral_mono_ae hf_in hg_in hle_ae
    -- value of ∫ g
    have hbase := integral_exp_shift_div4 a
    have hg_val : (∫ u : ℝ in Set.Ioi a, g u) = K * a ^ 10 * Real.exp (-(a / 2)) := by
      calc
        (∫ u : ℝ in Set.Ioi a, g u)
            = ∫ u : ℝ in Set.Ioi a, c * Real.exp (-((u - a) / 4)) := by rfl
        _ = c * (∫ u : ℝ in Set.Ioi a, Real.exp (-((u - a) / 4))) := by
            exact MeasureTheory.integral_const_mul c (fun u : ℝ => Real.exp (-((u - a) / 4)))
        _ = c * 4 := by rw [hbase]
        _ = K * a ^ 10 * Real.exp (-(a / 2)) := by
            dsimp [c, K]
            ring
    calc
      (∫ u : ℝ in Set.Ioi a, u ^ 10 * Real.exp (-(u / 2)))
          = (∫ u : ℝ in Set.Ioi a, f u) := by rfl
      _ ≤ (∫ u : ℝ in Set.Ioi a, g u) := hmono
      _ = K * a ^ 10 * Real.exp (-(a / 2)) := hg_val

end Commons.Analysis.ExpLog
