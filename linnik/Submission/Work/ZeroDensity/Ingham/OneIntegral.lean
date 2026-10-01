import Mathlib
import Submission.Work.ZeroDensity.Ingham.integrableOn_one_add_pow_mul_exp_neg

namespace Work.ZeroDensity.Ingham

open MeasureTheory Filter

theorem integralIoiPolyexpLocal (T H c₀ : ℝ) (hT : 0 ≤ T) (hH : 1 ≤ H) (hc₀ : 0 ≤ c₀)
    (f : ℝ → ℝ)
    (hf0 : ∀ v ∈ Set.Ioi H, 0 ≤ f v)
    (hfe : ∀ v ∈ Set.Ioi H,
      f v ≤ c₀ * ((3 + T + v) ^ 4 * (1 + v) ^ 6 * Real.exp (-(Real.pi / 2) * v))) :
    (∫ v in Set.Ioi H, f v) ≤
      c₀ * (Real.exp (-(Real.pi / 2) * H) * (3 + T + H) ^ 4 * (1 + H) ^ 6
        * (∫ s in Set.Ioi 0, (1 + s) ^ 10 * Real.exp (-(Real.pi / 2) * s))) := by
  set K : ℝ := Real.exp (-(Real.pi / 2) * H) * (3 + T + H) ^ 4 * (1 + H) ^ 6 with hK
  -- Step 1: change of variable v = H + s
  have htrans : (∫ v in Set.Ioi H, f v) = ∫ s in Set.Ioi 0, f (H + s) := by
    have key : ∀ x : ℝ, Set.indicator (Set.Ioi 0) (fun s => f (H + s)) x
        = Set.indicator (Set.Ioi H) f (x + H) := by
      intro x
      by_cases hx : x ∈ Set.Ioi 0
      · have hxH : x + H ∈ Set.Ioi H := by
          simp only [Set.mem_Ioi] at hx ⊢; linarith
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxH]
        exact congrArg f (add_comm H x)
      · have hxH : x + H ∉ Set.Ioi H := by
          simp only [Set.mem_Ioi, not_lt] at hx ⊢; linarith
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hxH]
    calc (∫ v in Set.Ioi H, f v)
        = ∫ v, Set.indicator (Set.Ioi H) f v :=
          (MeasureTheory.integral_indicator (s := Set.Ioi H) measurableSet_Ioi).symm
      _ = ∫ s, Set.indicator (Set.Ioi H) f (s + H) :=
          (MeasureTheory.integral_add_right_eq_self (Set.indicator (Set.Ioi H) f) H).symm
      _ = ∫ s, Set.indicator (Set.Ioi 0) (fun s => f (H + s)) s := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with s
          exact (key s).symm
      _ = ∫ s in Set.Ioi 0, f (H + s) :=
          MeasureTheory.integral_indicator (s := Set.Ioi 0) measurableSet_Ioi
  -- Step 2: pointwise bound
  have hpt : ∀ s ∈ Set.Ioi 0,
      f (H + s) ≤ c₀ * (K * ((1 + s) ^ 10 * Real.exp (-(Real.pi / 2) * s))) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hmem : H + s ∈ Set.Ioi H := by simp only [Set.mem_Ioi]; linarith
    refine le_trans (hfe (H + s) hmem) ?_
    refine mul_le_mul_of_nonneg_left ?_ hc₀
    have hb1 : (0 : ℝ) ≤ 3 + T + (H + s) := by linarith
    have hb2 : 3 + T + (H + s) ≤ (3 + T + H) * (1 + s) := by
      have hp : (0 : ℝ) ≤ s * (2 + T + H) := mul_nonneg hs0.le (by linarith)
      linarith
    have e1 : (3 + T + (H + s)) ^ 4 ≤ (3 + T + H) ^ 4 * (1 + s) ^ 4 := by
      have h := pow_le_pow_left₀ hb1 hb2 4
      rwa [mul_pow] at h
    have hd1 : (0 : ℝ) ≤ 1 + (H + s) := by linarith
    have hd2 : 1 + (H + s) ≤ (1 + H) * (1 + s) := by
      have hp : (0 : ℝ) ≤ s * H := mul_nonneg hs0.le (by linarith)
      linarith
    have e2 : (1 + (H + s)) ^ 6 ≤ (1 + H) ^ 6 * (1 + s) ^ 6 := by
      have h := pow_le_pow_left₀ hd1 hd2 6
      rwa [mul_pow] at h
    have he : Real.exp (-(Real.pi / 2) * (H + s))
        = Real.exp (-(Real.pi / 2) * H) * Real.exp (-(Real.pi / 2) * s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he]
    have hAB : (3 + T + (H + s)) ^ 4 * (1 + (H + s)) ^ 6
        ≤ ((3 + T + H) ^ 4 * (1 + s) ^ 4) * ((1 + H) ^ 6 * (1 + s) ^ 6) := by
      refine mul_le_mul e1 e2 (by positivity) (by positivity)
    have hC : (0 : ℝ) ≤ Real.exp (-(Real.pi / 2) * H) * Real.exp (-(Real.pi / 2) * s) :=
      mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    have hAB' : (0 : ℝ) ≤ ((3 + T + H) ^ 4 * (1 + s) ^ 4) * ((1 + H) ^ 6 * (1 + s) ^ 6) :=
      by positivity
    calc (3 + T + (H + s)) ^ 4 * (1 + (H + s)) ^ 6
            * (Real.exp (-(Real.pi / 2) * H) * Real.exp (-(Real.pi / 2) * s))
        ≤ ((3 + T + H) ^ 4 * (1 + s) ^ 4) * ((1 + H) ^ 6 * (1 + s) ^ 6)
            * (Real.exp (-(Real.pi / 2) * H) * Real.exp (-(Real.pi / 2) * s)) :=
          mul_le_mul hAB le_rfl hC hAB'
      _ = K * ((1 + s) ^ 10 * Real.exp (-(Real.pi / 2) * s)) := by
          rw [hK]; ring
  -- Step 3: integrability of the majorant
  have hint : Integrable
      (fun s => c₀ * (K * ((1 + s) ^ 10 * Real.exp (-(Real.pi / 2) * s))))
      (volume.restrict (Set.Ioi 0)) := by
    have hbase : Integrable (fun s => (1 + s) ^ 10 * Real.exp (-(Real.pi / 2) * s))
        (volume.restrict (Set.Ioi 0)) := by
      have h := Work.ZeroDensity.Ingham.integrableOn_one_add_pow_mul_exp_neg 10
        (b := Real.pi / 2) (by positivity)
      refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
      have hneg : -(Real.pi / 2 * s) = -(Real.pi / 2) * s := by ring
      beta_reduce
      rw [hneg]
    have h1 := hbase.const_mul K
    have h2 := h1.const_mul c₀
    simpa only [smul_eq_mul] using h2
  -- Step 4: monotonicity of the integral
  have h0 : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] (fun s => f (H + s)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    exact hf0 (H + s) (by simp only [Set.mem_Ioi] at hs ⊢; linarith)
  have hae : (fun s => f (H + s)) ≤ᵐ[volume.restrict (Set.Ioi 0)]
      (fun s => c₀ * (K * ((1 + s) ^ 10 * Real.exp (-(Real.pi / 2) * s)))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
    exact hpt s hs
  have hmono : (∫ s in Set.Ioi 0, f (H + s))
      ≤ ∫ s in Set.Ioi 0, c₀ * (K * ((1 + s) ^ 10 * Real.exp (-(Real.pi / 2) * s))) :=
    MeasureTheory.integral_mono_of_nonneg h0 hint hae
  calc (∫ v in Set.Ioi H, f v)
      = ∫ s in Set.Ioi 0, f (H + s) := htrans
    _ ≤ ∫ s in Set.Ioi 0, c₀ * (K * ((1 + s) ^ 10 * Real.exp (-(Real.pi / 2) * s))) := hmono
    _ = c₀ * (K * (∫ s in Set.Ioi 0, (1 + s) ^ 10 * Real.exp (-(Real.pi / 2) * s))) := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

end Work.ZeroDensity.Ingham
