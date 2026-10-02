import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_explicit_formula_mult
import Submission.Commons.NumberTheory.Linnik.tentMellin_bridge_scale

open Complex DirichletCharacter MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators

set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

/-- `norm_intervalIntegral_mul_le_gen` with the weaker hypothesis `0 ≤ M`. -/
theorem norm_intervalIntegral_mul_le_gen_nonneg {F Φ : ℂ → ℂ} {M : ℝ} (hM : 0 ≤ M) {A B : ℝ}
    (hAB : A ≤ B) (hΦ : ∀ u : ℂ, u.re ≤ B → ‖Φ u‖ ≤ M / (1 + ‖u‖ ^ 2))
    {v : ℝ} (_hv : 1 ≤ |v|)
    (hint : IntervalIntegrable (fun x : ℝ => ‖F ((x : ℂ) + (v : ℂ) * Complex.I)‖) volume A B)
    (hint2 : IntervalIntegrable (fun x : ℝ =>
      F ((x : ℂ) + (v : ℂ) * Complex.I) * Φ ((x : ℂ) + (v : ℂ) * Complex.I)) volume A B) :
    ‖(∫ x : ℝ in A..B, F ((x : ℂ) + (v : ℂ) * Complex.I) *
        Φ ((x : ℂ) + (v : ℂ) * Complex.I))‖ ≤
      (M / (1 + v ^ 2)) * (∫ x : ℝ in A..B, ‖F ((x : ℂ) + (v : ℂ) * Complex.I)‖) := by
  have hure : ∀ x : ℝ, ((x : ℂ) + (v : ℂ) * Complex.I).re = x := by intro x; simp
  have huim : ∀ x : ℝ, ((x : ℂ) + (v : ℂ) * Complex.I).im = v := by intro x; simp
  have hnorm_sq : ∀ x : ℝ, ‖((x : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 = x ^ 2 + v ^ 2 := by
    intro x
    rw [Complex.sq_norm, Complex.normSq_apply, hure x, huim x]
    ring
  have hΦbound : ∀ x : ℝ, x ≤ B → ‖Φ ((x : ℂ) + (v : ℂ) * Complex.I)‖ ≤ M / (1 + v ^ 2) := by
    intro x hx
    have h1 : ‖Φ ((x : ℂ) + (v : ℂ) * Complex.I)‖
        ≤ M / (1 + ‖((x : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2) :=
      hΦ _ (by rw [hure x]; exact hx)
    have hden : (1 : ℝ) + v ^ 2 ≤ 1 + ‖((x : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 := by
      have := hnorm_sq x; nlinarith [sq_nonneg x]
    have hpos : (0 : ℝ) < 1 + v ^ 2 := by nlinarith [sq_nonneg v]
    exact h1.trans (div_le_div_of_nonneg_left hM hpos hden)
  have hint3 : IntervalIntegrable
      (fun x : ℝ => (M / (1 + v ^ 2)) * ‖F ((x : ℂ) + (v : ℂ) * Complex.I)‖) volume A B :=
    hint.const_mul _
  have hint2n : IntervalIntegrable
      (fun x : ℝ => ‖F ((x : ℂ) + (v : ℂ) * Complex.I) * Φ ((x : ℂ) + (v : ℂ) * Complex.I)‖)
      volume A B :=
    hint2.norm
  calc ‖(∫ x : ℝ in A..B, F ((x : ℂ) + (v : ℂ) * Complex.I) *
          Φ ((x : ℂ) + (v : ℂ) * Complex.I))‖
      ≤ ∫ x : ℝ in A..B,
          ‖F ((x : ℂ) + (v : ℂ) * Complex.I) * Φ ((x : ℂ) + (v : ℂ) * Complex.I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hAB
    _ ≤ ∫ x : ℝ in A..B,
          (M / (1 + v ^ 2)) * ‖F ((x : ℂ) + (v : ℂ) * Complex.I)‖ := by
        apply intervalIntegral.integral_mono_on hAB hint2n hint3
        intro x hx
        rw [norm_mul]
        have := mul_le_mul_of_nonneg_left (hΦbound x hx.2)
          (norm_nonneg (F ((x : ℂ) + (v : ℂ) * Complex.I)))
        simpa [mul_comm] using this
    _ = (M / (1 + v ^ 2)) *
          (∫ x : ℝ in A..B, ‖F ((x : ℂ) + (v : ℂ) * Complex.I)‖) :=
        intervalIntegral.integral_const_mul (M / (1 + v ^ 2))
          (fun x : ℝ => ‖F ((x : ℂ) + (v : ℂ) * Complex.I)‖)

theorem horizontal_logDeriv_completedL_tendsto_gen {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {A B : ℝ} (hA : -(1/2 : ℝ) ≤ A) (hAB : A ≤ B) (hB2 : B ≤ 2)
    {Φ : ℂ → ℂ} (hΦdiff : Differentiable ℂ Φ) {M : ℝ} (hM : 0 ≤ M)
    (hΦb : ∀ u : ℂ, u.re ≤ B → ‖Φ u‖ ≤ M / (1 + ‖u‖ ^ 2))
    {c : ℝ} (hc : 0 < c) {T' : ℝ → ℝ}
    (hT' : ∀ T : ℝ, 1 ≤ T → T + 1 ≤ T' T)
    (hsep : ∀ T : ℝ, 1 ≤ T → ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
      c / Real.log ((N : ℝ) * (T' T + 3)) ≤ |ρ.im - T' T|)
    (hsep' : ∀ T : ℝ, 1 ≤ T → ∀ ρ : ℂ, DirichletCharacter.completedLFunction χ ρ = 0 →
      c / Real.log ((N : ℝ) * (T' T + 3)) ≤ |ρ.im + T' T|) :
    (Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in A..B,
        logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I) *
          Φ ((x : ℂ) + ((T' T : ℝ) : ℂ) * Complex.I)) Filter.atTop (nhds 0)) ∧
    (Filter.Tendsto (fun T : ℝ => ∫ x : ℝ in A..B,
        logDeriv (DirichletCharacter.completedLFunction χ) ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I) *
          Φ ((x : ℂ) - ((T' T : ℝ) : ℂ) * Complex.I)) Filter.atTop (nhds 0)) := by
  obtain ⟨C, hC0, hCb⟩ := exists_bound_integral_logDeriv_completedL_horizontal χ hχ hχprim
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (NeZero.one_le (n := N))
  have hNpos : 0 < (N:ℝ) := by linarith
  have hT'tend : Tendsto T' atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (1:ℝ), eventually_ge_atTop (b - 1)] with T h1 h2
    exact le_trans (by linarith) (hT' T h1)
  have hlim : Tendsto (fun T : ℝ => (M * C * (2 + |Real.log c|)) *
      ((Real.log ((N:ℝ) * (T' T + 3)))^2 / (1 + (T' T)^2))) atTop (nhds 0) := by
    simpa using
      ((Commons.NumberTheory.Linnik.tendsto_log_N_sq_div (N := N)).comp hT'tend).const_mul
        (M * C * (2 + |Real.log c|))
  have hlarge : ∀ᶠ T : ℝ in atTop, c ≤ Real.log ((N:ℝ) * (T' T + 3)) := by
    have hlogtend : Tendsto (fun T : ℝ => Real.log ((N:ℝ) * (T + 4))) atTop atTop := by
      have h1 : Tendsto (fun T : ℝ => (N:ℝ) * (T + 4)) atTop atTop := by
        have h2 : Tendsto (fun T : ℝ => T + 4) atTop atTop := by
          simpa [add_comm] using Filter.tendsto_atTop_add_const_left atTop (4:ℝ) tendsto_id
        exact h2.const_mul_atTop hNpos
      exact Real.tendsto_log_atTop.comp h1
    filter_upwards [hlogtend.eventually (eventually_ge_atTop c), eventually_ge_atTop (1:ℝ)]
      with T h1 h2
    refine le_trans h1 (Real.log_le_log (by positivity) ?_)
    have h3 : T + 4 ≤ T' T + 3 := by have := hT' T h2; linarith
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have hT'2 : ∀ T : ℝ, 1 ≤ T → 2 ≤ |T' T| := by
    intro T hT
    rw [abs_of_nonneg (by linarith [hT' T hT])]
    linarith [hT' T hT]
  have hkey : ∀ v : ℝ, 2 ≤ |v| → c ≤ Real.log ((N:ℝ) * (|v| + 3)) →
      (∀ ρ : ℂ, completedLFunction χ ρ = 0 →
        c / Real.log ((N:ℝ) * (|v| + 3)) ≤ |ρ.im - (|v|)|) →
      (∀ ρ : ℂ, completedLFunction χ ρ = 0 →
        c / Real.log ((N:ℝ) * (|v| + 3)) ≤ |ρ.im + (|v|)|) →
      ‖(∫ x : ℝ in A..B, logDeriv (completedLFunction χ)
          ((x : ℂ) + (v : ℂ) * Complex.I) * Φ ((x : ℂ) + (v : ℂ) * Complex.I))‖
        ≤ (M * C * (2 + |Real.log c|)) *
            ((Real.log ((N:ℝ) * (|v| + 3)))^2 / (1 + v ^ 2)) := by
    intro v hv hcl hs1 hs2
    have hLpos : 0 < Real.log ((N:ℝ) * (|v| + 3)) := by
      apply Real.log_pos
      nlinarith [hN1, abs_nonneg v]
    have hδ0 : 0 < c / Real.log ((N:ℝ) * (|v| + 3)) := div_pos hc hLpos
    have hδ1 : c / Real.log ((N:ℝ) * (|v| + 3)) ≤ 1 := by
      rw [div_le_one hLpos]; exact hcl
    have hnz : ∀ x : ℝ, completedLFunction χ ((x : ℂ) + (v : ℂ) * Complex.I) ≠ 0 := by
      intro x h0
      have him : (((x : ℂ) + (v : ℂ) * Complex.I)).im = v := by simp
      by_cases hv0 : 0 ≤ v
      · have h1 := hs1 _ h0
        rw [him] at h1
        have hz : |v - (|v|)| = 0 := by rw [abs_of_nonneg hv0, sub_self, abs_zero]
        rw [hz] at h1
        linarith
      · have hvneg : v < 0 := not_le.mp hv0
        have h1 := hs2 _ h0
        rw [him] at h1
        have hz : |v + (|v|)| = 0 := by rw [abs_of_neg hvneg, add_neg_cancel, abs_zero]
        rw [hz] at h1
        linarith
    have hcontHalf : ContinuousOn (fun x : ℝ => ‖logDeriv (completedLFunction χ)
        ((x : ℂ) + (v : ℂ) * Complex.I)‖) (Set.uIcc (-1/2 : ℝ) 2) :=
      (((continuousOn_logDeriv_completedL χ hχ).comp (by fun_prop)
        (fun x _ => hnz x)).norm)
    have hfi : IntervalIntegrable (fun x : ℝ => ‖logDeriv (completedLFunction χ)
        ((x : ℂ) + (v : ℂ) * Complex.I)‖) volume (-1/2) 2 := hcontHalf.intervalIntegrable
    have hA' : (-1/2 : ℝ) ≤ A := by linarith [hA]
    have hmono : (∫ x : ℝ in A..B, ‖logDeriv (completedLFunction χ)
        ((x : ℂ) + (v : ℂ) * Complex.I)‖) ≤
        (∫ x : ℝ in (-1/2)..2, ‖logDeriv (completedLFunction χ)
        ((x : ℂ) + (v : ℂ) * Complex.I)‖) :=
      intervalIntegral.integral_mono_interval hA' hAB hB2
        (Filter.Eventually.of_forall (fun x => norm_nonneg _)) hfi
    have hIb : (∫ x : ℝ in A..B, ‖logDeriv (completedLFunction χ)
        ((x : ℂ) + (v : ℂ) * Complex.I)‖) ≤
        C * Real.log ((N:ℝ) * (|v| + 3)) *
          (Real.log ((N:ℝ) * (|v| + 3)) +
            Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3))))) := by
      refine le_trans hmono ?_
      by_cases hv0 : 0 ≤ v
      · have h := (hCb |v| hv (c / Real.log ((N:ℝ) * (|v| + 3))) hδ0 hδ1 hs1 hs2).1
        simpa [abs_of_nonneg hv0] using h
      · have hvneg : v < 0 := not_le.mp hv0
        have h := (hCb |v| hv (c / Real.log ((N:ℝ) * (|v| + 3))) hδ0 hδ1 hs1 hs2).2
        simpa [abs_of_neg hvneg, Complex.ofReal_neg, neg_mul, neg_neg] using h
    have hLv1 : 1 ≤ Real.log ((N:ℝ) * (|v| + 3)) := by
      have h5 : (5:ℝ) ≤ (N:ℝ) * (|v| + 3) := by nlinarith [hN1, abs_nonneg v]
      have he : Real.exp 1 ≤ 5 := by linarith [Real.exp_one_lt_d9]
      calc (1:ℝ) ≤ Real.log 5 := by
            rw [Real.le_log_iff_exp_le (by norm_num)]; exact he
        _ ≤ Real.log ((N:ℝ) * (|v| + 3)) := Real.log_le_log (by norm_num) h5
    have hlogδ : Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3)))) ≤
        Real.log ((N:ℝ) * (|v| + 3)) + |Real.log c| := by
      have hLne : Real.log ((N:ℝ) * (|v| + 3)) ≠ 0 := ne_of_gt hLpos
      have h1 : 1 / (c / Real.log ((N:ℝ) * (|v| + 3))) =
          Real.log ((N:ℝ) * (|v| + 3)) / c := by
        rw [one_div_div]
      rw [h1, Real.log_div hLne hc.ne']
      have h2 : Real.log (Real.log ((N:ℝ) * (|v| + 3))) ≤ Real.log ((N:ℝ) * (|v| + 3)) := by
        have := Real.log_le_sub_one_of_pos hLpos
        linarith
      have h3 : - Real.log c ≤ |Real.log c| := neg_le_abs _
      linarith
    have hstep : (M / (1 + v ^ 2)) * (C * Real.log ((N:ℝ) * (|v| + 3)) *
        (Real.log ((N:ℝ) * (|v| + 3)) +
          Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3))))))
        ≤ (M * C * (2 + |Real.log c|)) *
            ((Real.log ((N:ℝ) * (|v| + 3)))^2 / (1 + v ^ 2)) := by
      have hD : (0:ℝ) < 1 + v ^ 2 := by positivity
      have hZ : Real.log ((N:ℝ) * (|v| + 3)) * (Real.log ((N:ℝ) * (|v| + 3)) +
          Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3)))))
          ≤ (2 + |Real.log c|) * (Real.log ((N:ℝ) * (|v| + 3)))^2 := by
        have h2 : Real.log ((N:ℝ) * (|v| + 3)) ≤ (Real.log ((N:ℝ) * (|v| + 3)))^2 := by
          nlinarith [hLv1]
        have h4 : 0 ≤ |Real.log c| := abs_nonneg _
        nlinarith [hlogδ, h2, h4, hLv1, hLpos]
      have hmain := mul_le_mul_of_nonneg_left hZ (mul_nonneg hM hC0.le)
      have hkey2 : M * (C * Real.log ((N:ℝ) * (|v| + 3)) * (Real.log ((N:ℝ) * (|v| + 3)) +
            Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3)))))) / (1 + v ^ 2)
          ≤ (M * C * (2 + |Real.log c|) * (Real.log ((N:ℝ) * (|v| + 3)))^2) / (1 + v ^ 2) :=
        (div_le_div_iff_of_pos_right hD).mpr (by linarith [hmain])
      calc (M / (1 + v ^ 2)) * (C * Real.log ((N:ℝ) * (|v| + 3)) *
              (Real.log ((N:ℝ) * (|v| + 3)) +
                Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3))))))
          = M * (C * Real.log ((N:ℝ) * (|v| + 3)) * (Real.log ((N:ℝ) * (|v| + 3)) +
                Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3)))))) / (1 + v ^ 2) := by ring
        _ ≤ (M * C * (2 + |Real.log c|) * (Real.log ((N:ℝ) * (|v| + 3)))^2) / (1 + v ^ 2) := hkey2
        _ = (M * C * (2 + |Real.log c|)) *
              ((Real.log ((N:ℝ) * (|v| + 3)))^2 / (1 + v ^ 2)) := by ring
    have hint : IntervalIntegrable (fun x : ℝ => ‖logDeriv (completedLFunction χ)
        ((x : ℂ) + (v : ℂ) * Complex.I)‖) volume A B :=
      ((continuousOn_logDeriv_completedL χ hχ).comp (by fun_prop)
        (fun x _ => hnz x)).norm.intervalIntegrable
    have hint2 : IntervalIntegrable (fun x : ℝ => logDeriv (completedLFunction χ)
        ((x : ℂ) + (v : ℂ) * Complex.I) * Φ ((x : ℂ) + (v : ℂ) * Complex.I)) volume A B :=
      (((continuousOn_logDeriv_completedL χ hχ).comp (by fun_prop) (fun x _ => hnz x)).mul
        (hΦdiff.continuous.comp_continuousOn
          (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + (v : ℂ) * Complex.I)
            (Set.uIcc A B)))).intervalIntegrable
    have hb := norm_intervalIntegral_mul_le_gen_nonneg
      (F := fun u : ℂ => logDeriv (completedLFunction χ) u) (Φ := Φ)
      hM hAB hΦb (le_trans (by norm_num : (1:ℝ) ≤ 2) hv) hint hint2
    calc ‖(∫ x : ℝ in A..B, logDeriv (completedLFunction χ)
            ((x : ℂ) + (v : ℂ) * Complex.I) * Φ ((x : ℂ) + (v : ℂ) * Complex.I))‖
        ≤ (M / (1 + v ^ 2)) * (∫ x : ℝ in A..B,
            ‖logDeriv (completedLFunction χ) ((x : ℂ) + (v : ℂ) * Complex.I)‖) := hb
      _ ≤ (M / (1 + v ^ 2)) * (C * Real.log ((N:ℝ) * (|v| + 3)) *
            (Real.log ((N:ℝ) * (|v| + 3)) +
              Real.log (1 / (c / Real.log ((N:ℝ) * (|v| + 3)))))) :=
          mul_le_mul_of_nonneg_left hIb (by positivity)
      _ ≤ (M * C * (2 + |Real.log c|)) *
            ((Real.log ((N:ℝ) * (|v| + 3)))^2 / (1 + v ^ 2)) := hstep
  constructor
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _)) ?_ hlim
    filter_upwards [eventually_ge_atTop (1:ℝ), hlarge] with T h1 h2
    have habs : |T' T| = T' T := abs_of_nonneg (by linarith [hT' T h1])
    have hs1 : ∀ ρ : ℂ, completedLFunction χ ρ = 0 →
        c / Real.log ((N:ℝ) * (|T' T| + 3)) ≤ |ρ.im - (|T' T|)| := by
      intro ρ hρ; rw [habs]; exact hsep T h1 ρ hρ
    have hs2 : ∀ ρ : ℂ, completedLFunction χ ρ = 0 →
        c / Real.log ((N:ℝ) * (|T' T| + 3)) ≤ |ρ.im + (|T' T|)| := by
      intro ρ hρ; rw [habs]; exact hsep' T h1 ρ hρ
    have hcl : c ≤ Real.log ((N:ℝ) * (|T' T| + 3)) := by rw [habs]; exact h2
    simpa [habs] using hkey (T' T) (hT'2 T h1) hcl hs1 hs2
  · refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Filter.Eventually.of_forall (fun T => norm_nonneg _)) ?_ hlim
    filter_upwards [eventually_ge_atTop (1:ℝ), hlarge] with T h1 h2
    have habs : |T' T| = T' T := abs_of_nonneg (by linarith [hT' T h1])
    have habs2 : |-(T' T)| = T' T := by rw [abs_neg, habs]
    have hs1 : ∀ ρ : ℂ, completedLFunction χ ρ = 0 →
        c / Real.log ((N:ℝ) * (|-(T' T)| + 3)) ≤ |ρ.im - (|-(T' T)|)| := by
      intro ρ hρ; rw [habs2]; exact hsep T h1 ρ hρ
    have hs2 : ∀ ρ : ℂ, completedLFunction χ ρ = 0 →
        c / Real.log ((N:ℝ) * (|-(T' T)| + 3)) ≤ |ρ.im + (|-(T' T)|)| := by
      intro ρ hρ; rw [habs2]; exact hsep' T h1 ρ hρ
    have hcl : c ≤ Real.log ((N:ℝ) * (|-(T' T)| + 3)) := by rw [habs2]; exact h2
    have h := hkey (-(T' T)) (by rw [abs_neg]; exact hT'2 T h1) hcl hs1 hs2
    simpa [habs2, habs, neg_sq, Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using h

end

end Commons.NumberTheory.DirichletCharacter
