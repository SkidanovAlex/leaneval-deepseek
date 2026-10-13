import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Measure.Haar.Unique

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EComparison

open MeasureTheory Filter
open scoped BigOperators Topology

/-- Auxiliary: a nonnegative integrable function whose integrals over the consecutive
windows `[a n, a (n+1)]` are bounded below by a positive constant is not integrable. -/
private lemma not_integrable_of_window_lower {f : ℝ → ℝ} {I : ℝ}
    (hint : Integrable f) (hnonneg : ∀ t, 0 ≤ f t) (hI : 0 < I)
    (a : ℕ → ℝ) (ha0 : a 0 = 0)
    (hwin : ∀ n : ℕ, I ≤ ∫ x in (a n)..(a (n + 1)), f x) : False := by
  have htel : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, ∫ x in (a n)..(a (n + 1)), f x)
        = ∫ x in (0 : ℝ)..(a N), f x := by
    intro N
    induction N with
    | zero => simp [ha0]
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact intervalIntegral.integral_add_adjacent_intervals
        hint.intervalIntegrable hint.intervalIntegrable
  have hpartial : ∀ N : ℕ, (N : ℝ) * I ≤ ∫ x in (0 : ℝ)..(a N), f x := by
    intro N
    calc (N : ℝ) * I = ∑ _n ∈ Finset.range N, I := by simp
      _ ≤ ∑ n ∈ Finset.range N, ∫ x in (a n)..(a (n + 1)), f x :=
          Finset.sum_le_sum (fun n _ => hwin n)
      _ = ∫ x in (0 : ℝ)..(a N), f x := htel N
  obtain ⟨N, hN⟩ := exists_nat_gt ((∫ x : ℝ, f x) / I)
  have hN' : (∫ x : ℝ, f x) < (N : ℝ) * I := by
    have h := mul_lt_mul_of_pos_right hN hI
    rwa [div_mul_cancel₀ _ (ne_of_gt hI)] at h
  have hbound : (N : ℝ) * I ≤ ∫ x : ℝ, f x := by
    refine le_trans (hpartial N) ?_
    rcases le_or_gt 0 (a N) with h | h
    · rw [intervalIntegral.integral_of_le h]
      exact setIntegral_le_integral hint (Eventually.of_forall hnonneg)
    · rw [intervalIntegral.integral_of_ge h.le]
      have h1 : 0 ≤ ∫ x in Set.Ioc (a N) 0, f x := integral_nonneg hnonneg
      have h2 : 0 ≤ ∫ x : ℝ, f x := integral_nonneg hnonneg
      linarith
  linarith

/-- The `c ≥ 0` case: a function `exp (c t) * (A cos (ωt) + B sin (ωt))²` with a genuinely
oscillating trigonometric factor is never integrable. -/
private lemma exp_trig_nonneg {c : ℝ} (hc : 0 ≤ c) {ω A B : ℝ} (hω : ω ≠ 0)
    (hint : Integrable (fun t : ℝ => Real.exp (c * t) *
      (A * Real.cos (ω * t) + B * Real.sin (ω * t)) ^ 2)) :
    A = 0 ∧ B = 0 := by
  by_contra hne
  have hAB : A ≠ 0 ∨ B ≠ 0 := not_and_or.mp hne
  set T : ℝ := 2 * Real.pi / |ω| with hTdef
  set ψ : ℝ → ℝ := fun t => A * Real.cos (ω * t) + B * Real.sin (ω * t) with hψdef
  set g : ℝ → ℝ := fun t => Real.exp (c * t) * ψ t ^ 2 with hgdef
  have hT : 0 < T := by
    rw [hTdef]
    exact div_pos (by positivity) (abs_pos.mpr hω)
  have hcontψ : Continuous ψ := by rw [hψdef]; fun_prop
  have hcontg : Continuous g := by rw [hgdef]; fun_prop
  have homegaT : ω * T = 2 * Real.pi ∨ ω * T = -(2 * Real.pi) := by
    rcases lt_trichotomy ω 0 with h | h | h
    · right; rw [hTdef, abs_of_neg h]; field_simp
    · exact absurd h hω
    · left; rw [hTdef, abs_of_pos h]; field_simp
  have hhalf : ω * (T / 2) = Real.pi ∨ ω * (T / 2) = -Real.pi := by
    rcases homegaT with h | h
    · left; rw [show ω * (T / 2) = (ω * T) / 2 by ring, h]; ring
    · right; rw [show ω * (T / 2) = (ω * T) / 2 by ring, h]; ring
  have hquarter : ω * (T / 4) = Real.pi / 2 ∨ ω * (T / 4) = -(Real.pi / 2) := by
    rcases homegaT with h | h
    · left; rw [show ω * (T / 4) = (ω * T) / 4 by ring, h]; ring
    · right; rw [show ω * (T / 4) = (ω * T) / 4 by ring, h]; ring
  have hper : Function.Periodic ψ T := by
    intro t
    show A * Real.cos (ω * (t + T)) + B * Real.sin (ω * (t + T))
       = A * Real.cos (ω * t) + B * Real.sin (ω * t)
    rcases homegaT with h | h
    · have harg : ω * (t + T) = ω * t + 2 * Real.pi := by rw [mul_add, h]
      rw [harg, Real.cos_add_two_pi, Real.sin_add_two_pi]
    · have harg : ω * (t + T) = ω * t - 2 * Real.pi := by rw [mul_add, h]; ring
      rw [harg, Real.cos_sub_two_pi, Real.sin_sub_two_pi]
  have hpern : ∀ n : ℕ, Function.Periodic ψ ((n : ℝ) * T) := by
    intro n
    simpa [nsmul_eq_mul] using hper.nsmul n
  have hshift : ∀ (n : ℕ) (t : ℝ),
      g (t + (n : ℝ) * T) = Real.exp (c * ((n : ℝ) * T)) * g t := by
    intro n t
    show Real.exp (c * (t + (n : ℝ) * T)) * ψ (t + (n : ℝ) * T) ^ 2
       = Real.exp (c * ((n : ℝ) * T)) * (Real.exp (c * t) * ψ t ^ 2)
    rw [hpern n t,
      show c * (t + (n : ℝ) * T) = c * ((n : ℝ) * T) + c * t by ring, Real.exp_add]
    ring
  have hintg : Integrable g := by
    simpa [hgdef, hψdef] using hint
  have hpoint : ∃ x₀ ∈ Set.Ioo (0 : ℝ) T, ψ x₀ ≠ 0 := by
    rcases hAB with hA | hB
    · refine ⟨T / 2, ⟨by linarith, by linarith⟩, ?_⟩
      show A * Real.cos (ω * (T / 2)) + B * Real.sin (ω * (T / 2)) ≠ 0
      rcases hhalf with h | h
      · rw [h, Real.cos_pi, Real.sin_pi]
        simpa using neg_ne_zero.mpr hA
      · rw [h, Real.cos_neg, Real.cos_pi, Real.sin_neg, Real.sin_pi]
        simpa using neg_ne_zero.mpr hA
    · refine ⟨T / 4, ⟨by linarith, by linarith⟩, ?_⟩
      show A * Real.cos (ω * (T / 4)) + B * Real.sin (ω * (T / 4)) ≠ 0
      rcases hquarter with h | h
      · rw [h, Real.cos_pi_div_two, Real.sin_pi_div_two]
        simpa using hB
      · rw [h, Real.cos_neg, Real.cos_pi_div_two, Real.sin_neg, Real.sin_pi_div_two]
        simpa using neg_ne_zero.mpr hB
  obtain ⟨x₀, hx₀I, hx₀ne⟩ := hpoint
  have hI : 0 < ∫ x in (0 : ℝ)..T, g x := by
    have hmem : {t : ℝ | ψ t ≠ 0} ∈ 𝓝 x₀ := hcontψ.continuousAt.eventually_ne hx₀ne
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hmem
    set ρ : ℝ := min ε (min (x₀ / 2) ((T - x₀) / 2)) with hρdef
    have hρpos : 0 < ρ := by
      rw [hρdef]
      exact lt_min hεpos (lt_min (by linarith [hx₀I.1]) (by linarith [hx₀I.2]))
    have hball : Metric.ball x₀ ρ ⊆ Function.support g ∩ Set.Ioc 0 T := by
      intro t ht
      have htx : |t - x₀| < ρ := by
        simpa [Metric.mem_ball, Real.dist_eq] using ht
      refine ⟨?_, ?_⟩
      · change g t ≠ 0
        have hne : ψ t ≠ 0 := hεsub (Metric.ball_subset_ball (min_le_left _ _) ht)
        exact mul_ne_zero (Real.exp_ne_zero _) (pow_ne_zero 2 hne)
      · rw [Set.mem_Ioc]
        constructor
        · have h2 : |t - x₀| < x₀ / 2 :=
            lt_of_lt_of_le htx (le_trans (min_le_right _ _) (min_le_left _ _))
          have := (abs_lt.mp h2).1
          linarith [hx₀I.1]
        · have h2 : |t - x₀| < (T - x₀) / 2 :=
            lt_of_lt_of_le htx (le_trans (min_le_right _ _) (min_le_right _ _))
          have := (abs_lt.mp h2).2
          linarith [hx₀I.2]
    have hmeas : 0 < volume (Function.support g ∩ Set.Ioc 0 T) :=
      lt_of_lt_of_le (Metric.measure_ball_pos volume x₀ hρpos) (measure_mono hball)
    exact (intervalIntegral.integral_pos_iff_support_of_nonneg_ae (f := g) (a := (0 : ℝ))
      (b := T) (μ := volume)
      (Eventually.of_forall (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
      (hcontg.intervalIntegrable 0 T)).mpr ⟨hT, hmeas⟩
  have hwin : ∀ n : ℕ,
      (∫ x in (0 : ℝ)..T, g x) ≤ ∫ x in ((n : ℝ) * T)..((↑(n + 1) : ℝ) * T), g x := by
    intro n
    have hsub : ∫ x in ((n : ℝ) * T)..((↑(n + 1) : ℝ) * T), g x
        = ∫ x in (0 : ℝ)..T, g (x + (n : ℝ) * T) := by
      have key := intervalIntegral.integral_comp_add_right (f := g) (a := (0 : ℝ)) (b := T)
        ((n : ℝ) * T)
      rw [zero_add] at key
      rw [show T + (n : ℝ) * T = (↑(n + 1) : ℝ) * T by push_cast; ring] at key
      exact key.symm
    rw [hsub]
    simp only [hshift n]
    rw [intervalIntegral.integral_const_mul]
    exact le_mul_of_one_le_left hI.le (Real.one_le_exp (by positivity))
  exact not_integrable_of_window_lower hintg
    (fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) hI
    (fun n : ℕ => (n : ℝ) * T) (by simp) hwin

theorem not_integrable_exp_trig {c ω A B : ℝ} (hω : ω ≠ 0)
    (hint : MeasureTheory.Integrable
      (fun t : ℝ => Real.exp (c * t) * (A * Real.cos (ω * t) + B * Real.sin (ω * t)) ^ 2)) :
    A = 0 ∧ B = 0 := by
  rcases le_or_gt 0 c with hc | hc
  · exact exp_trig_nonneg hc hω hint
  · have hcomp : MeasureTheory.Integrable (fun t : ℝ =>
        Real.exp (c * (-t)) * (A * Real.cos (ω * (-t)) + B * Real.sin (ω * (-t))) ^ 2) :=
      hint.comp_neg
    have hfun : (fun t : ℝ => Real.exp (c * (-t)) *
          (A * Real.cos (ω * (-t)) + B * Real.sin (ω * (-t))) ^ 2)
        = fun t : ℝ => Real.exp ((-c) * t) *
          (A * Real.cos (ω * t) + (-B) * Real.sin (ω * t)) ^ 2 := by
      funext t
      rw [show c * -t = (-c) * t by ring, show ω * -t = -(ω * t) by ring,
        Real.cos_neg, Real.sin_neg]
      ring
    have hint' : MeasureTheory.Integrable (fun t : ℝ => Real.exp ((-c) * t) *
        (A * Real.cos (ω * t) + (-B) * Real.sin (ω * t)) ^ 2) := by
      rw [← hfun]
      exact hcomp
    have hres := exp_trig_nonneg (by linarith : (0 : ℝ) ≤ -c) hω hint'
    exact ⟨hres.1, neg_eq_zero.mp hres.2⟩

end Work.FTS.StrongEps.EComparison
