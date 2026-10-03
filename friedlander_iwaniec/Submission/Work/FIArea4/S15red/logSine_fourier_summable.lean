import Mathlib
import Submission.Work.FIArea4.logSine_fourier

namespace Work.FIArea4.S15red

open scoped BigOperators Topology ContDiff
open Filter MeasureTheory
open intervalIntegral

noncomputable section

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- **The mollified log-sine Fourier expansion, with summability.**  The coefficients
furnished by `Work.FIArea4.logSine_fourier` are the Fourier coefficients of the `C^∞`
`2π`-periodic mollification `logSine_Ffun N`; reproducing the construction here we obtain, in
addition, that the coefficient family is absolutely summable. -/
theorem logSine_fourier_summable :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∃ c : ℤ → ℂ,
      Summable c ∧ Summable (fun ℓ : ℤ => ‖c ℓ‖) ∧
      (∑' ℓ : ℤ, ‖c ℓ‖) ≤ C * (Real.log (N : ℝ)) ^ (2 : ℕ) ∧
      (∀ α : ℝ, 2 / (N : ℝ) ≤ |α| → |α| ≤ 1 →
        -Real.log (|Real.sin α| / 2)
          = (∑' ℓ : ℤ, c ℓ * Complex.exp (Complex.I * (ℓ : ℂ) * (α : ℂ))).re) := by
  classical
  obtain ⟨Ci1, hCi1pos, hCi1⟩ := logSine_integral_deriv
  obtain ⟨Ci2, hCi2pos, hCi2⟩ := logSine_integral_deriv2
  obtain ⟨Ch3, hCh3pos, hCh3⟩ := logSine_harmonic_bound
  obtain ⟨Ct4, hCt4pos, hCt4⟩ := logSine_tail_sq_bound
  refine ⟨Ci1 * Ch3 / (2 * Real.pi) + Ci2 * Ct4 / (2 * Real.pi * Real.log 2)
      + 4 / Real.log 2 + 1, by positivity, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := logSine_hN1_of hN
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2N : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  set A : ℝ := (1/(2*Real.pi)) * ∫ α in (-Real.pi)..Real.pi, |deriv (ufun N) α| with hAdef
  set B : ℝ := (1/(2*Real.pi)) * ∫ α in (-Real.pi)..Real.pi, |deriv (deriv (ufun N)) α| with hBdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg logSine_hab_pi.le (fun x _ => abs_nonneg _))
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg logSine_hab_pi.le (fun x _ => abs_nonneg _))
  have hAb : A ≤ Ci1 * Real.log N / (2*Real.pi) := by
    rw [hAdef]
    calc (1/(2*Real.pi)) * ∫ α in (-Real.pi)..Real.pi, |deriv (ufun N) α|
        ≤ (1/(2*Real.pi)) * (Ci1 * Real.log N) :=
          mul_le_mul_of_nonneg_left (hCi1 N hN) (by positivity)
      _ = Ci1 * Real.log N / (2*Real.pi) := by ring
  have hBb : B ≤ Ci2 * (N:ℝ) * Real.log N / (2*Real.pi) := by
    rw [hBdef]
    calc (1/(2*Real.pi)) * ∫ α in (-Real.pi)..Real.pi, |deriv (deriv (ufun N)) α|
        ≤ (1/(2*Real.pi)) * (Ci2 * (N:ℝ) * Real.log N) :=
          mul_le_mul_of_nonneg_left (hCi2 N hN) (by positivity)
      _ = Ci2 * (N:ℝ) * Real.log N / (2*Real.pi) := by ring
  have hpartial : ∀ u : Finset ℤ,
      ∑ ℓ ∈ u, ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖
        ≤ 4 * Real.log N + A * (Ch3 * Real.log N) + B * (Ct4 / N) := by
    intro u
    set s : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ) with hsdef
    have h0s : (0:ℤ) ∈ s := by rw [hsdef]; exact logSine_zero_mem_Icc N
    rw [← Finset.sum_filter_add_sum_filter_not u (fun ℓ => ℓ ∈ s)
      (fun ℓ => ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖)]
    have h1 : ∑ ℓ ∈ u.filter (fun ℓ => ℓ ∈ s), ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖
        ≤ 4 * Real.log N + A * (Ch3 * Real.log N) := by
      have h1a : ∑ ℓ ∈ u.filter (fun ℓ => ℓ ∈ s), ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖
          ≤ ∑ ℓ ∈ u.filter (fun ℓ => ℓ ∈ s),
              (if ℓ = 0 then 4 * Real.log N else A / |(ℓ:ℝ)|) := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        by_cases h0 : ℓ = 0
        · subst h0
          rw [if_pos rfl]
          exact logSine_norm_Ffun_coeff_zero_le N hN
        · rw [if_neg h0, hAdef]
          exact logSine_norm_Ffun_coeff_le_harm N hN h0
      have h1b : ∑ ℓ ∈ u.filter (fun ℓ => ℓ ∈ s),
            (if ℓ = 0 then 4 * Real.log N else A / |(ℓ:ℝ)|)
          ≤ ∑ ℓ ∈ s, (if ℓ = 0 then 4 * Real.log N else A / |(ℓ:ℝ)|) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (s := u.filter (fun ℓ => ℓ ∈ s)) (t := s) ?_ ?_
        · intro x hx; exact (Finset.mem_filter.mp hx).2
        · intro ℓ _ _
          by_cases h0 : ℓ = 0
          · rw [if_pos h0]; positivity
          · rw [if_neg h0]; exact div_nonneg hA0 (abs_nonneg _)
      have h1c : ∑ ℓ ∈ s, (if ℓ = 0 then 4 * Real.log N else A / |(ℓ:ℝ)|)
          ≤ 4 * Real.log N + A * (Ch3 * Real.log N) := by
        rw [← Finset.sum_erase_add s
            (fun x => if x = 0 then 4 * Real.log N else A / |(x:ℝ)|) (a := 0) h0s,
          if_pos rfl]
        have hsum1 : ∑ x ∈ s.erase 0, (if x = 0 then 4 * Real.log N else A / |(x:ℝ)|)
            = ∑ x ∈ s.erase 0, A / |(x:ℝ)| := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [if_neg (Finset.mem_erase.mp hx).1]
        rw [hsum1]
        have hmul : ∑ x ∈ s.erase 0, A / |(x:ℝ)| = A * ∑ x ∈ s.erase 0, (1 / |(x:ℝ)|) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [div_eq_mul_one_div]
        rw [hmul]
        have hbound : ∑ x ∈ s.erase 0, (1:ℝ) / |(x:ℝ)| ≤ Ch3 * Real.log N := by
          rw [hsdef]; exact hCh3 N hN
        have := mul_le_mul_of_nonneg_left hbound hA0
        linarith
      linarith
    have h2 : ∑ ℓ ∈ u.filter (fun ℓ => ¬ (ℓ ∈ s)), ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖
        ≤ B * (Ct4 / N) := by
      have h2a : ∑ ℓ ∈ u.filter (fun ℓ => ¬ (ℓ ∈ s)), ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖
          ≤ ∑ ℓ ∈ u.filter (fun ℓ => ¬ (ℓ ∈ s)),
              (if (N:ℤ) < |ℓ| then B / ((ℓ:ℝ)^2) else 0) := by
        apply Finset.sum_le_sum
        intro ℓ hℓ
        have hnot : ℓ ∉ s := (Finset.mem_filter.mp hℓ).2
        have hgt : (N:ℤ) < |ℓ| := by
          rw [← not_le]
          intro hle
          exact hnot (by rw [hsdef, Finset.mem_Icc]; exact abs_le.mp hle)
        have hne : ℓ ≠ 0 := by
          intro h0; exact hnot (h0 ▸ h0s)
        rw [if_pos hgt, hBdef]
        exact logSine_norm_Ffun_coeff_le_sq N hN hne
      have h2b : ∑ ℓ ∈ u.filter (fun ℓ => ¬ (ℓ ∈ s)),
            (if (N:ℤ) < |ℓ| then B / ((ℓ:ℝ)^2) else 0)
          ≤ ∑' ℓ : ℤ, (if (N:ℤ) < |ℓ| then B / ((ℓ:ℝ)^2) else 0) :=
        Summable.sum_le_tsum _ (fun i _ => by split <;> positivity) (logSine_summable_int_tail B hB0 N)
      have h2c : (∑' ℓ : ℤ, (if (N:ℤ) < |ℓ| then B / ((ℓ:ℝ)^2) else 0))
          ≤ B * (Ct4 / N) := by
        rw [show (fun ℓ : ℤ => if (N:ℤ) < |ℓ| then B / ((ℓ:ℝ)^2) else 0)
            = (fun ℓ : ℤ => B * (if (N:ℤ) < |ℓ| then (1:ℝ) / ((ℓ:ℝ)^2) else 0)) by
          funext ℓ
          by_cases h : (N:ℤ) < |ℓ|
          · rw [if_pos h, if_pos h, div_eq_mul_one_div]
          · rw [if_neg h, if_neg h, mul_zero]]
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (hCt4 N hN) hB0
      linarith
    linarith
  have hsumm : Summable (fun ℓ : ℤ => ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖) :=
    summable_of_sum_le (fun ℓ => norm_nonneg _) hpartial
  have hsummC : Summable (fourierCoeff (⇑(logSine_Ffun N hN1))) := Summable.of_norm hsumm
  have hle : (∑' ℓ : ℤ, ‖fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ‖)
      ≤ 4 * Real.log N + A * (Ch3 * Real.log N) + B * (Ct4 / N) :=
    hsumm.tsum_le_of_sum_le hpartial
  have hkey : Real.log N ≤ (Real.log N)^2 / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    nlinarith [hlog2N, hlogN]
  have hfin : 4 * Real.log N + A * (Ch3 * Real.log N) + B * (Ct4 / N)
      ≤ (Ci1 * Ch3 / (2 * Real.pi) + Ci2 * Ct4 / (2 * Real.pi * Real.log 2)
          + 4 / Real.log 2 + 1) * (Real.log N)^2 := by
    have hA' : A * (Ch3 * Real.log N) ≤ Ci1 * Ch3 / (2*Real.pi) * (Real.log N)^2 := by
      calc A * (Ch3 * Real.log N) ≤ (Ci1 * Real.log N / (2*Real.pi)) * (Ch3 * Real.log N) :=
            mul_le_mul_of_nonneg_right hAb (by positivity)
        _ = Ci1 * Ch3 / (2*Real.pi) * (Real.log N)^2 := by ring
    have hB' : B * (Ct4 / N) ≤ Ci2 * Ct4 / (2*Real.pi) * Real.log N := by
      calc B * (Ct4 / N) ≤ (Ci2 * (N:ℝ) * Real.log N / (2*Real.pi)) * (Ct4 / N) :=
            mul_le_mul_of_nonneg_right hBb (by positivity)
        _ = Ci2 * Ct4 / (2*Real.pi) * Real.log N := by
            field_simp
    have hB'' : B * (Ct4 / N) ≤ Ci2 * Ct4 / (2*Real.pi * Real.log 2) * (Real.log N)^2 := by
      refine hB'.trans ?_
      have hK0 : 0 ≤ Ci2 * Ct4 / (2*Real.pi) := by positivity
      calc Ci2 * Ct4 / (2*Real.pi) * Real.log N
          ≤ Ci2 * Ct4 / (2*Real.pi) * ((Real.log N)^2 / Real.log 2) :=
            mul_le_mul_of_nonneg_left hkey hK0
        _ = Ci2 * Ct4 / (2*Real.pi * Real.log 2) * (Real.log N)^2 := by ring
    have h4 : 4 * Real.log N ≤ 4 / Real.log 2 * (Real.log N)^2 := by
      calc 4 * Real.log N ≤ 4 * ((Real.log N)^2 / Real.log 2) :=
            mul_le_mul_of_nonneg_left hkey (by norm_num)
        _ = 4 / Real.log 2 * (Real.log N)^2 := by ring
    nlinarith [hA', hB'', h4, sq_nonneg (Real.log N)]
  refine ⟨fun ℓ => fourierCoeff (⇑(logSine_Ffun N hN1)) ℓ, hsummC, hsumm, ?_, ?_⟩
  · exact le_trans hle hfin
  · intro α hα1 hα2
    have hαmem : α ∈ Set.Ioc (-Real.pi) Real.pi := by
      constructor
      · linarith [neg_abs_le α, Real.pi_gt_three]
      · linarith [le_abs_self α, Real.pi_gt_three]
    have hpt := has_pointwise_sum_fourier_series_of_summable (T := 2 * Real.pi) hsummC
      (α : AddCircle (2 * Real.pi))
    rw [logSine_Ffun_coe_eq N hN1 hαmem] at hpt
    have hcongr : (fun i : ℤ => fourierCoeff (⇑(logSine_Ffun N hN1)) i
          • fourier i (α : AddCircle (2 * Real.pi)))
        = (fun i : ℤ => fourierCoeff (⇑(logSine_Ffun N hN1)) i
          * Complex.exp (Complex.I * (i:ℂ) * (α:ℂ))) := by
      funext i
      have harg : (2 * (Real.pi : ℂ) * Complex.I * (i:ℂ) * (α:ℂ)) / ((2 * Real.pi : ℝ) : ℂ)
          = Complex.I * (i:ℂ) * (α:ℂ) := by
        push_cast
        field_simp
      rw [smul_eq_mul, fourier_coe_apply, harg]
    rw [hcongr] at hpt
    have hre : (∑' i : ℤ, fourierCoeff (⇑(logSine_Ffun N hN1)) i
        * Complex.exp (Complex.I * (i:ℂ) * (α:ℂ))).re = ufun N α := by
      rw [hpt.tsum_eq, ufunC, Complex.ofReal_re]
    rw [hre, ufun_of_range N hN α hα1 hα2]

end

end Work.FIArea4.S15red
