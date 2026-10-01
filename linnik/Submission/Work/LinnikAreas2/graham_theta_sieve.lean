import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas.Density4.thetaDiag_theta_at_le
import Submission.Work.LinnikAreas.Density4.vonMangoldt_sq_sum_bound
import Submission.Work.ZeroDensity.Jutila.bvDefs
import Submission.Work.ZeroDensity.Jutila.LzSqIntGood
import Submission.Work.ZeroDensity.Jutila.LzSqIntBad
import Submission.Work.LinnikAreas2.lz_sq_sharp_real_of_int
import Submission.Work.LinnikAreas2.bz_sq_hard_via_s3h

namespace Work.LinnikAreas2

open scoped BigOperators

noncomputable section

/-- **The `θ`-mollifier divisor sum is the truncated von Mangoldt sum `Lz`, divided by `log W`.**
Indeed `θ_d = μ(d)·log(W/d)/log W` for `d ≤ W` and `θ_d = 0` for `d > W`. -/
lemma theta_divisor_sum_eq_Lz (W : ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM W d)
      = Work.ZeroDensity.Jutila.Lz W n / Real.log W := by
  have hterm : ∀ d : ℕ, Work.LinnikAreas.Density4.thetaM W d
      = (if (d : ℝ) ≤ W then (ArithmeticFunction.moebius d : ℝ) * Real.log (W / (d : ℝ))
          else 0) / Real.log W := by
    intro d
    rw [Work.LinnikAreas.Density4.thetaM]
    by_cases h : (d : ℝ) ≤ W
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, zero_div]
  calc (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM W d)
      = ∑ d ∈ n.divisors, (if (d : ℝ) ≤ W then
            (ArithmeticFunction.moebius d : ℝ) * Real.log (W / (d : ℝ)) else 0) / Real.log W :=
        Finset.sum_congr rfl (fun d _ => hterm d)
    _ = (∑ d ∈ n.divisors, (if (d : ℝ) ≤ W then
            (ArithmeticFunction.moebius d : ℝ) * Real.log (W / (d : ℝ)) else 0)) / Real.log W := by
        rw [Finset.sum_div]
    _ = Work.ZeroDensity.Jutila.Lz W n / Real.log W := by
        rw [Work.ZeroDensity.Jutila.Lz, Finset.sum_filter]

theorem graham_theta_sieve (ε : ℝ) (hε : 0 < ε) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
    ∀ (w : ℝ) (L : ℝ), 0 < w → 0 < L →
      (∀ N : ℕ, 1 ≤ N → (N : ℝ) ≤ Real.exp (w * L) →
        (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
            Work.LinnikAreas.Density4.thetaM (Real.exp (w * L)) d) ^ 2)
          ≤ 1 + (1 + ε) * (N : ℝ) * Real.log (N : ℝ) / (Real.log (Real.exp (w * L))) ^ 2
              + C₁ * (N : ℝ) / (Real.log (Real.exp (w * L))) ^ 2) ∧
      (∀ N : ℕ, Real.exp (w * L) ≤ (N : ℝ) →
        (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
            Work.LinnikAreas.Density4.thetaM (Real.exp (w * L)) d) ^ 2)
          ≤ 1 + (1 + ε) * (N : ℝ) / Real.log (Real.exp (w * L))
              + C₁ * (N : ℝ) / (Real.log (Real.exp (w * L))) ^ 2) := by
  obtain ⟨Cv, hCv, hv⟩ := Work.LinnikAreas.Density4.vonMangoldt_sq_sum_bound
  obtain ⟨Ce, hCe, he⟩ := Work.ZeroDensity.Jutila.LzSqIntGood
  obtain ⟨Ch, hCh, hh⟩ := Work.ZeroDensity.Jutila.LzSqIntBad bz_sq_hard_via_s3h
  obtain ⟨Cz, hCz, hz⟩ := lz_sq_sharp_real_of_int ⟨Ce, hCe, he⟩ ⟨Ch, hCh, hh⟩
  refine ⟨Cv + Cz + 1, by positivity, ?_⟩
  intro w L hw hL
  set M : ℝ := w * L with hMdef
  have hM : 0 < M := by rw [hMdef]; exact mul_pos hw hL
  have hlogW : Real.log (Real.exp M) = M := Real.log_exp M
  have hW1 : 1 < Real.exp M := Real.one_lt_exp_iff.mpr hM
  constructor
  · -- Clause 1: `1 ≤ N ≤ e^M`
    intro N hN1 hNW
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1'
    have hpt : ∀ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
          Work.LinnikAreas.Density4.thetaM (Real.exp M) d) ^ 2
        = (if n = 1 then (1 : ℝ) else 0) + (ArithmeticFunction.vonMangoldt n) ^ 2 / M ^ 2 := by
      intro n hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
      have hnl : (n : ℝ) ≤ Real.exp M := le_trans (by exact_mod_cast hnN) hNW
      rw [Work.LinnikAreas.Density4.thetaDiag_theta_at_le M hM n hn1 hnl]
      by_cases h1 : n = 1
      · subst h1
        rw [if_pos rfl, ArithmeticFunction.vonMangoldt_apply_one]
        norm_num
      · rw [if_neg h1, zero_add, div_pow, zero_add]
    have h1sum : (∑ n ∈ Finset.Icc 1 N, (if n = 1 then (1 : ℝ) else 0)) = 1 := by
      rw [Finset.sum_ite_eq']
      simp [Finset.mem_Icc, hN1]
    have hdiag : (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
          Work.LinnikAreas.Density4.thetaM (Real.exp M) d) ^ 2)
        = 1 + (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2) / M ^ 2 := by
      rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_div, h1sum]
    rw [hdiag, hlogW]
    have hsq := hv N hN1
    have hkey : (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2)
        ≤ (1 + ε) * ((N : ℝ) * Real.log (N : ℝ)) + (Cv + Cz + 1) * (N : ℝ) := by
      have h1 : (0 : ℝ) ≤ ε * ((N : ℝ) * Real.log (N : ℝ)) := by positivity
      have h2 : Cv * (N : ℝ) ≤ (Cv + Cz + 1) * (N : ℝ) := by
        have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        nlinarith [hCz.le]
      nlinarith [hsq]
    calc 1 + (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n) ^ 2) / M ^ 2
        ≤ 1 + ((1 + ε) * ((N : ℝ) * Real.log (N : ℝ)) + (Cv + Cz + 1) * (N : ℝ)) / M ^ 2 := by
          gcongr
      _ = 1 + (1 + ε) * (N : ℝ) * Real.log (N : ℝ) / M ^ 2
            + (Cv + Cz + 1) * (N : ℝ) / M ^ 2 := by
          rw [add_div]; ring
  · -- Clause 2: `N ≥ e^M`
    intro N hNW
    rw [hlogW]
    have hN1 : 1 ≤ N := by
      have h : (1 : ℝ) ≤ (N : ℝ) :=
        le_of_lt (lt_of_lt_of_le (Real.one_lt_exp_iff.mpr hM) hNW)
      exact_mod_cast h
    by_cases hW2 : (2 : ℝ) ≤ Real.exp M
    · -- large cut-off: the sharp real-cut-off second moment of `Lz`
      have hz' := hz (Real.exp M) hW2 N hNW
      have hpt : ∀ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
            Work.LinnikAreas.Density4.thetaM (Real.exp M) d) ^ 2
          = (Work.ZeroDensity.Jutila.Lz (Real.exp M) n) ^ 2 / M ^ 2 := by
        intro n _
        rw [theta_divisor_sum_eq_Lz (Real.exp M) n, hlogW, div_pow]
      have hS : (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
            Work.LinnikAreas.Density4.thetaM (Real.exp M) d) ^ 2)
          = (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz (Real.exp M) n) ^ 2) / M ^ 2 := by
        rw [Finset.sum_congr rfl hpt, Finset.sum_div]
      rw [hS]
      have hlogW' : Real.log (Real.exp M) = M := Real.log_exp M
      rw [hlogW'] at hz'
      have hstep : (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz (Real.exp M) n) ^ 2) / M ^ 2
          ≤ ((N : ℝ) * M + Cz * (N : ℝ)) / M ^ 2 :=
        div_le_div_of_nonneg_right hz' (by positivity)
      calc (∑ n ∈ Finset.Icc 1 N, (Work.ZeroDensity.Jutila.Lz (Real.exp M) n) ^ 2) / M ^ 2
          ≤ ((N : ℝ) * M + Cz * (N : ℝ)) / M ^ 2 := hstep
        _ = (N : ℝ) / M + Cz * (N : ℝ) / M ^ 2 := by
            have hMne : M ≠ 0 := ne_of_gt hM
            field_simp
        _ ≤ 1 + (1 + ε) * (N : ℝ) / M + (Cv + Cz + 1) * (N : ℝ) / M ^ 2 := by
            have h1 : (N : ℝ) / M ≤ (1 + ε) * (N : ℝ) / M := by
              have hnn : (0 : ℝ) ≤ (N : ℝ) / M := by positivity
              have hεx : (0 : ℝ) ≤ ε * ((N : ℝ) / M) := mul_nonneg hε.le hnn
              have hEq : (1 + ε) * (N : ℝ) / M = (N : ℝ) / M + ε * ((N : ℝ) / M) :=
                by ring
              rw [hEq]
              linarith
            have h2 : Cz * (N : ℝ) / M ^ 2 ≤ (Cv + Cz + 1) * (N : ℝ) / M ^ 2 := by
              apply div_le_div_of_nonneg_right _ (by positivity)
              nlinarith [hCv.le, Nat.cast_nonneg (α := ℝ) N]
            linarith
    · -- small cut-off `e^M < 2`: the divisor sum is constantly `1`
      have hlt2 : Real.exp M < 2 := not_le.mp hW2
      have hinner : ∀ n : ℕ, 1 ≤ n → (∑ d ∈ n.divisors,
            Work.LinnikAreas.Density4.thetaM (Real.exp M) d) = 1 := by
        intro n hn
        have hfilt : n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Real.exp M) = {1} := by
          ext d
          simp only [Finset.mem_filter, Finset.mem_singleton, Nat.mem_divisors]
          constructor
          · rintro ⟨⟨hdvd, _⟩, hdle⟩
            have hpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
            have hlt : (d : ℝ) < 2 := lt_of_le_of_lt hdle hlt2
            have hlt' : d < 2 := by exact_mod_cast hlt
            omega
          · rintro rfl
            have h1e : ((1 : ℕ) : ℝ) ≤ Real.exp M := by
              simpa using le_of_lt hW1
            exact ⟨⟨one_dvd n, by omega⟩, h1e⟩
        have hsum1 : (∑ d ∈ n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Real.exp M),
              (ArithmeticFunction.moebius d : ℝ) * Real.log (Real.exp M / (d : ℝ)))
            = Real.log (Real.exp M) := by
          rw [hfilt, Finset.sum_singleton, ArithmeticFunction.moebius_apply_one]
          norm_num
        rw [theta_divisor_sum_eq_Lz, Work.ZeroDensity.Jutila.Lz, hsum1, hlogW]
        exact div_self (ne_of_gt hM)
      have hS : (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
            Work.LinnikAreas.Density4.thetaM (Real.exp M) d) ^ 2) = (N : ℝ) := by
        have hpt : ∀ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors,
            Work.LinnikAreas.Density4.thetaM (Real.exp M) d) ^ 2 = (1 : ℝ) := by
          intro n hn
          rw [hinner n (Finset.mem_Icc.mp hn).1, one_pow]
        rw [Finset.sum_congr rfl hpt, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
          nsmul_eq_mul, mul_one]
      rw [hS]
      have hMlt1 : M < 1 + ε := by
        have hMlt : M < Real.log 2 := by
          rw [← hlogW]
          exact Real.log_lt_log (Real.exp_pos M) hlt2
        have hlog2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
        linarith
      have h1 : (N : ℝ) ≤ (1 + ε) * (N : ℝ) / M := by
        rw [le_div_iff₀ hM]
        have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        nlinarith
      have h2 : (0 : ℝ) ≤ (Cv + Cz + 1) * (N : ℝ) / M ^ 2 := by positivity
      linarith

end

end Work.LinnikAreas2
