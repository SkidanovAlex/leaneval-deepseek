import Mathlib
import Submission.Work.FIArea6Hecke.R.AxisLogDefs
import Submission.Work.FIArea6Hecke.R.norm_logDeriv_one_sub_mul_cpow_le
import Submission.Work.FIArea6Hecke.R.sum_log_primes_le
import Submission.Work.FIArea6Hecke.R.AxisBadPolyLogDerivSum
import Submission.Work.FIArea6Hecke.R.AxisFactorLogDerivNormLe

set_option autoImplicit false

open scoped BigOperators

namespace Work.FIArea6Hecke.R

noncomputable section

/-- The logarithmic derivative of the bad-prime correction `G_d` is, at a point `s` of the
half-plane `1 < re s`, the sum of the logarithmic derivatives of its Euler factors. -/
private theorem axisBadPoly_logDeriv_eq_sum_aux
    (hsum : ∀ (d : ℕ) {s : ℂ}, 1 < s.re →
      logDeriv (axisBadPoly d) s
        = ∑ p ∈ (4 * d).primeFactors,
            (logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s
              + logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s))
    (hfac : ∀ {c : ℂ} {p : ℕ} {s : ℂ}, 2 ≤ p → ‖c‖ ≤ 1 → 1 < s.re →
      ‖logDeriv (fun u : ℂ => (1 : ℂ) - c * (p : ℂ) ^ (-u)) s‖ ≤ (4 / 3) * Real.log (p : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ σ τ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv (Work.FIArea6Hecke.R.axisBadPoly d) ((σ : ℂ) + (τ : ℂ) * Complex.I)
        / Work.FIArea6Hecke.R.axisBadPoly d ((σ : ℂ) + (τ : ℂ) * Complex.I)).re
        ≤ C * Real.log (4 * (d : ℝ)) := by
  refine ⟨8 / 3, by norm_num, ?_⟩
  intro d hd σ τ hσ1 hσ2
  set s : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hsdef
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hs : 1 < s.re := by rw [hsre]; exact hσ1
  have hS : ∀ p ∈ (4 * d).primeFactors, Nat.Prime p ∧ p ∣ 4 * d :=
    fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp⟩
  have h1 : -deriv (axisBadPoly d) s / axisBadPoly d s = -logDeriv (axisBadPoly d) s := by
    rw [neg_div, ← logDeriv_apply]
  rw [h1, Complex.neg_re, hsum d hs, Complex.re_sum]
  simp only [Complex.add_re]
  have hterm : ∀ p ∈ (4 * d).primeFactors,
      -((logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s).re
        + (logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s).re)
      ≤ (4 / 3) * Real.log (p : ℝ) + (4 / 3) * Real.log (p : ℝ) := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hF : ‖logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s‖
        ≤ (4 / 3) * Real.log (p : ℝ) := by
      have h := hfac (c := 1) (p := p) (s := s) hp2 (by simp) hs
      simpa using h
    have hG : ‖logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s‖
        ≤ (4 / 3) * Real.log (p : ℝ) :=
      hfac (c := axisChi4 p) (p := p) (s := s) hp2 (axisChi4_norm_le_one p) hs
    have aF : -(logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s).re
        ≤ (4 / 3) * Real.log (p : ℝ) :=
      (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hF)
    have aG : -(logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s).re
        ≤ (4 / 3) * Real.log (p : ℝ) :=
      (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans hG)
    linarith
  have hsum_le := Finset.sum_le_sum hterm
  have hsum_neg : -(∑ p ∈ (4 * d).primeFactors,
        ((logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s).re
         + (logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s).re))
      = ∑ p ∈ (4 * d).primeFactors,
        -((logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s).re
         + (logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s).re) := by
    rw [Finset.sum_neg_distrib]
  have hcomb : (∑ p ∈ (4 * d).primeFactors,
        ((4 / 3) * Real.log (p : ℝ) + (4 / 3) * Real.log (p : ℝ)))
      = (8 / 3) * (∑ p ∈ (4 * d).primeFactors, Real.log (p : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    ring
  have hlog : (∑ p ∈ (4 * d).primeFactors, Real.log (p : ℝ)) ≤ Real.log (4 * (d : ℝ)) :=
    sum_log_primes_le d _ hd hS
  calc -(∑ p ∈ (4 * d).primeFactors,
        ((logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s).re
         + (logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s).re))
      = ∑ p ∈ (4 * d).primeFactors,
        -((logDeriv (fun u : ℂ => (1 : ℂ) - (p : ℂ) ^ (-u)) s).re
         + (logDeriv (fun u : ℂ => (1 : ℂ) - axisChi4 p * (p : ℂ) ^ (-u)) s).re) := hsum_neg
    _ ≤ ∑ p ∈ (4 * d).primeFactors,
        ((4 / 3) * Real.log (p : ℝ) + (4 / 3) * Real.log (p : ℝ)) := hsum_le
    _ = (8 / 3) * (∑ p ∈ (4 * d).primeFactors, Real.log (p : ℝ)) := hcomb
    _ ≤ (8 / 3) * Real.log (4 * (d : ℝ)) := mul_le_mul_of_nonneg_left hlog (by norm_num)

theorem AxisBadPolyOffAxisLogDerivReBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ σ τ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv (Work.FIArea6Hecke.R.axisBadPoly d) ((σ : ℂ) + (τ : ℂ) * Complex.I)
        / Work.FIArea6Hecke.R.axisBadPoly d ((σ : ℂ) + (τ : ℂ) * Complex.I)).re
        ≤ C * Real.log (4 * (d : ℝ)) :=
  axisBadPoly_logDeriv_eq_sum_aux AxisBadPolyLogDerivSum AxisFactorLogDerivNormLe

end

end Work.FIArea6Hecke.R
