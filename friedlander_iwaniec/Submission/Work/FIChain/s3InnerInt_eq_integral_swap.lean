import Mathlib
import Submission.Work.FIChain.S3plusC_route_defs
import Submission.Work.FIChain.s3swap_indicator_integral
import Submission.Work.FIChain.s3swap_intervalIntegrable

set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset MeasureTheory
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Fubini swap for the `λ⁺`-inner sum.**  The integrated form `s3InnerInt` of the inner `c`-sum,
`Σ_{c} a(ℓc) ∫_1^{c/Cm} ρ(c;u) du/u`, equals the single integral over `u ∈ [1, sz/Cm]` of the
`u`-wise sum `Σ_c [Cm·u < c] a(ℓc)ρ(c;u)/u`.  The point is that for `c` in the summation range,
`Cm·u < c ↔ u < c/Cm ≤ sz/Cm`, so the `c`-th inner integral `∫_1^{sz/Cm} [...]` collapses to
`∫_1^{c/Cm}`; the finite sum is then pulled out of the interval integral (each summand is
interval integrable since `Cm ≥ 1` and `|ρ(c;u)| ≤ τ(c)`). -/
theorem s3InnerInt_eq_integral_swap (a : ℕ → ℝ) (N ℓ Cm : ℕ) (z sz : ℝ)
    (hCm : 1 ≤ Cm) (hzCm : ((Cm : ℕ) : ℝ) ≤ z) (hsz : 0 < sz)
    (hT : 1 ≤ sz / (Cm : ℝ)) :
    s3InnerInt a N ℓ Cm z sz
      = ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)),
          ∑ c ∈ (Finset.Icc 1 N).filter
              (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N),
            (if (Cm : ℝ) * u < ((c : ℕ) : ℝ)
              then a (ℓ * c) * Submission.ASP.rhoTrunc c u else 0) / u := by
  classical
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by
    have h : (0 : ℕ) < Cm := by omega
    exact_mod_cast h
  rw [s3InnerInt]
  set S : Finset ℕ := (Finset.Icc 1 N).filter
      (fun c => z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N) with hSdef
  have hmem : ∀ c ∈ S, z < ((c : ℕ) : ℝ) ∧ ((c : ℕ) : ℝ) ≤ sz ∧ ℓ * c ≤ N := by
    intro c hc
    rw [hSdef] at hc
    exact (Finset.mem_filter.mp hc).2
  -- pointwise rewriting of the `c`-th summand as an indicator of `(-∞, c/Cm)`
  have hpoint : ∀ (c : ℕ) (u : ℝ),
      (if (Cm : ℝ) * u < ((c : ℕ) : ℝ)
        then a (ℓ * c) * Submission.ASP.rhoTrunc c u else 0) / u
        = (Set.Iio (((c : ℕ) : ℝ) / (Cm : ℝ))).indicator
            (fun u => a (ℓ * c) * Submission.ASP.rhoTrunc c u / u) u := by
    intro c u
    by_cases h : (Cm : ℝ) * u < ((c : ℕ) : ℝ)
    · have hmem' : u ∈ Set.Iio (((c : ℕ) : ℝ) / (Cm : ℝ)) := by
        rw [Set.mem_Iio, lt_div_iff₀ hCmpos]; linarith
      rw [if_pos h, Set.indicator_of_mem hmem']
    · have hmem' : u ∉ Set.Iio (((c : ℕ) : ℝ) / (Cm : ℝ)) := by
        rw [Set.mem_Iio, not_lt, div_le_iff₀ hCmpos]; linarith
      rw [if_neg h, Set.indicator_of_notMem hmem']
      simp
  have hfun : ∀ c : ℕ,
      (fun u : ℝ => (if (Cm : ℝ) * u < ((c : ℕ) : ℝ)
        then a (ℓ * c) * Submission.ASP.rhoTrunc c u else 0) / u)
        = (fun u : ℝ => (Set.Iio (((c : ℕ) : ℝ) / (Cm : ℝ))).indicator
            (fun u => a (ℓ * c) * Submission.ASP.rhoTrunc c u / u) u) :=
    fun c => funext (hpoint c)
  -- each summand is interval integrable on `1..sz/Cm`
  have hInt : ∀ c ∈ S, IntervalIntegrable
      (fun u : ℝ => (if (Cm : ℝ) * u < ((c : ℕ) : ℝ)
        then a (ℓ * c) * Submission.ASP.rhoTrunc c u else 0) / u)
      volume (1 : ℝ) (sz / (Cm : ℝ)) := by
    intro c hc
    obtain ⟨hcz, hcsz, -⟩ := hmem c hc
    have hczR : ((Cm : ℕ) : ℝ) < ((c : ℕ) : ℝ) := lt_of_le_of_lt hzCm hcz
    have h1X : (1 : ℝ) ≤ sz / (Cm : ℝ) := by
      have h1 : (1 : ℝ) < ((c : ℕ) : ℝ) / (Cm : ℝ) := (one_lt_div hCmpos).mpr hczR
      have h2 : ((c : ℕ) : ℝ) / (Cm : ℝ) ≤ sz / (Cm : ℝ) :=
        div_le_div_of_nonneg_right hcsz hCmpos.le
      linarith
    rw [hfun c]
    refine s3swap_intervalIntegrable (fun u : ℝ => a (ℓ * c) * Submission.ASP.rhoTrunc c u)
      (|a (ℓ * c)| * ((c.divisors.card : ℕ) : ℝ))
      (a := (1 : ℝ)) (b := sz / (Cm : ℝ)) (t := ((c : ℕ) : ℝ) / (Cm : ℝ))
      (le_refl 1) h1X ?_ ?_
    · exact measurable_const.mul (Submission.ASP.measurable_rhoTrunc c)
    · intro u
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (Submission.ASP.abs_rhoTrunc_le c u) (abs_nonneg _)
  -- pull the finite sum out of the interval integral
  have hIntSum : (∫ u in (1 : ℝ)..(sz / (Cm : ℝ)), ∑ c ∈ S,
        (if (Cm : ℝ) * u < ((c : ℕ) : ℝ)
          then a (ℓ * c) * Submission.ASP.rhoTrunc c u else 0) / u)
      = ∑ c ∈ S, ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)),
        (if (Cm : ℝ) * u < ((c : ℕ) : ℝ)
          then a (ℓ * c) * Submission.ASP.rhoTrunc c u else 0) / u :=
    intervalIntegral.integral_finsetSum hInt
  -- the `c`-th inner integral collapses to `∫_1^{c/Cm}`
  have hPer : ∀ c ∈ S, (∫ u in (1 : ℝ)..(sz / (Cm : ℝ)),
        (if (Cm : ℝ) * u < ((c : ℕ) : ℝ)
          then a (ℓ * c) * Submission.ASP.rhoTrunc c u else 0) / u)
      = a (ℓ * c) * ∫ u in (1 : ℝ)..(((c : ℕ) : ℝ) / (Cm : ℝ)),
          Submission.ASP.rhoTrunc c u / u := by
    intro c hc
    obtain ⟨hcz, hcsz, -⟩ := hmem c hc
    have hczR : ((Cm : ℕ) : ℝ) < ((c : ℕ) : ℝ) := lt_of_le_of_lt hzCm hcz
    have h1t : (1 : ℝ) ≤ ((c : ℕ) : ℝ) / (Cm : ℝ) :=
      le_of_lt ((one_lt_div hCmpos).mpr hczR)
    have htX : ((c : ℕ) : ℝ) / (Cm : ℝ) ≤ sz / (Cm : ℝ) :=
      div_le_div_of_nonneg_right hcsz hCmpos.le
    calc (∫ u in (1 : ℝ)..(sz / (Cm : ℝ)),
          (if (Cm : ℝ) * u < ((c : ℕ) : ℝ)
            then a (ℓ * c) * Submission.ASP.rhoTrunc c u else 0) / u)
        = ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)),
            (Set.Iio (((c : ℕ) : ℝ) / (Cm : ℝ))).indicator
              (fun u => a (ℓ * c) * Submission.ASP.rhoTrunc c u / u) u :=
          intervalIntegral.integral_congr (fun u _ => hpoint c u)
      _ = ∫ u in (1 : ℝ)..(((c : ℕ) : ℝ) / (Cm : ℝ)),
            a (ℓ * c) * Submission.ASP.rhoTrunc c u / u :=
          s3swap_indicator_integral
            (g := fun u : ℝ => a (ℓ * c) * Submission.ASP.rhoTrunc c u) h1t htX
      _ = ∫ u in (1 : ℝ)..(((c : ℕ) : ℝ) / (Cm : ℝ)),
            a (ℓ * c) * (Submission.ASP.rhoTrunc c u / u) :=
          intervalIntegral.integral_congr (fun u _ => mul_div_assoc _ _ _)
      _ = a (ℓ * c) * ∫ u in (1 : ℝ)..(((c : ℕ) : ℝ) / (Cm : ℝ)),
            Submission.ASP.rhoTrunc c u / u :=
          intervalIntegral.integral_const_mul _ _
  rw [hIntSum]
  exact Finset.sum_congr rfl (fun c hc => (hPer c hc).symm)

end

end Work.FIChain
