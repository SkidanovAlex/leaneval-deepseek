import Mathlib
import Submission.Work.FIArea2.R6.Area6eDefs
import Submission.Work.FIArea2.R6.Inputs6
import Submission.Work.FIArea2.R6.sec9Psum_le_of_Lsum_six
import Submission.Work.FIArea2.R6.sec9_Z_bound_six
import Submission.Work.FIArea2.R6.Assembly6
import Submission.Work.FIArea2.R6.BetaPrim6
import Submission.Work.FIArea2.R6.sec9ErrSum6_pair_le
import Submission.Work.FIArea2.R6.sec9ErrSum6_arith

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The §9 pair sum of (9.1) against the coefficient-free §9 sum (9.5).**

`sec9ErrSum6` is `√M` times the (9.1) right-hand side summed over the coprime pairs of the box with
the (9.2) weight `Haver`, the factor `|z₁z₂|^{-1/4}` and the logarithmic factor
`log(2 + 1/(1-γ²))`.  Each summand is at most

  `256 (log N + 2) N^{-1/2} · ‖β z₁‖‖β z₂‖ τ(Δ)³|Δ|⁻¹ · sec9Usum Pa z₁ z₂`,

by `sec9ErrSum6_pair_le` (the constants are `4·64`: the log bound `sec9_log_bound6` and the (9.2)
comparison `IsBetaCoeff6.haver_le6`), so the pair sum is at most
`256 (log N + 2) N^{-1/2} · sec9Psum6 Pa β`. -/
lemma sec9ErrSum6_le_sec9Psum6 (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    sec9ErrSum6 Pa β
      ≤ Real.sqrt Pa.M * (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2))
          * sec9Psum6 Pa β := by
  have hpair := sec9ErrSum6_pair_le Pa φ z0 β hβ
  have hK0 : (0 : ℝ) ≤ 256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2) := by
    have h1 : (0 : ℝ) ≤ Real.log Pa.N + 2 := by
      have h2 := Real.log_nonneg Pa.hN1
      linarith
    have h2 : (0 : ℝ) ≤ Pa.N ^ (-(1 : ℝ) / 2) :=
      Real.rpow_nonneg (by linarith [Pa.hN1]) _
    positivity
  have hsum : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
      (if Work.FIPlan.GaussCoprime z1 z2 then
        ‖β z1‖ * ‖β z2‖ * (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
          * ((((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
              / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
              * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
              * Work.FIArea2.Haver Pa z1 z2)
       else 0))
      ≤ (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2)) * sec9Psum6 Pa β := by
    rw [sec9Psum6, Finset.mul_sum]
    refine Finset.sum_le_sum fun z1 h1 => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun z2 h2 => ?_
    by_cases hc : Work.FIPlan.GaussCoprime z1 z2
    · rw [if_pos hc]
      exact hpair z1 h1 z2 h2 hc
    · rw [if_neg hc]
      exact mul_nonneg hK0 (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (sec9Core6_nonneg Pa z1 z2)) (Work.FIArea2.sec9Usum_nonneg Pa z1 z2))
  calc sec9ErrSum6 Pa β
      = Real.sqrt Pa.M * (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.GaussCoprime z1 z2 then
            ‖β z1‖ * ‖β z2‖ * (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
              * ((((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
                  / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
                  * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
                  * Work.FIArea2.Haver Pa z1 z2)
           else 0)) := rfl
    _ ≤ Real.sqrt Pa.M * ((256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2))
          * sec9Psum6 Pa β) := mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg Pa.M)
    _ = Real.sqrt Pa.M * (256 * (Real.log Pa.N + 2) * Pa.N ^ (-(1 : ℝ) / 2))
          * sec9Psum6 Pa β := by ring

/-- ***FI* (9.10) for the §9 error sum of the round-6 area-2 assembly.**  For every `η ∈ (0, 3/32)`
there are constants `Cb, x0 > 0` such that for every datum `Pa` with `x ≥ x0` and `Pa.η = η`, every
round-6 coefficient `β` (`IsBetaCoeff6`) satisfies

  `sec9ErrSum6 Pa β ≤ Cb·ϑ⁻¹τ²N²(log N)^{bFun η}`.

The three ingredients are the pointwise (9.1) bound (`sec9ErrSum6_pair_le`), the §9 aggregation
`sec9Psum_le_of_Lsum_six` fed with the lacunarity input `hL` and the per-frequency bound
`sec9_Z_bound_six` (`KZ = 8`), and the arithmetic reduction `sec9ErrSum6_arith` (the geometric
`√(M/N)(H²+1)(2R+1)² ≤ 128N²` of `Assembly6.geom_le_six`, the logarithmic
`log(H+R+2) ≤ 2 log N` of `Assembly6.log_pow_le_six`, and `bFun η ≥ 5000 ≥ 2KL + 25`). -/
theorem sec9ErrSum6_bound (hL : Work.FIArea2.R6.LacProp) :
    ∀ η : ℝ, 0 < η → η < 3 / 32 →
    ∃ Cb x0 : ℝ, 0 < Cb ∧ 0 < x0 ∧
      ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
      ∀ (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
        Work.FIArea2.R6.sec9ErrSum6 Pa β
          ≤ Cb * Pa.ϑ⁻¹ * Pa.τ ^ (2 : ℕ) * Pa.N ^ 2
              * (Real.log Pa.N) ^ (Work.FITop4.bFun Pa.η) := by
  intro η hη0 hη32
  obtain ⟨CL, hCL, KL, hKL, hLb⟩ := hL
  obtain ⟨CZ, hCZ, hZ⟩ := sec9_Z_bound_six
  obtain ⟨C, hC, hPsum⟩ := sec9Psum_le_of_Lsum_six CZ hCZ 8 hZ CL hCL KL hLb
  refine ⟨256 * 128 * 2 * C * CZ * CL, 4096, by positivity, by norm_num, ?_⟩
  intro Pa hx0 hη φ z0 β hβ
  have hN8 : 8 ≤ Pa.N := by
    have hx1 : (1 : ℝ) ≤ (Pa.x : ℝ) := by linarith
    have h4096 : ((4096 : ℝ)) ^ ((1 : ℝ) / 4) = 8 := by
      rw [show (4096 : ℝ) = (8 : ℝ) ^ 4 by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ (8 : ℝ))]
      norm_num
    have hstep1 : (8 : ℝ) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
      have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ (4096 : ℝ)) hx0
        (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 4)
      rwa [h4096] at h
    have hstep2 : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [Pa.hη])
    have hlt : (8 : ℝ) < Pa.N := lt_of_le_of_lt (le_trans hstep1 hstep2) Pa.hNlo
    exact le_of_lt hlt
  have hη0' : 0 < Pa.η := by rw [hη]; exact hη0
  have hη32' : Pa.η < 3 / 32 := by rw [hη]; exact hη32
  have hErr := sec9ErrSum6_le_sec9Psum6 Pa φ z0 β hβ
  have hP := hPsum Pa β (fun z => Work.FIArea2.R6.IsBetaCoeff6.norm_le_tau hβ z)
  exact sec9ErrSum6_arith Pa CZ CL C KL hCZ hCL hC hKL hN8 hη0' hη32' hErr hP

end

end Work.FIArea2.R6
