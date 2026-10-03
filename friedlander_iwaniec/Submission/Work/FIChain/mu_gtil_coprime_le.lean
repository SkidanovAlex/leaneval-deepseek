import Mathlib
import Submission.Work.FIChain.S3plusC_route_defs
import Submission.Work.FIChain.FIgtil_sum_19_real
import Submission.Work.FIChain.floor_log_rpow_six_le

namespace Work.FIChain

open Finset

/-- **`(2.4)` for `g̃ = FIgtil` with the trivial weight.**  Uniform in the coprimality parameter
`ℓ ≥ 1` and in `u ≥ 2`:
`|Σ_{d ≤ u, d squarefree, (d,ℓ)=1} μ(d)·g̃(d)| ≤ C·σ̃_ℓ·(log u)^{-6}`.

This is the weight-`w ≡ 1` instance of the PROVED `Work.FIChain.mu_density_abel_le` (whose
conclusion reads `≤ C·σ̃_ℓ·(w y·(log y)^{-6} + Σ_{d<y}|w d − w(d+1)|·(log(d+1))^{-6})`; for the
constant weight the second term vanishes).  Its hypotheses for `g = FIgtil` are all on disk:
`FIgtil_nonneg`, `FIgtil_one`, `FIgtil_mul` (coprime), `FIgtil_lt_one`, `FIgtil_bound`, and `(1.9)`
in the two-sided real `(log y)^{-10}` form, which follows from `ASP.FIgtil_sum_19_nat`
(`|Σ_{p≤y} g̃ p − loglog y − c| ≤ C((log y)^{-10} + 1/y)`; also convert the real `y` to `⌊y⌋₊`
— the `loglog` and `1/y` discrepancies are absorbed by constants, e.g. `1/⌊y⌋₊ ≤ 5·10⁵(log y)^{-10}`).
Finally convert `(log ⌊u⌋₊)^{-6} ≤ 64 (log u)^{-6}` for `u ≥ 2` (since `⌊u⌋₊ > u/2`).

The `(1.9)`-input is packaged as `Work.FIChain.FIgtil_sum_19_real` and the floor conversion as
`Work.FIChain.floor_log_rpow_six_le`; the sieve estimate itself is
`Commons.NumberTheory.Sieve.sieve_mu_sum_coprime_powLog` (equivalently, the `w ≡ 1` instance of
`Work.FIChain.mu_density_abel_le`), applied at `ϱ = ℓ`, `y = ⌊u⌋₊`. -/
theorem mu_gtil_coprime_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ : ℕ) (u : ℝ), 1 ≤ ℓ → 2 ≤ u →
      |∑ d ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun d => Squarefree d ∧ Nat.Coprime d ℓ),
          (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil d|
        ≤ C * Work.FIChain.sigmaTilde ℓ * (Real.log u) ^ (-6 : ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := Commons.NumberTheory.Sieve.sieve_mu_sum_coprime_powLog
    Submission.ASP.FIgtil Submission.ASP.FIgtil_nonneg Submission.ASP.FIgtil_one
    (fun m n h => Submission.ASP.FIgtil_mul h) (fun p hp => Submission.ASP.FIgtil_lt_one hp)
    Submission.ASP.FIgtil_bound FIgtil_sum_19_real
  refine ⟨64 * C, by positivity, ?_⟩
  intro ℓ u hℓ hu
  have hu2 : 2 ≤ ⌊u⌋₊ := Nat.le_floor hu
  have h1 := hC ℓ ⌊u⌋₊ hℓ hu2
  have hβ : 0 ≤ ∏ p ∈ ℓ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) :=
    Finset.prod_nonneg (fun p _ => by positivity)
  have hCβ : 0 ≤ C * ∏ p ∈ ℓ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) :=
    mul_nonneg (le_of_lt hCpos) hβ
  have hgoal : |∑ d ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun d => Squarefree d ∧ Nat.Coprime d ℓ),
          (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil d|
        ≤ C * (∏ p ∈ ℓ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (Real.log (⌊u⌋₊ : ℝ)) ^ (-6 : ℝ) := h1
  calc |∑ d ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun d => Squarefree d ∧ Nat.Coprime d ℓ),
          (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil d|
      ≤ C * (∏ p ∈ ℓ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (Real.log (⌊u⌋₊ : ℝ)) ^ (-6 : ℝ) := hgoal
    _ ≤ C * (∏ p ∈ ℓ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)))
          * (64 * (Real.log u) ^ (-6 : ℝ)) :=
        mul_le_mul_of_nonneg_left (floor_log_rpow_six_le u hu) hCβ
    _ = 64 * C * (∏ p ∈ ℓ.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))) * (Real.log u) ^ (-6 : ℝ) := by ring
    _ = (64 * C) * Work.FIChain.sigmaTilde ℓ * (Real.log u) ^ (-6 : ℝ) := by
        rw [Work.FIChain.sigmaTilde]

end Work.FIChain
