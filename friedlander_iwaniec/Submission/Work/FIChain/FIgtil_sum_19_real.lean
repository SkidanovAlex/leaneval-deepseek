import Mathlib
import Submission.Work.FIChain.S3plusC_route_defs
import Submission.ASP.S28

namespace Work.FIChain

/-- **(1.9) for the density `g̃ = FIgtil`, in the two-sided real `(log y)^{-10}` form.**
On disk (`Submission.ASP.FIgtil_sum_19_nat`) is the `ℕ`-indexed version
`|Σ_{p ≤ n} g̃ p − loglog n − c| ≤ C·((log n)^{-10} + 1/n)`.  This is the `ℝ`-indexed
version needed as the hypothesis of `Commons.NumberTheory.Sieve.sieve_mu_sum_coprime_powLog`
(and hence of the PROVED `Work.FIChain.mu_density_abel_le`), in which the sum runs over
`(⌊y⌋₊).primesLE`: the discrepancies `loglog ⌊y⌋₊ − loglog y` and `1/⌊y⌋₊` are absorbed by
constants using `log ⌊y⌋₊ ≥ (1/2)·log y`, `y ≤ 2·⌊y⌋₊`, `log t ≤ 10·t^{1/10}` (hence
`1/y ≤ 10^{10}·(log y)^{-10}`) and `|loglog y − loglog ⌊y⌋₊| ≤ 4/(y·log y) ≤ 4·10^9·(log y)^{-10}`. -/
theorem FIgtil_sum_19_real :
    ∃ c C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (⌊y⌋₊).primesLE, Submission.ASP.FIgtil p) - (Real.log (Real.log y) + c)|
        ≤ C * (Real.log y) ^ (-10 : ℝ) := by
  -- `Submission.ASP.FIgtil_sum_19_real` (module `Submission.ASP.S28`) is the same statement
  -- with the sum over `(Icc 2 ⌊y⌋₊).filter Nat.Prime` and the error in `zpow` form.
  obtain ⟨c, C, hC, h⟩ := Submission.ASP.FIgtil_sum_19_real
  refine ⟨c, C, hC, fun y hy => ?_⟩
  -- the two index sets agree, because a prime is `≥ 2`
  have hset : (⌊y⌋₊).primesLE = (Finset.Icc 2 ⌊y⌋₊).filter Nat.Prime := by
    ext p
    rw [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hle, hp⟩; exact ⟨⟨hp.two_le, hle⟩, hp⟩
    · rintro ⟨⟨-, hle⟩, hp⟩; exact ⟨hle, hp⟩
  have hthis := h y hy
  rw [← hset] at hthis
  -- `A - (loglog y + c) = A - loglog y - c`
  have hsub : (∑ p ∈ (⌊y⌋₊).primesLE, Submission.ASP.FIgtil p) - Real.log (Real.log y) - c
      = (∑ p ∈ (⌊y⌋₊).primesLE, Submission.ASP.FIgtil p) - (Real.log (Real.log y) + c) := by
    ring
  rw [hsub] at hthis
  -- `(log y)^{-10}` in `rpow` form equals the `zpow` form `(log y)^{-(10:ℤ)}`
  rw [← Real.rpow_neg_ofNat (Real.log y) 10] at hthis
  exact hthis

end Work.FIChain
