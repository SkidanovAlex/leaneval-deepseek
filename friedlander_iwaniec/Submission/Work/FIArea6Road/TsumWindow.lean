/-
# `Submission.Work.FIArea6Road.TsumWindow` — the finite-window form of the §16 heart

The Möbius-twisted Hecke sum `Tsum` of *FI* (16.30) is an infinite series, but the test function
`p` vanishes off the segment `(N, (1+θ)N]` (4.12)/(5.14).  Hence every summand with `n = 0` or
`n > ⌊(1+θ)N⌋₊` is zero and the series collapses to the finite sum over the window
`1 ≤ n ≤ ⌊(1+θ)N⌋₊`:

  `Tsum Pa χ m p = Σ_{1 ≤ n ≤ ⌊(1+θ)N⌋₊} tsumTerm Pa χ m p n`.

The two halves of the support argument are:

* `n = 0`: `NoSmallPrimesNat Pa 0` is *false* (since `2 ≤ Pa.Pz`, `2` is prime and `2 ∣ 0`), so the
  indicator kills the term;
* `n > ⌊(1+θ)N⌋₊`: then `(1+θ)N < ⌊(1+θ)N⌋₊ + 1 ≤ n` (`Nat.lt_floor_add_one`), while
  `p u ≠ 0 → u ≤ (1+θ)N` (`hpsupp`), so `p n = 0`.
-/
import Mathlib
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace Work.FIArea6Road

theorem TsumWindow
    (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (hpsupp : ∀ u : ℝ, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) :
    Work.FIArea6Hecke.Tsum Pa chi m p
      = ∑ n ∈ Finset.Icc 1 ⌊(1 + Pa.θ) * Pa.N⌋₊, Work.FIArea6.TauPieces.tsumTerm Pa chi m p n := by
  rw [Work.FIArea6.TauPieces.Tsum_eq_tsumTerm]
  refine tsum_eq_sum ?_
  intro n hn
  rw [Finset.mem_Icc] at hn
  by_cases hn1 : 1 ≤ n
  · -- the window's right end: `⌊(1+θ)N⌋₊ < n` forces `(1+θ)N < n`, hence `p n = 0`
    have hnM : ⌊(1 + Pa.θ) * Pa.N⌋₊ < n := by
      by_contra hc
      exact hn ⟨hn1, not_lt.mp hc⟩
    have hp0 : p (n : ℝ) = 0 := by
      by_contra hne
      have h2 := (hpsupp (n : ℝ) hne).2
      have hlt : (1 + Pa.θ) * Pa.N < (n : ℝ) := by
        have hle : ⌊(1 + Pa.θ) * Pa.N⌋₊ + 1 ≤ n := hnM
        have hleR : ((⌊(1 + Pa.θ) * Pa.N⌋₊ : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
          exact_mod_cast hle
        have := Nat.lt_floor_add_one ((1 + Pa.θ) * Pa.N)
        linarith
      linarith
    simp [Work.FIArea6.TauPieces.tsumTerm, hp0]
  · -- `n < 1`, i.e. `n = 0`, and `(0, Π) ≠ 1` because `2 ∣ 0` and `2 ≤ Pz`
    have hn0 : n = 0 := by omega
    subst hn0
    have h0 : ¬ Work.FIArea6Hecke.NoSmallPrimesNat Pa 0 := by
      intro h
      exact h 2 Nat.prime_two Pa.hP2 (dvd_zero 2)
    simp [Work.FIArea6.TauPieces.tsumTerm, h0]

end Work.FIArea6Road
