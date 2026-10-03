/-
# `Work.FIChain.sieveDens_mul_one_nonneg`

The §6 sieve density `ν ↦ g̃(ν)·hSieveC g̃ ε ν` of the `hSieveC`-input of
`Work.FIChain.SieveInput`: it takes the value `1` at `ν = 1`, it is *multiplicative* on coprime
arguments, and it is *nonnegative*.

Here `g̃ = Submission.ASP.FIgtil` is the (squarefree-supported) density of `ã = atil FIa`, and

    hSieveC g ε ν = ∏_{p ∣ ν} (1 + p^{-ε}) / (1 + p^{-ε} · g p)

is the `h(ν)` of the companion paper's §6.  Both factors behave as they should: `FIgtil` is
multiplicative (`Submission.ASP.FIgtil_mul`) and `hSieveC` inherits multiplicativity from
`Nat.Coprime.primeFactors_mul`; each local factor `(1 + p^{-ε})/(1 + p^{-ε}·g p)` has *strictly
positive* numerator and denominator for **every** `ε : ℝ` (as `p^{-ε} > 0` and `g p ≥ 0`), so no
sign condition on `ε` is needed.

Everything below is `sorry`-free.
-/
import Mathlib
import Submission.Work.FIChain.Defs

set_option autoImplicit false

namespace Work.FIChain

open Finset
open scoped BigOperators

/-- `hSieveC g ε` is multiplicative: the local factor at `p` depends only on `p`, so the product
over `primeFactors (m*n) = primeFactors m ∪ primeFactors n` (disjoint for coprime `m,n`) splits.
No nonvanishing hypothesis is needed: for coprime `m,n` one of them is `0` only if the other is
`1`, and then both sides reduce. -/
lemma hSieveC_mul (g : ℕ → ℝ) (ε : ℝ) {m n : ℕ} (h : m.Coprime n) :
    hSieveC g ε (m * n) = hSieveC g ε m * hSieveC g ε n := by
  simp only [hSieveC]
  rw [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]

/-- `hSieveC g ε n ≥ 0` whenever `g` is nonnegative: every local factor is nonnegative, since
`p^{-ε} > 0` for all real `ε` and `0 ≤ g p`. -/
lemma hSieveC_nonneg (g : ℕ → ℝ) (ε : ℝ) (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    0 ≤ hSieveC g ε n := by
  rw [hSieveC]
  refine Finset.prod_nonneg fun p hp => ?_
  have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have h1 : 0 < (p : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hp0 _
  have hnum : 0 < 1 + (p : ℝ) ^ (-ε) := by linarith
  have hden : 0 < 1 + (p : ℝ) ^ (-ε) * g p := by
    have := mul_nonneg h1.le (hg p)
    linarith
  exact div_nonneg hnum.le hden.le

/-- The sieve density `ν ↦ g̃(ν)·hSieveC g̃ ε ν` of the FI sequence `ã`: normalised at `1`,
multiplicative in `ν`, and nonnegative. -/
theorem sieveDens_mul_one_nonneg (ε : ℝ) :
    Submission.ASP.FIgtil 1 * Work.FIChain.hSieveC Submission.ASP.FIgtil ε 1 = 1 ∧
    (∀ m n : ℕ, Nat.Coprime m n →
      Submission.ASP.FIgtil (m * n) * Work.FIChain.hSieveC Submission.ASP.FIgtil ε (m * n)
        = (Submission.ASP.FIgtil m * Work.FIChain.hSieveC Submission.ASP.FIgtil ε m)
          * (Submission.ASP.FIgtil n * Work.FIChain.hSieveC Submission.ASP.FIgtil ε n)) ∧
    (∀ n : ℕ, 0 ≤ Submission.ASP.FIgtil n * Work.FIChain.hSieveC Submission.ASP.FIgtil ε n) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Submission.ASP.FIgtil_one, hSieveC]
    simp
  · intro m n hmn
    rw [Submission.ASP.FIgtil_mul hmn, hSieveC_mul _ _ hmn]
    ring
  · intro n
    exact mul_nonneg (Submission.ASP.FIgtil_nonneg n)
      (hSieveC_nonneg _ _ Submission.ASP.FIgtil_nonneg n)

end Work.FIChain
