/-
# `Work.FIChain.sieveDens_le_one_sub`

The §6 one-prime sieve density `ν ↦ g̃(ν)·hSieveC g̃ ε ν` is *uniformly bounded away from `1`*,
uniformly in the sieve parameter `ε ≥ 0`:

    ∃ δ > 0, ∀ ε ≥ 0, ∀ p prime,   g̃(p) · hSieveC g̃ ε p ≤ 1 − δ,

with `g̃ = Submission.ASP.FIgtil` the (squarefree-supported) density of `ã = atil FIa` and

    hSieveC g ε ν = ∏_{p ∣ ν} (1 + p^{-ε}) / (1 + p^{-ε} · g p)

the `h(ν)` of the companion paper's §6.

## The mathematics

For a prime `p`, `hSieveC g̃ ε p = (1 + t)/(1 + t·g̃(p))` with `t = p^{-ε} ∈ (0,1]` (as `p ≥ 1`
and `ε ≥ 0`).  The one-variable function

    f(t) = g̃(1 + t)/(1 + g̃ t)

is nondecreasing on `[0,1]` whenever `0 ≤ g̃ ≤ 1`, because

    f(1) − f(t) ∝ g̃·(1 − g̃)·(1 − t) ≥ 0.

Hence it suffices to dominate `g̃(p)` by a constant `< 1` uniformly in `p`.  Two elementary
ingredients give `g̃(p) ≤ 2/3`:

* `g̃(p) ≤ g(p)`:  `g̃(p) = (g(p) − g(p²))/(1 − g(p²)) ≤ g(p)` because `g(p²) ≥ 0` and `g(p) ≤ 1`
  (formally, the difference `g(p) − g̃(p) = g(p²)(1 − g(p))/(1 − g(p²)) ≥ 0`);
* `g(p) ≤ 2/3` (all primes `p`):  `g(2) = N(2)/4 = 1/2` and for `p ≥ 3` the classical bound
  `g(p)·p ≤ 2` of `Submission.gdens_prime_mul_le` gives `g(p) ≤ 2/p ≤ 2/3`.

With `g̃(p) ≤ 2/3` one gets `f(t) ≤ f(1) = 2g̃/(1 + g̃) ≤ 2·(2/3)/(5/3) = 4/5 = 1 − 1/5`, and
δ = 1/5 does the job.  (The constants are far from optimal: any δ < 1/3 would also work, since
`g̃(p) ≤ 1/2`.)

Everything below is `sorry`-free.
-/
import Mathlib
import Submission.Work.FIChain.Defs

set_option autoImplicit false

namespace Work.FIChain

open Finset
open scoped BigOperators

/-! ## 1. The local density at a prime is at most `2/3` -/

/-- `g(p) ≤ 2/3` for every prime `p`.  For `p = 2` this is `g(2) = N(2)/4 = 1/2`; for `p ≥ 3` it
follows from the classical bound `g(p)·p ≤ 2`. -/
lemma sieveDens_FIg_prime_le_two_thirds {p : ℕ} (hp : p.Prime) :
    Submission.ASP.FIg p ≤ 2 / 3 := by
  by_cases h2 : p = 2
  · subst h2
    simp only [Submission.ASP.FIg, Submission.gdens, Submission.N_prime_two]
    norm_num
  · have hp2 : 2 ≤ p := hp.two_le
    have hp3 : 3 ≤ p := by omega
    have hb : Submission.gdens p * (p : ℚ) ≤ 2 := Submission.gdens_prime_mul_le hp
    have hbR : ((Submission.gdens p : ℚ) : ℝ) * (p : ℝ) ≤ 2 := by
      exact_mod_cast hb
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hle : Submission.ASP.FIg p ≤ 2 / (p : ℝ) := by
      rw [Submission.ASP.FIg]
      rw [le_div_iff₀ hp0]
      linarith
    have hp3R : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    have h2p : (2 : ℝ) / (p : ℝ) ≤ 2 / 3 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith

/-- `g̃(p) ≤ 2/3` for every prime `p`: `g̃(p) ≤ g(p)` (the correction `g(p) − g̃(p)` is
nonnegative) and `g(p) ≤ 2/3`. -/
lemma sieveDens_FIgtil_prime_le_two_thirds {p : ℕ} (hp : p.Prime) :
    Submission.ASP.FIgtil p ≤ 2 / 3 := by
  rw [Submission.ASP.FIgtil_prime hp, Submission.ASP.gtilVal]
  have h0 : 0 ≤ Submission.ASP.FIg (p ^ 2) := Submission.ASP.FIg_nonneg _
  have h1 : Submission.ASP.FIg p ≤ 2 / 3 := sieveDens_FIg_prime_le_two_thirds hp
  have hle : Submission.ASP.FIg (p ^ 2) ≤ Submission.ASP.FIg p :=
    (Submission.ASP.FI_gdens_prime_sq_le p hp).1
  have hden : (0 : ℝ) < 1 - Submission.ASP.FIg (p ^ 2) := by linarith
  rw [div_le_iff₀ hden]
  nlinarith [h0, h1]

/-! ## 2. The one-prime sieve factor -/

/-- At a prime, `hSieveC g ε` is the single Euler factor `(1 + p^{-ε})/(1 + p^{-ε}·g p)`. -/
lemma hSieveC_prime (g : ℕ → ℝ) (ε : ℝ) {p : ℕ} (hp : p.Prime) :
    hSieveC g ε p = (1 + (p : ℝ) ^ (-ε)) / (1 + (p : ℝ) ^ (-ε) * g p) := by
  rw [hSieveC, hp.primeFactors, Finset.prod_singleton]

/-- **The one-prime bound**: for `0 ≤ g ≤ 2/3` and `0 < t ≤ 1`,

    g · (1 + t)/(1 + g·t) ≤ 4/5 = 1 − 1/5.

Indeed the left side is `≤ 2g/(1+g)` (the function `t ↦ g(1+t)/(1+gt)` is nondecreasing, since
`2g/(1+g) − g(1+t)/(1+gt) = g(1−g)(1−t)/((1+g)(1+gt)) ≥ 0`), and `2g/(1+g) ≤ 4/5 ⟺ g ≤ 2/3`. -/
lemma one_prime_factor_le (g t : ℝ) (hg0 : 0 ≤ g) (hg : g ≤ 2 / 3) (ht0 : 0 < t)
    (ht1 : t ≤ 1) : g * ((1 + t) / (1 + t * g)) ≤ 1 - 1 / 5 := by
  have hden : 0 < 1 + t * g := by nlinarith
  have h4 : (0 : ℝ) ≤ (1 - g) * (1 - t) := mul_nonneg (by linarith) (by linarith)
  have h2 : g * (1 + t) / (1 + t * g) ≤ 2 * g / (1 + g) := by
    rw [div_le_div_iff₀ hden (by linarith)]
    nlinarith [h4]
  have h3 : 2 * g / (1 + g) ≤ 4 / 5 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + g)]
    linarith
  rw [← mul_div_assoc]
  linarith

/-! ## 3. The main statement -/

theorem sieveDens_le_one_sub :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : ℝ), 0 ≤ ε → ∀ p : ℕ, p.Prime →
      Submission.ASP.FIgtil p * Work.FIChain.hSieveC Submission.ASP.FIgtil ε p ≤ 1 - δ := by
  refine ⟨1 / 5, by norm_num, fun ε hε p hp => ?_⟩
  rw [hSieveC_prime _ _ hp]
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have ht0 : 0 < (p : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _
  have ht1 : (p : ℝ) ^ (-ε) ≤ 1 := by
    calc (p : ℝ) ^ (-ε) ≤ (p : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
      _ = 1 := Real.rpow_zero _
  exact one_prime_factor_le _ _ (Submission.ASP.FIgtil_nonneg p)
    (sieveDens_FIgtil_prime_le_two_thirds hp) ht0 ht1

end Work.FIChain
