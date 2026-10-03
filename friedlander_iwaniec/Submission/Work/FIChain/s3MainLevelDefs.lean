/-
# `Submission.Work.FIChain.s3MainLevelDefs` — the *level sum* of the `(1.7)`-main half

The companion's §8.3 route to `S*(x;y,z) ≪ A(x)(log x)^{-1}` reorganises
`Work.FIChain.s3MainPlus` as follows (see `NOTES_S3plusC_session12.md` §4):

1. un-merge the outer index (`ℓ = e·b`): the divisor weight `Σ_{b | ℓ, sy < b} μ b` becomes an
   *interval* sum over a fresh variable `b` (this is `sum_divisors_reindex`);
2. write `Ã(m₁) − Ã(m₂) = Σ_{m₂ < n ≤ m₁} ã(n)` (the counting function `Ã` is the sum of the
   nonnegative sequence `ã = atilc`), and swap the `n`-sum out of the `u`-integral.  For fixed
   `n` the conditions on `(e,b,d,u)` become

   * `b > sy`, `e·b·z ≤ x` (the support of the `λ⁺`-half),
   * `n ≤ e·b·sz`, `e·b·z < n`, `e·b·Cm·u < n`,
   * `1 ≤ u ≤ sz/Cm` and `d ≤ ⌊u⌋₊`.

The `b`-conditions are then *interval* conditions (a half-line intersection on
`b`), which is exactly what the sieve estimate `(2.4)` (`Work.FIChain.mu_gtil_interval_le`)
consumes: for fixed `(n,u,e,d)` the weight in `b` is `μ(b)·g̃(b)·(constant)` — the density
`g̃ = FIgtil` factorises because it is supported on squarefree numbers.

This module fixes the two definitions of that normal form:

* `s3LevelWindow x z sz Cm sy n u e` — the set of admissible `b`;
* `s3MainLevelSum lam x z sz Cm sy n` — the level sum `K(n)`.

The identity `s3MainPlus = Σ_{n ≤ x} ã(n)·K(n)` and the bound `|K(n)| ≤ C(log x)^{-1}` are the
two halves of the target (`s3MainPlus_pt_le`); they are stated in their own modules.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.s3RemPlus_defs
import Submission.Work.FIChain.S3plusC_route_defs

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The `b`-window of the level sum.**  For fixed `(n, u, e)` the admissible `b` are those with

* `sy < b` (the divisor cut of `S₃⁺`),
* `e·b·z ≤ x` (otherwise `S3plusInnerC` vanishes — `ℓ·z ≤ x`),
* `n ≤ e·b·sz` (`n` below the top of the `(1.7)`-block),
* `e·b·z < n` and `e·b·Cm·u < n` (`n` above the bottom of the block).

Each of these is a half-line in `b`, so for fixed `(n,u,e)` the window is an interval. -/
def s3LevelWindow (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) (u : ℝ) (e : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter (fun b =>
    sy < (b : ℝ) ∧ (e : ℝ) * (b : ℝ) * z ≤ (x : ℝ) ∧
      (n : ℝ) ≤ (e : ℝ) * (b : ℝ) * sz ∧ (e : ℝ) * (b : ℝ) * z < (n : ℝ) ∧
      (e : ℝ) * (b : ℝ) * (Cm : ℝ) * u < (n : ℝ))

lemma mem_s3LevelWindow {x : ℕ} {z sz : ℝ} {Cm : ℕ} {sy : ℝ} {n : ℕ} {u : ℝ} {e b : ℕ} :
    b ∈ s3LevelWindow x z sz Cm sy n u e ↔
      (1 ≤ b ∧ b ≤ x ∧ sy < (b : ℝ) ∧ (e : ℝ) * (b : ℝ) * z ≤ (x : ℝ) ∧
        (n : ℝ) ≤ (e : ℝ) * (b : ℝ) * sz ∧ (e : ℝ) * (b : ℝ) * z < (n : ℝ) ∧
        (e : ℝ) * (b : ℝ) * (Cm : ℝ) * u < (n : ℝ)) := by
  simp only [s3LevelWindow, Finset.mem_filter, Finset.mem_Icc]
  tauto

lemma s3LevelWindow_subset (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) (u : ℝ) (e : ℕ) :
    s3LevelWindow x z sz Cm sy n u e ⊆ Finset.Icc 1 x :=
  Finset.filter_subset _ _

/-- **The level sum** `K(n)`: the sum over `(e,b,d,u)` of the `gcd`-density weight
`μ(b)·ρ(e·b)·μ(d)·g̃(e·b·d)/u` restricted to the `b`-window of `s3LevelWindow` and to
`1 ≤ u ≤ sz/Cm`, `d ≤ ⌊u⌋₊`.

The target's two halves are `s3MainPlus = Σ_{n ≤ x} ã(n)·K(n)` and `|K(n)| ≤ C(log x)^{-1}`
for every `n ≤ x`. -/
def s3MainLevelSum (lam : ℕ → ℝ) (x : ℕ) (z sz : ℝ) (Cm : ℕ) (sy : ℝ) (n : ℕ) : ℝ :=
  ∫ u in (1 : ℝ)..(sz / (Cm : ℝ)), (1 / u) *
    (∑ e ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
      ∑ b ∈ s3LevelWindow x z sz Cm sy n u e,
        (ArithmeticFunction.moebius b : ℝ) * Submission.ASP.rhoOf lam (e * b) *
          (ArithmeticFunction.moebius d : ℝ) * Submission.ASP.FIgtil (e * b * d))

/-- `Σ_{n ≤ x} ã(n) = Ã(x)`: the counting function is the sum of the `ã` over `Icc 1 x`. -/
lemma sum_atilc_Icc_eq (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, atilc n = AcountAtilC x := by
  rw [AcountAtilC, Work.FITop.AcountAtil, Submission.ASP.Acount, Nat.floor_natCast]

end

end Work.FIChain
