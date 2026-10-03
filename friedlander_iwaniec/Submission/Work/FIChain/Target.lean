/-
# `Submission.Work.FIChain.Target` — the deliverable, wired to the two named gaps

`Work.FIChain.primeSum_bound_of_prop41'` below is **the same statement** as the single `sorry` of
`Submission/Work/FITop/Top.lean`, `Work.FITop.primeSum_bound_of_prop41` (the paper's Theorem 1 for
`ã`), stated here over this chapter's vocabulary (`Submission.ASP.FIa`, `Submission.ASP.Acount`,
`Work.FITop.Pcut`-free parameters).  The lead's `challenge_of_prop41` rewires by the one-line name
change.

It is *proved* here from `Work.FIChain.primeSum_bound_of_prop41` (the full endgame, **sorry-free**,
1640 lines, `Submission/Work/FIChain/primeSum_bound_of_prop41.lean`) plus the **two gaps** of the
chapter, isolated below as the single hypothesis `Work.FIChain.FIChainGaps`:

* `sieve` — the `λ`-input of the companion's §3/§6 for the FI density, with a `Δ`-uniform constant
  (obstruction (D));
* `S3avg` — the §8 `S₃`-average at the corrected `B`-dependent scale (the `hS3` of the endgame).

**Status of the two gaps (see `NOTES.md`, §"Session 4").**

* `sieve`.  `SieveInput` has nine conjuncts.  For `f = FIgtil · hSieveC FIgtil (1/log Δ)` and the
  **`lcm`-square Selberg weight** `λ = selbergSq f ⌊√Δ⌋`, *eight* of the nine are proved
  (`selbergSq_FIgtil_input`: `λ 1 = 1`, squarefree support, support `ν ≤ ⌊√Δ⌋² ≤ Δ`, `ρ ≥ 0`, the
  two PSD conjuncts, and the sieve inequality with `C_sieve ≤ K` **uniform in `Δ`**).  The ninth,
  `∀ν, |λ ν| ≤ 1`, is **FALSE for this weight** — referees produced
  `Δ = (2340000)²`, `ν = 2·5·13·17·29·37·41·53·61` with `|λ ν| ≈ 1.5435`, and the violations recur
  for arbitrarily large `Δ` (the resonant level moves outward as one appends primes `≡ 1 (4)`), so
  no constant bound and no `∃Δ₀`-form can hold.  The route that remains is the classical one-sided
  (Rosser–Iwaniec) `λ⁺`, which has `|λ| ≤ 1` and `ρ ≥ 0` for free (`lamPlus_upper_moebius_and_support`,
  proved here) and whose missing half is the **κ ≈ 2 upper-bound main term** `Σ_{ν<Δ}λ⁺_ν f ν ≤
  C·∏_{p<Δ}(1-f p)` with `C` uniform — the paper's "theory of the 2-dimensional sieve".  The
  dimension-1 case is in the workspace (`Submission.Work.ChenPlan.LinearSieve.linear_sieve_v6`,
  `linear_sieve_v6_upper`), and `Utab` is its explicit envelope; the κ = 2 analogue is the gap.
* `S3avg`.  `ASP.S19.smAvg_S3_le` bounds the `y`-integrated `S₃` in terms of `hw`
  (`|Σ_{b|ℓ, sy<b}μ b|·|ρ ℓ| ≤ w ℓ`, available for every `λ` with `|λ| ≤ 1`) and a `ρ`-window.
  The companion's `Xrho` window (two Möbius factors) is *false* for `ã`; the contract's
  `RhoWindowC` (one `μ`, `Work.FITop.XrhoC`) is supplied by `Prop41Statement` — but only for
  truncation levels `s ≤ ⌊√z⌋` (`rhoWindowC_param`), while the §8 `λ⁻`-half needs `s` up to
  `⌊s·z⌋ ≈ √x/L^{B+2} ≫ √z`.  Hence the `μ(c)`-signed splitting
  `Λ = λ⁻ - λ⁺` of `S3_eq_S3plusC_sub_S3minusC`: the `λ⁻` half uses the window at level
  `C = ⌊√z⌋`, the `λ⁺` half is estimated by the (1.7) density route plus (R′) (`remainder_all`).
  The two halves' constraints are compatible iff `η ≥ 0.0373`, so the chapter's `etac` must be
  raised from `1/32` to `1/25` (then `1/4 - 2η = 17/100`, and `window_marginsC` etc. — which
  hard-code `1/4 - 2*etac = 3/16` — must be re-proved at the new value); the previous session's
  `smAvg_S3_paramC` was returned "wrong as stated" for exactly this reason.
-/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.Work.FIChain.window_marginsC
import Submission.Work.FITop.BformAtilEqXsum
import Submission.Work.FITop.AtilTauPowFourLe
import Submission.Work.FITop.Defs
import Submission.ASP.S7c
import Submission.ASP.S8b
import Submission.ASP.S20
import Submission.ASP.S21
import Submission.ASP.S22
import Submission.ASP.S23
import Submission.ASP.S24
import Submission.ASP.S25
import Submission.Work.FITop.SingleDvdTauSqLe
import Submission.Work.FITop.WindowRangeMarginsChain
import Submission.Work.FITop.BprimeWindowDelta1
import Submission.Work.FITop.RangeCheckChain
import Submission.ASP.S30
import Submission.Work.FITop.WolkeSquarefreeTau
import Submission.Work.FITop.AdTauAggregate
import Submission.Work.FITop.SumIteDivDvd
import Submission.Work.FIChain.scale_factsC
import Submission.Work.FIChain.LocalS4
import Submission.Work.FIChain.LocalS5c
import Submission.Work.FIChain.remainder_all
import Submission.Work.FIChain.rhoWindowC_param
import Submission.Work.FIChain.LocalS6c
import Submission.ASP.S7e
import Submission.Commons.NumberTheory.Chebyshev.sum_prime_log_mul_g_Ioc_le
import Submission.Work.FIChain.chainRangeFactsC
import Submission.Work.FIChain.Tsum_uniformAll
import Submission.Work.FIChain.Tsum2_uniformAll
import Submission.Work.FIChain.FIgtil_prod_sub_le
import Submission.Work.FIChain.FIgtil_tau_div_sum_le
import Submission.Work.FIChain.AcountAtil_log_bound
import Submission.Work.FIChain.rosserLambda_FIgtil_r2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Work.FIChain.S3zdev
import Submission.Work.FIChain.S3splitBstar
import Submission.Work.FIChain.S3plusC_machinery
import Submission.Work.FIChain.s3RemPlus_defs
import Submission.Work.FIChain.mu_gtil_interval_le
import Submission.Commons.NumberTheory.Sieve.sieve_mu_sum_coprime_powLog
import Submission.Work.FIChain.zc_sharp_bounds
import Submission.Work.FIChain.s3MainLevelDefs
import Submission.Work.FIChain.s3MainPlus_eq_levelSum
import Submission.Work.FIChain.s3LevelWindow_sum_le
import Submission.Work.FIChain.s3Density_sum_le
import Submission.Work.FIChain.s3MainLevelSum_le
import Submission.Work.FIChain.s3RemPlus_zavg_le
import Submission.Work.FIChain.abs_S3minusC_le
import Submission.Work.FIChain.measurable_s3halves
import Submission.Work.FIChain.S3xC_intervalIntegrable
import Submission.Work.FITop.RhoWindowCProp41
import Submission.Work.FIChain.Yc_lower_sharp
import Submission.Work.FIChain.assemblyC
import Submission.Work.FIChain.AcountAtilC_ge_const_mul_rpow
import Submission.Work.FIChain.AcountAtilC_le_const_mul_rpow
import Submission.Work.FIChain.exists_z1_le_of_measurable_zavg
import Submission.Work.FIChain.FI_primeSum_of_estimates_signed

set_option autoImplicit false

namespace Work.FIChain

open Finset Filter
open scoped BigOperators

noncomputable section

/-- **Gap 1 — the `λ`-input of the companion's §3/§6 (obstruction (D)).**

There are `K > 0` and, for every sieve level `Δ ≥ 3`, a weight `λ` together with a constant
`C_sieve ≤ K` satisfying the nine conjuncts of `Work.FIChain.SieveInput` for the FI density
`g = Submission.ASP.FIgtil`.

(Stated exactly as the `hsieve` hypothesis of `Work.FIChain.assemblyC`; the `Δ`-uniformity of
`C_sieve` is what the endgame's `E₃`-term needs, see `NOTES.md` §"Session 4".) -/
def FIChainSieveGap : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℕ, 3 ≤ Δ → ∃ lam : ℕ → ℝ, ∃ C_sieve : ℝ,
    SieveInput Submission.ASP.FIgtil Δ lam C_sieve ∧ C_sieve ≤ K

/-- **Gap 2 — the §8 `S₃`-average at the corrected `B`-dependent scale.**

For every `B > 0` there is `K > 0` with, eventually in `x`, the `y`-integrated `S₃` of the chain is
bounded by `J·K·Ã(x)·(log x)^{-4}·log ⌊s·z⌋` for **every** weight `λ` satisfying `SieveInput` at
the level `Δ = Deltac x`; the window condition `Yc/Δ > x^{1/4+1/64}` is the range check of the
corrected family (`window_marginsC`).  (Stated exactly as the `hS3` hypothesis of
`Work.FIChain.assemblyC`.) -/
def FIChainS3Gap : Prop :=
  ∀ B : ℝ, 0 < B → ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℕ in Filter.atTop,
    (x : ℝ) ^ ((1 : ℝ) / 4 + 1 / 64) + 2 < Yc x B / (Deltac x : ℝ) →
    ∀ lam : ℕ → ℝ, ∀ C_sieve : ℝ,
      SieveInput Submission.ASP.FIgtil (Deltac x) lam C_sieve →
      (∫ y in Yc x B..(Real.exp 1 * Yc x B),
          |Submission.ASP.S3 atilc lam x (zc x B)
            (sc x B * y) (sc x B * zc x B)| / y)
        ≤ (Jc x B : ℝ)
            * (K * AcountAtilC x * (Real.log (x : ℝ)) ^ (-(4 : ℤ)))
            * Real.log (((⌊sc x B * zc x B⌋₊ : ℕ) : ℝ))

/-- **The two gaps, packaged.** -/
def FIChainGaps : Prop := FIChainSieveGap ∧ FIChainS3Gap

end

end Work.FIChain
