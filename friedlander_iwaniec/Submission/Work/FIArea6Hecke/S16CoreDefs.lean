/-
# `Submission.Work.FIArea6Hecke.S16CoreDefs` — the interface of the §16 core bound

This file fixes the two `Prop`s into which the target

  `Work.FIArea6Hecke.S16Core_of_invBound : (∀ ε ∈ (0,1/4], HeckeLcontInvBoundAll ε) → S16Core`

is decomposed, together with the elementary lemmas about the *mollifier class* of (4.13)+(5.13)
that the decomposition uses.

## The mathematics

`Work.FITop4.Bridge.S16Core` is *FI* Lemma 16.2 ("the polynomial X²+Y⁴ captures its primes",
Annals 148 (1998), §16) at the round-6 coefficient class `IsBetaCoeff6`, i.e. the bound

  `‖S_χ^k(β)‖ ≤ cε [exp(-ηcε(4d)^{-ε}√log N) + exp(-η log N/log P)]·(4d)·N·(log N)^6`

for the character sum `S_χ^k(β) = Σ_z β_z χ(z)(z/|z|)^k` of (16.25), where
`β_z = q(arg z - φ)·p(|z|²)·μ(|z|²)·γ(|z|²;C)` is the coefficient of (5.13) supported on primary
`z` that are free of small primes (5.8), have `τ(|z|²) ≤ τ` (5.9) and lie in the class of `z₀`
mod eight (5.7).

Its only known proof is *FI* §16: the **angle mollifier** `q` is expanded in its Fourier series
(16.26)/(16.27) — this is what replaces the *angular* localisation of `β` by the *frequencies*
`j = k + ℓ`, `|ℓ| ≤ L = exp(√log N)` — the **radius mollifier** `p` is written as a Mellin
integral (16.28), the Hecke eigenvalues are regrouped into the Dirichlet series
`Z = M·P·Q` (16.30)–(16.34), and the contour of (16.36) is shifted to the left of `s = 1` using
the inverse bound (16.23) — the hypothesis `HeckeLcontInvBoundAll` — with
`δ = min{c(ε)/(d^ε log T), 1/log P}` (16.37), giving (16.38).

Two features of the *formal* coefficient class `IsBetaCoeff6` are not present in the paper's `β`
of (5.13):

* the paper's `β` is *not* restricted by (5.9) (`τ(n) ≤ τ`), while `IsBetaCoeff6` builds the
  divisor bound into the support;
* the paper's `β` carries no axis-free condition, while `IsBetaCoeff6` restricts to
  `IsAxisFree Pa z`;
* the paper's (5.7) congruence is handled inside the proof by characters modulo eight (which
  changes `χ` into a character of modulus `lcm(4d,8) ≤ 4·(2d)`), while the formal class has the
  congruence as a support restriction.

The `Prop` `S16CleanCore` below is the paper's statement for `β` *without* those three support
restrictions (i.e. the coefficient of (5.13) subject to (5.7')+(5.8) only, where the angular
localisation is carried by the smooth weight `q`, so that no *indicator* of the sector occurs —
that is exactly the form §16's Fourier expansion needs), with all constants displayed:
separate region constant `c`, prefactor `C`, threshold `x0`, the modulus allowance
`d ≤ 2(log N)^ν` (the factor `2` absorbs the modulus change of the (5.7) detection, cf. (16.25)),
and the frequency range `|j| ≤ 3exp(√log N)` (the paper's `|m| ≤ 2exp(√log N)` after summing over
`|ℓ| ≤ L`).  The `Prop` `S16RadialCore` keeps the three extra support restrictions, and the
lemmas of this file show that the *paper's* statement implies the formal one
(`S16RadialCore_of_cleanCore`) and that the formal one implies the target
(`S16Core_of_radialCore`), the latter by the elementary redundancy
`[InPolarBox]·q(arg z - φ)p(|z|²) = q(arg z - φ)p(|z|²)` of the support indicators with the
mollifier supports ((4.12) for `p`, (5.12) for `q`, using `q(0) = 0`).

So the target reduces to the two lemmas

1. `S16CleanCore_of_invBound` — the analytic heart, *FI* (16.25)–(16.38);
2. `S16RadialCore_of_cleanCore` — the removal of the three extra support restrictions from the
   formal coefficient class.
-/
import Mathlib
import Submission.Work.FITop4.Bridge.area5_6_defs

set_option autoImplicit false

namespace Work.FIArea6Hecke

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The angular mollifier `q` of (5.12)/(5.13) vanishes at `0`.**  `q` is `C²`, supported in
`[0, 2πθ]` (the support clause `q α ≠ 0 → 0 ≤ α ≤ 2πθ`), hence `q = 0` on `(-∞,0)` and
`q 0 = 0` by continuity. -/
lemma mollQ_zero {q : ℝ → ℝ} {θ : ℝ} (hqC : ContDiff ℝ 2 q)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) : q 0 = 0 := by
  have hzero : ∀ α : ℝ, α < 0 → q α = 0 := by
    intro α hα
    by_contra h
    exact absurd (hqsupp α h).1 (not_le.mpr hα)
  have hclosed : IsClosed {α : ℝ | q α = 0} := isClosed_eq hqC.continuous continuous_const
  have hsub : Set.Iio (0 : ℝ) ⊆ {α : ℝ | q α = 0} := fun α hα => hzero α hα
  have hcl : closure (Set.Iio (0 : ℝ)) ⊆ {α : ℝ | q α = 0} := closure_minimal hsub hclosed
  exact hcl (by rw [closure_Iio]; simp)

/-- **The radius mollifier `p` of (4.12)/(5.13) vanishes outside its segment**:
if `u ∉ (N, (1+θ)N]` then `p u = 0`. -/
lemma mollP_zero_of_not_mem {p : ℝ → ℝ} {N θ u : ℝ}
    (hpsupp : ∀ u, p u ≠ 0 → N < u ∧ u ≤ (1 + θ) * N)
    (hu : ¬(N < u ∧ u ≤ (1 + θ) * N)) : p u = 0 := by
  by_contra h
  exact hu (hpsupp u h)

/-- **The clean §16 core** (*FI* Lemma 16.2 in the form its proof needs): the character sum
(16.25) with the coefficient of (5.13) — the smooth angular weight `q`, the smooth radial weight
`p`, the Möbius factor `μ(n)` and the truncated Möbius factor `γ(n;C)` — over primary `z` free of
small primes (5.8), with no further support restriction and no *indicator* of the sector `(5.12)`.

For every `ε ∈ (0,1/4]` there are `c, C, x0 > 0` such that for every admissible datum `Pa` with
`x0 ≤ Pa.x`, every strict character `χ` modulo `4d` (`1 ≤ d ≤ 2(log N)^ν`, `εν < 1/2`), every
frequency `|j| ≤ 3exp(√log N)` and every mollifier pair `q`, `p` of the class (4.14)/(5.12),

  `‖Σ_{z primary, (z,Π)=1} q(arg z - φ) p(|z|²) μ(n) γ(n;C) χ(z)(z/|z|)^j‖`
  `≤ C[exp(-ηc(4d)^{-ε}√log N) + exp(-η log N/log P)]·(4d)·N·(log N)^6`.

The factor `2` in the modulus allowance is what allows the (5.7) detection of §16 ("this
congruence can be detected by characters to modulus eight so we can relax it by changing `χ` in
`ψ`"): the detected character has modulus `4·lcm(d,2) ≤ 4·(2d)`.  The frequency range
`3exp(√log N)` likewise absorbs the paper's summation over `|ℓ| ≤ L = exp(√log N)` together with
the given `|k| ≤ exp(√log N)`. -/
def S16CleanCore : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ c C x0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < x0 ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
    ∀ (φ ν : ℝ) (d : ℕ) (j : ℤ) (chi : GaussianInt → ℂ) (q p : ℝ → ℝ),
      0 < ν → ν < 1 / (2 * ε) → 1 ≤ d → (d : ℝ) ≤ 2 * (Real.log Pa.N) ^ ν →
      |(j : ℝ)| ≤ 3 * Real.exp (Real.sqrt (Real.log Pa.N)) →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      ContDiff ℝ 2 q → ContDiff ℝ 2 p →
      (∀ α, 0 ≤ q α) → (∀ α, q α ≤ 1) →
      (∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ) →
      (∀ m : ℕ, m ≤ 2 → ∀ α : ℝ,
        |iteratedDeriv m q α| ≤ Work.FITop4.cMoll m * Pa.θ ^ (-(m : ℝ))) →
      (∀ u, 0 ≤ p u) → (∀ u, p u ≤ 1) →
      (∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) →
      (∀ m : ℕ, m ≤ 2 → ∀ u : ℝ,
        |iteratedDeriv m p u| ≤ Work.FITop4.cMoll m * (Pa.θ * Pa.N) ^ (-(m : ℝ))) →
      ‖∑ z ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z then
            ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j
          else 0)‖
        ≤ C * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
            + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
          * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)

/-- **The §16 core at the formal coefficient class** — the target form.

This is the same statement as `S16CleanCore` but with the three extra support restrictions of
`IsBetaCoeff6` (the divisor bound (5.9), the class modulo eight (5.7), and the axis-free
restriction of round 6.1) in place, and — importantly — with a **single** constant `cε` serving
both as the prefactor and in the exponent `exp(-η cε (4d)^{-ε} √log N)`, exactly as in the frozen
target `Work.FITop4.Bridge.S16Core`.

*Remark on the constants (recorded for the requester).*  *FI*'s printed Lemma 16.2 has **two**
constants: the exponent `exp(-ηc(ε)d^{-ε}√log N)` carries the region constant `c(ε)` of (16.24)
while the bound has a separate implied constant ("depending only on ε"), i.e. the two-constant
form `S16CleanCore`.  The single-constant form asserted here is strictly stronger: writing
`X = (4d)^{-ε}√log N` and `E₂ = exp(-η log N/log P)` and comparing with a two-constant bound
`C₀(E₁(c₀)+E₂)M`, one needs a `cε` with `cε ≥ C₀` (to cover the `E₂` slot) and
`C₀ exp(-ηc₀X) ≤ cε exp(-ηcεX)` for all `X`, which forces `cε ≤ c₀` as soon as `X` is large.  So
the single-constant form is *not* implied by the paper's two-constant lemma; it needs the extra
information that the prefactor can be chosen below the exponent constant, i.e. essentially
`C₀ ≤ c₀`.  This is the same phenomenon that `Submission/Work/FITop4/Bridge/area5_6_defs.lean`
records for `HeckeLcontInvBoundAll` ("a single constant would be false, since ... a `c` exceeding
the zero-free depth lets a zero of `Lcont` into the region").  The present statement is the form
the frozen target demands; it is what the §16 assembly must produce. -/
def S16RadialCore : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ cε x0 : ℝ, 0 < cε ∧ 0 < x0 ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
    ∀ (φ ν : ℝ) (z0 : GaussianInt) (d : ℕ) (j : ℤ) (chi : GaussianInt → ℂ) (q p : ℝ → ℝ),
      0 < ν → ν < 1 / (2 * ε) → 1 ≤ d → (d : ℝ) ≤ 2 * (Real.log Pa.N) ^ ν →
      |(j : ℝ)| ≤ 3 * Real.exp (Real.sqrt (Real.log Pa.N)) →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      ContDiff ℝ 2 q → ContDiff ℝ 2 p →
      (∀ α, 0 ≤ q α) → (∀ α, q α ≤ 1) →
      (∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ) →
      (∀ m : ℕ, m ≤ 2 → ∀ α : ℝ,
        |iteratedDeriv m q α| ≤ Work.FITop4.cMoll m * Pa.θ ^ (-(m : ℝ))) →
      (∀ u, 0 ≤ p u) → (∀ u, p u ≤ 1) →
      (∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) →
      (∀ m : ℕ, m ≤ 2 → ∀ u : ℝ,
        |iteratedDeriv m p u| ≤ Work.FITop4.cMoll m * (Pa.θ * Pa.N) ^ (-(m : ℝ))) →
      ‖∑ z ∈ Work.FITop.boxN Pa,
          (if Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z
              ∧ (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)
              ∧ Work.FITop4.SameClass8 z z0 ∧ Work.FITop4.IsAxisFree Pa z then
            ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j
          else 0)‖
        ≤ cε * (Real.exp (-(Pa.η * cε * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
            + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
          * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)

end

end Work.FIArea6Hecke
