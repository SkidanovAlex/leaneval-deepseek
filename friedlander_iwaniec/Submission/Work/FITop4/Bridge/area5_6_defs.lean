import Mathlib
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.LcontDefs

/-!
# `Submission.Work.FITop4.Bridge.area5_6_defs` — the interface of the round-6 bridge

Vocabulary used by the bridge `Work.FITop4.Bridge.area5_6` (and by the two lemmas it is assembled
from, `Work.FIArea6Hecke.S16Core_of_invBound` and `Work.FIArea6Hecke.area5_6_of_S16Core`):
`IsBetaSupp` (the (4.13)+(5.13) coefficient with an arbitrary support restriction), `S16Core`
(*FI* Lemma 16.2 at the *strict* characters of modulus `4d`, arbitrary support) and
`HeckeInvBoundAll` (its analytic input, *FI* (16.23) for strict characters).

`Area5_6` (`Submission/Work/FITop4/Areas6.lean`) is *FI* Lemma 16.2 at the round-6 hypotheses: the
round-4 area-5 conclusion with (i) the threshold `∃ x₀, x₀ ≤ Pa.x` and (ii) `IsBetaCoeff6` in place
of `IsBetaCoeff` (the (4.13)/(5.13) coefficient with the (5.7) restriction `z ≡ z₀ (mod 8)` built
into its support).

## What is in this file

The *interface* that the round-4 §16 argument transfers along:

* `IsBetaSupp Pa φ S β` — the coefficient of (4.13)+(5.13) with the **support further restricted to
  an arbitrary set `S`**; the round-4 `IsBetaCoeff` is the case `S = univ`, `IsBetaCoeff6` is the
  case `S = {z | z ≡ z₀ (mod 8)}` (`IsBetaCoeff6.toSupp`), and the *port* of the round-4 §16
  argument to the round-6 support is exactly the passage from `S = univ` to a general `S`.  The §16
  argument never asks *which* `S` is; it uses `q`, `p`, `μ`, `γ` and the box conditions only.
* `S16Core` — *FI* Lemma 16.2 at the *strict primitive* characters (the class for which the Hecke
  `L`-function of `ℚ(i)` and its theta series are defined in `FIArea5/S16Hecke`), with the support
  generalised to an arbitrary `S`.  This is the only analytic input; everything else
  (`strict primitive → arbitrary character`, the bookkeeping of the constants, the threshold) is
  formal.
* `area5_6` — the target, assembled from `S16Core` and the Hecke inverse bound (16.23).

The three ingredients are stated in the *same shape* as the target (a single existential constant
`cε` appearing both in the exponential and as the implied constant, plus the threshold `x₀`), so the
assembly is pure bookkeeping:

1. `Work.FIArea6Hecke.heckeInvBound_all : ∀ ε ∈ (0,1/4], HeckeInvBound ε` — the Hecke `L`-function
   inverse bound (16.23)/(16.24) (*FI* §16, stages 1–3);
2. `Submission.Work.FIArea6Hecke.s16Core_of_invBound` — the §16 assembly (16.25)–(16.38)
   (Fourier truncation of `q`, Mellin inversion of `p`, `Z = M·P·Q`, the contour shift `δ`),
   giving `S16Core` from 1.;
3. `Submission.Work.FIArea6Hecke.area5_6_of_s16Core : S16Core → Area5_6` — the reduction from
   strict primitive characters to an arbitrary `IsCharMod4d` character (the conductor/primitive
   part of a character of `(ℤ[i]/4d)^*`, the correction terms off the units being sums of the *same*
   restricted-support shape, hence covered by `S16Core`), plus the bookkeeping of `cε`.

The threshold `∃ x₀` is what makes step 3's bookkeeping work: the `exp(-η log N/log Pz)` term is
never smaller than `exp(-η c (4d)^{-ε}√log N)` for `x ≥ x₀` (because `log Pz ≥ (loglog x)²` and
`(4d)^{-ε}√log N ≫ log N/log Pz`), so the exponential slots may be filled at the holder's
convenience and only the prefactor/constant comparison remains.
-/

set_option autoImplicit false

namespace Work.FITop4.Bridge

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The coefficient of (4.13)+(5.13) with an arbitrary support restriction.**  There are fixed
mollifiers `q`, `p` of the round-4 `C²` class with

  `β_z = q(arg z − φ)·p(|z|²)·μ(|z|²)·γ(|z|²;C)`

for `z` in the polar box (5.14) that is free of small primes (5.8), has `τ(|z|²) ≤ τ` (5.9) **and
lies in `S`**, and `β_z = 0` otherwise.

`IsBetaSupp Pa φ {z | z ≡ z₀ (mod 8)} β` is `IsBetaCoeff6 Pa φ z₀ β` (`IsBetaCoeff6.toSupp`).

**Warning (machine-found, do not use as a hypothesis).**  `IsBetaSupp` at an *arbitrary* set `S` is
NOT a legitimate interface for the §16 bound: the bound is false for it.  Taking
`S = {z | μ(|z|²) = −1}` together with a coefficient whose Möbius factor survives the truncation
(`C = 1`, so `γ ≡ 1`) makes every summand one-signed, `β_z χ(z)(z/|z|)^k = −q(α_z)p(|z|²) ≤ 0`, and
the sum's size is then `≍ θ²N/log P`, which exceeds the claimed
`cε(exp(−ηcε(4d)^{−ε}√log N) + exp(−η log N/log P))·(4d)N(log N)^6` (the first exponential is
`≍ exp(−c√log N) ≫ (log x)^{−2A'}`).  The §16 cancellation lives in the *sign pattern of
`μ(n)γ(n)` over the whole support*, so a support that is not sign-neutral destroys it.  What *is*
neutral is the (5.7) congruence `z ≡ z₀ (mod 8)` (the paper's remark after (16.25): it "can be
detected by characters to modulus eight so we can relax it by changing `χ` in `ψ`"): that is why the
round-6 hypothesis is used *as a whole* in `S16Core` below and not weakened to `IsBetaSupp`. -/
def IsBetaSupp (Pa : Work.FITop.Params) (φ : ℝ) (S : Set GaussianInt)
    (β : GaussianInt → ℂ) : Prop :=
  ∃ q p : ℝ → ℝ,
    ContDiff ℝ 2 q ∧ ContDiff ℝ 2 p ∧
    (∀ α, 0 ≤ q α) ∧ (∀ α, q α ≤ 1) ∧
    (∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ) ∧
    (∀ j : ℕ, j ≤ 2 → ∀ α : ℝ, |iteratedDeriv j q α| ≤ cMoll j * Pa.θ ^ (-(j : ℝ))) ∧
    (∀ u, 0 ≤ p u) ∧ (∀ u, p u ≤ 1) ∧
    (∀ u, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N) ∧
    (∀ j : ℕ, j ≤ 2 → ∀ u : ℝ,
      |iteratedDeriv j p u| ≤ cMoll j * (Pa.θ * Pa.N) ^ (-(j : ℝ))) ∧
    (∀ z : GaussianInt, β z =
      (if InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
          (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ z ∈ S
          ∧ IsAxisFree Pa z
       then ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
       else 0))

/-- **`IsBetaCoeff6` is `IsBetaSupp` at the class of `z₀` modulo eight**: the round-6 hypothesis is
the round-4 one at the support `S = {z | z ≡ z₀ (mod 8)}` (the (5.7) congruence `z ≡ z₀ (mod 8)` of
`IsBetaCoeff6` is literally `z ∈ S`). -/
theorem IsBetaCoeff6.toSupp {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (h : IsBetaCoeff6 Pa φ z0 β) :
    IsBetaSupp Pa φ {z | SameClass8 z z0} β := by
  obtain ⟨q, p, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hβ⟩ := h
  exact ⟨q, p, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    fun z => by rw [hβ z]; simp only [Set.mem_ofPred_eq]⟩

/-- **The support of a coefficient with an extra restriction `S`**: every non-zero point lies in the
polar box (5.14), is free of small primes (5.8), has `τ(|z|²) ≤ τ` (5.9), lies in `S` and is
axis-free (ROUND 6.1 item (2)).  This is the form in which the §16 assembly and the reduction to
`IsCharMod4d` characters consume the hypothesis. -/
theorem IsBetaSupp.support {Pa : Work.FITop.Params} {φ : ℝ} {S : Set GaussianInt}
    {β : GaussianInt → ℂ} (h : IsBetaSupp Pa φ S β) {z : GaussianInt} (hz : β z ≠ 0) :
    InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ z ∈ S ∧ IsAxisFree Pa z := by
  obtain ⟨q, p, -, -, -, -, -, -, -, -, -, -, hβ⟩ := h
  rw [hβ z] at hz
  by_cases hc : InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧
      (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ) ∧ z ∈ S ∧ IsAxisFree Pa z
  · exact hc
  · rw [if_neg hc] at hz; exact absurd rfl hz

/-- **The Hecke `L`-function inverse bound (16.23) for *strict* characters of modulus `4d`** — the
general form of *FI* (16.23)/(16.24) in which the §16 assembly consumes it.

A strict character `χ` mod `4d` (`IsCharMod4dStrict d χ`) is a genuine character of
`(ℤ[i]/4dℤ[i])^*` extended by zero, so `L(s,ψ_m) = heckeLSeries chi m s`,
`ψ_m(z) = χ(z)(z/|z|)^m`, is a Hecke `L`-function *of conductor dividing `(4d)`*: the conductor
`𝔣` (an ideal) satisfies `𝔣 ∣ (4d)`, and the classical theory gives

  `‖L(s,ψ_m)^{-1}‖ ≤ c·d·log²(|m| + |t| + 3)`  for  `1 - c/(d^ε log(|m|+|t|+3)) < s.re ≤ 2`,

the prefactor `d` and the region width `c/d^ε` both being legitimate because `N𝔣 ≤ 16d²` (the
conductor's norm is at most the modulus's, so the conductor-normalised bound `≪ (N𝔣)^{1/2}log²`
in `σ > 1 - c/(N𝔣)^{ε/2}log` specialises to the `d`-shaped one).

This is exactly the primitive-modulus statement `Work.FIArea6Hecke.HeckeInvBound` when `χ` happens
to be primitive (conductor `(4d)`), extended to the imprimitive strict characters by the classical
Euler-factor relation `L(s,χ) = L(s,χ_prim)·∏_{𝔭 ∣ (4d)/𝔣}(1 - χ_prim(𝔭)N𝔭^{-s})` together with the
trivial bound `∏_{𝔭}(1+N𝔭^{-σ}) ≤ 2^{ω(4d)} ≤ d`.

**Caveat (machine-read, from the reviewer).**  `Work.FIArea5.S16Hecke.heckeLSeries` is Mathlib's
`LSeries`, hence *zero wherever the Dirichlet series does not converge absolutely* — in particular
on `s.re ≤ 1`.  So this statement is vacuous for `s.re ≤ 1` and on `s.re > 1` it is the classical
Euler-product bound for `1/L` (no zeros of `L` with `s.re ≥ 1`, `|λ(p)| ≤ 2`).  Its intended use
downstream is only as the *shape* of the input; the §16 contour shift needs the inverse bound for
an **explicit analytic continuation** of the completed `L`-function (the `Lam` produced by
`S16Hecke.heckeFE_of_theta`), which is what `S16Core_of_invBound` must build and state for itself. -/
def HeckeInvBoundAll (ε : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ (d : ℕ) (chi : GaussianInt → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      ∀ (m : ℤ) (s : ℂ),
        1 - c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re → s.re ≤ 2 →
        ‖(Work.FIArea5.S16Hecke.heckeLSeries chi m s)⁻¹‖
          ≤ c * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ)


/-- The archimedean factor `X^s·Γ(s+|m|/2)`, `X = 4d/π`, of the completed Hecke `L`-function of
weight `m` (the honest completion of the true `L`-function; `(4d)^{-ε}`-type region constants are
unaffected by using this rather than `LambdaHecke`, since the two differ by the entire factor
`Γ(s+|m|/2)/Γ(s+m/2)` when `m < 0`). -/
def heckeArch (d : ℕ) (m : ℤ) (s : ℂ) : ℂ :=
  ((((4 * (d : ℝ)) / Real.pi) : ℂ) ^ s) * Complex.Gamma (s + (|(m : ℝ)| / 2 : ℝ))

/-- **The inverse bound (16.23)/(16.24) for the *analytic continuation* of the Hecke `L`-function**
— the analytic input of *FI* §16 in the form its contour shift consumes.

Mathlib's `LSeries` is *zero* wherever the Dirichlet series does not converge absolutely
(`LSeries.eq_zero_of_not_LSeriesSummable`), so `heckeLSeries` carries no information in the
critical strip; (16.20)/(16.23) are statements about the continuation of
`Λ(s,ψ_m) = X^s Γ(s+|m|/2)L(s,ψ_m)`, `X = 4d/π`: for every entire `Lam` agreeing with `Λ` on
`re s > 1 + |m|/2` (such a `Lam` exists for primitive `χ` by `S16Hecke.heckeFE_of_theta`; for a
strict `χ` of conductor `𝔣 ∣ (4d)` it exists as well, being `(X/X_𝔣)^s` times the completion
normalised to the conductor), the *continuation* `Lam s / heckeArch d m s` satisfies the
classical two-constant bound

  `‖(Lam s / X^s Γ(s+|m|/2))⁻¹‖ ≤ C·d·log²(|m| + |s.im| + 3)`  for  `1 - c/(d^ε log(|m|+|s.im|+3)) < s.re ≤ 2`.

**Two constants**, as in *FI* (16.23)/(16.24) ("`c(ε) > 0` … and the implied constant depends only
on `ε`") and as in the workspace's own proven analogues `zeta_inv_le_logPow_zeroFree`,
`LFunction_inv_le_logPow_zeroFree`: the region constant `c` and the bound constant `C` are
independent (`c` may be taken below the true zero-free depth, paying in `C`); a single constant
would be *false*, since the region always contains the strip `(1,2]` (where `1/Lcont` is bounded by
a positive constant) while a `c` exceeding the zero-free depth lets a zero of `Lcont` into the
region.  The characters are the *strict* ones of modulus `4d` — the class of `S16Core` — so that the
imprimitive/odd-conductor cases (`𝔣 = (3)`, the trivial character, …) are covered. -/
def HeckeLcontInvBoundAll (ε : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      AnalyticOn ℂ Lam Set.univ →
      (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
        Lam s = heckeArch d m s * Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
      ∀ s : ℂ,
        1 - c / ((d : ℝ) ^ ε * Real.log (|(m : ℝ)| + |s.im| + 3)) < s.re → s.re ≤ 2 →
        ‖(Lam s / heckeArch d m s)⁻¹‖
          ≤ C * (d : ℝ) * (Real.log (|(m : ℝ)| + |s.im| + 3)) ^ (2 : ℕ)

/-- **The §16 core bound** — *FI* Lemma 16.2 ("Let `χ` be a character to modulus `4d` on `ℤ[i]`") for
the *strict* characters of modulus `4d`, i.e. the class on which the Hecke `L`-function of `ℚ(i)` is
defined (`IsCharMod4dStrict`), at exactly the round-6 coefficient class `IsBetaCoeff6`:

for every `ε ∈ (0, 1/4]` there are `cε > 0` and a threshold `x₀` such that for every admissible datum
with `x₀ ≤ Pa.x`, every `ν < 1/(2ε)`, every `d ≥ 1` with `d ≤ (log N)^ν`, every `|k| ≤ exp(√log N)`,
every *strict* character `χ` to modulus `4d` and every `β` of (4.13)+(5.13)+(5.7),

  `‖Σ_{z ∈ boxN} β_z χ(z)(z/|z|)^k‖ ≤ cε[exp(-ηcε(4d)^{-ε}√log N) + exp(-η log N/log P)]·(4d)N(log N)^6`.

This is `Area5_6` with `IsCharMod4d` replaced by its strict part `IsCharMod4dStrict` and nothing else:
the coefficient class is *not* generalised (see the warning on `IsBetaSupp` — an arbitrary support
restriction makes the statement false), and primitivity is deliberately not assumed, since `Area5_6`
quantifies over all `IsCharMod4d` characters, including imprimitive ones whose conductor is not of
the form `(4d')` (the trivial character, characters inflated from `(ℤ[i]/3)^*`, …); those are
strict, so they are covered here but not by a primitive-modulus statement.

The §16 ingredients are the two smoothers (16.26)–(16.28) (proved:
`FIArea5/S16/fourierCoeff_decay_cMoll`, `fourier_truncation`, `mellin_decay`), the Euler product /
local recursion of the Hecke eigenvalues (proved: `S16Hecke.heckeLSeries_eulerProduct`,
`heckeLam_localRec`, `heckeLam_bound`), the (5.7) character detection to modulus eight (the paper's
remark after (16.25); it turns the restricted support into sums with `χ` replaced by `χψ`,
`ψ ∈ \widehat{(ℤ[i]/8)^*}`, of modulus `4·lcm(d,8) ≤ 4·(8d)`), and the inverse bound
`HeckeLcontInvBoundAll` for the analytic continuation. -/
def S16Core : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ cε x0 : ℝ, 0 < cε ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
    ∀ (φ ν : ℝ) (z0 : GaussianInt) (d : ℕ) (k : ℤ) (chi : GaussianInt → ℂ),
      0 < ν → ν < 1 / (2 * ε) → 1 ≤ d → (d : ℝ) ≤ (Real.log Pa.N) ^ ν →
      |(k : ℝ)| ≤ Real.exp (Real.sqrt (Real.log Pa.N)) →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      ∀ β : GaussianInt → ℂ, IsBetaCoeff6 Pa φ z0 β →
        ‖∑ z ∈ boxN Pa,
            β z * chi z
              * (z.toComplex / (Real.sqrt (gnorm z : ℝ) : ℂ)) ^ k‖
          ≤ cε * (Real.exp (-(Pa.η * cε * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
            * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)

end

end Work.FITop4.Bridge
