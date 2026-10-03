/-
# `Submission.Work.FIArea6V.Defs` — the clean area-6 lane: vocabulary

This is the vocabulary of the *clean* area-6 lane, the V-variant of the pinned §16 chain of
`Submission/Work/FIArea6c/` and `Submission/Work/FIArea6Road/PinnedDefs.lean`.  Its design is the
lead's `Submission/Work/FIArea6/AREA6_CONTRACT_LEAD.md` §§2–3: the (5.9) divisor pin
`Pa.τ = tauOf Pa.x Asave` is replaced everywhere by the *τ-vacuity* hypothesis `TauVac Pa φ`,
which says that the (5.9) restriction is vacuous on the polar (5.8)-support actually used.
`TauVac` is supplied at the raised datum `Pa.tauMax` by the elementary arithmetic of
`FIArea6V/TauArith.lean`.

The V-chain mirrors the pinned chain shape for shape (`Area6_6c` → `Area6_6V`,
`Section16Uc` → `Section16UV`, `Area5TwoP` → `Area5TwoV`, …), so that each node of the pinned
chain transports by a literal copy with the pin hypothesis replaced by `TauVac`.

Nothing here is a theorem; this module exists so that the pieces of the V-chain can be delegated
and stated in a common vocabulary.
-/
import Mathlib
import Submission.Work.FITop4.Areas6e
import Submission.Work.FITop4.Areas6
import Submission.Work.FIArea6Hecke.S16CoreDefs
import Submission.Work.FIArea6.S16TsumHeartDefs

set_option autoImplicit false

namespace Work.FIArea6V

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. τ-vacuity and the raised datum -/

/-- **τ-vacuity of the (5.9) divisor restriction on the polar (5.8)-support**: every point of the
polar box (5.14) that is free of small primes (5.8) satisfies the (5.9) bound `τ(|z|²) ≤ Pa.τ`.

This is the hypothesis that replaces the pin `Pa.τ = tauOf Pa.x Asave` of
`Work.FITop4.Area6_6c` in the clean lane: under it the τ-restricted sums of the pinned §16 chain
are *pointwise equal* to the unrestricted (clean) ones, so the clean §16 core bounds them. -/
def TauVac (Pa : Work.FITop.Params) (φ : ℝ) : Prop :=
  ∀ z : GaussianInt, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.NoSmallPrimes Pa z →
    (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ

/-- **`Pa` with the divisor cutoff raised to its admissible maximum `x^{η/3}`** (5.23).

The only field that changes is `τ`; `hτ1 := Pa.hτ1.trans Pa.hτ2` (the old lower bound is below the
old upper bound, which is the new value) and `hτ2 := le_rfl` keep the datum admissible, with no
threshold in the constants `A, A'`. -/
def tauMax (Pa : Work.FITop.Params) : Work.FITop.Params :=
  { Pa with τ := (Pa.x : ℝ) ^ (Pa.η / 3), hτ1 := Pa.hτ1.trans Pa.hτ2, hτ2 := le_rfl }

@[simp] theorem tauMax_x (Pa : Work.FITop.Params) : (tauMax Pa).x = Pa.x := rfl

@[simp] theorem tauMax_eta (Pa : Work.FITop.Params) : (tauMax Pa).η = Pa.η := rfl

@[simp] theorem tauMax_theta (Pa : Work.FITop.Params) : (tauMax Pa).θ = Pa.θ := rfl

@[simp] theorem tauMax_N (Pa : Work.FITop.Params) : (tauMax Pa).N = Pa.N := rfl

@[simp] theorem tauMax_Pz (Pa : Work.FITop.Params) : (tauMax Pa).Pz = Pa.Pz := rfl

@[simp] theorem tauMax_tau (Pa : Work.FITop.Params) : (tauMax Pa).τ = (Pa.x : ℝ) ^ (Pa.η / 3) :=
  rfl

@[simp] theorem tauMax_vartheta (Pa : Work.FITop.Params) : (tauMax Pa).ϑ = Pa.ϑ := rfl

@[simp] theorem tauMax_C (Pa : Work.FITop.Params) : (tauMax Pa).C = Pa.C := rfl

@[simp] theorem tauMax_M (Pa : Work.FITop.Params) : (tauMax Pa).M = Pa.M := rfl

/-! ## 2. The clean §16 core with an axis-free polar box -/

/-- **`S16CleanCoreTwoA`** — *FI* Lemma 16.2 as printed (clean support `IsPrimary ∧ NoSmallPrimes`,
no (5.9), no axis clause in the support) with the *axis-free polar box* supplied as a hypothesis.

The extra hypothesis is what the §16 Fourier bookkeeping needs: the principal-argument
difference `arg z − φ` stays inside one period, so the Fourier series of `q` evaluates to `q` and
no branch-cut defect occurs (`Work.FIArea6Road.s16Term_eq_zero_of_axis_near`).  With it, the
unrestricted `S16CleanCoreTwo` is the form the §16 argument actually proves. -/
def S16CleanCoreTwoA : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ c C x0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < x0 ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
    ∀ (φ ν : ℝ) (d : ℕ) (j : ℤ) (chi : GaussianInt → ℂ) (q p : ℝ → ℝ),
      (∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z) →
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

/-! ## 3. The τ-restricted §16 cores at τ-vacuity -/

/-- **`S16RadialNoClassTwoV`** — `Work.FIArea6.S16RadialNoClassTwo` (the τ-restricted radial §16
core on the support `IsPrimary ∧ NoSmallPrimes ∧ τ(|z|²) ≤ Pa.τ ∧ IsAxisFree`) with the two
hypotheses `TauVac Pa φ` and an axis-free polar box added to its `∀Pa`/`∀φ` clause.

Under them the radial summand equals the clean summand *pointwise* (a non-zero summand forces the
polar box, whence τ and axis hold), so this is a weakening of `S16CleanCoreTwoA`. -/
def S16RadialNoClassTwoV : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ c C x0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < x0 ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
    ∀ (φ ν : ℝ) (d : ℕ) (j : ℤ) (chi : GaussianInt → ℂ) (q p : ℝ → ℝ),
      TauVac Pa φ →
      (∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z) →
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
              ∧ Work.FITop4.IsAxisFree Pa z then
            ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
              * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
              * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
              * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j
          else 0)‖
        ≤ C * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
            + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
          * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)

/-- **`S16RadialCoreTwoV`** — `Work.FIArea6.S16RadialCoreTwo` (the same radial core with the (5.7)
congruence `SameClass8 z z0` added to the support and detected by characters mod eight) with
`TauVac Pa φ` and an axis-free polar box added. -/
def S16RadialCoreTwoV : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ c C x0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < x0 ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
    ∀ (φ ν : ℝ) (z0 : GaussianInt) (d : ℕ) (j : ℤ) (chi : GaussianInt → ℂ) (q p : ℝ → ℝ),
      TauVac Pa φ →
      (∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z) →
      0 < ν → ν < 1 / (2 * ε) → 1 ≤ d → (d : ℝ) ≤ (Real.log Pa.N) ^ ν →
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
        ≤ C * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
            + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
          * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)

/-- **`S16CoreTwoV`** — `Work.FIArea6.S16CoreTwo` (the `β`-indexed §16 core at the strict
characters) with `TauVac Pa φ` and an axis-free polar box added. -/
def S16CoreTwoV : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ c C x0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < x0 ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
    ∀ (φ ν : ℝ) (z0 : GaussianInt) (d : ℕ) (k : ℤ) (chi : GaussianInt → ℂ),
      TauVac Pa φ →
      (∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z) →
      0 < ν → ν < 1 / (2 * ε) → 1 ≤ d → (d : ℝ) ≤ (Real.log Pa.N) ^ ν →
      |(k : ℝ)| ≤ Real.exp (Real.sqrt (Real.log Pa.N)) →
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      ∀ β : GaussianInt → ℂ, Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
        ‖∑ z ∈ Work.FITop.boxN Pa,
            β z * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ k‖
          ≤ C * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
            * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)

/-! ## 4. The two-constant §16 input and the §16 display at τ-vacuity -/

/-- **`Area5TwoV`** — `Work.FIArea6.Area5Two` (*FI* Lemma 16.2 in its two-constant form at the
round-6 coefficient class `IsBetaCoeff6` and the characters `IsCharMod4d6`) with `TauVac Pa φ` and
an axis-free polar box added to its `∀Pa` clause.

This is *FI* Lemma 16.2 for the coefficient FI actually treats: the (5.9) clause inside
`IsBetaCoeff6` is discharged by `TauVac`, so the bound is the clean one of §16. -/
def Area5TwoV : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 4 →
    ∃ c C x0 : ℝ, 0 < c ∧ 0 < C ∧ 0 < x0 ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) →
    ∀ (φ ν : ℝ) (z0 : GaussianInt) (d : ℕ) (k : ℤ) (chi : GaussianInt → ℂ),
      TauVac Pa φ →
      (∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z) →
      0 < ν → ν < 1 / (2 * ε) → 1 ≤ d → (d : ℝ) ≤ (Real.log Pa.N) ^ ν →
      |(k : ℝ)| ≤ Real.exp (Real.sqrt (Real.log Pa.N)) →
      Work.FITop4.IsCharMod4d6 d chi →
      ∀ β : GaussianInt → ℂ, Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
        ‖∑ z ∈ Work.FITop.boxN Pa,
            β z * chi z
              * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ k‖
          ≤ C * (Real.exp (-(Pa.η * c * ((4 * d : ℕ) : ℝ) ^ (-ε) * Real.sqrt (Real.log Pa.N)))
              + Real.exp (-(Pa.η * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
            * ((4 * d : ℕ) : ℝ) * Pa.N * (Real.log Pa.N) ^ (6 : ℕ)

/-- **`Section16UV`** — `Work.FIArea6.Section16Uc` (the paper's §16 display for the cut `Ucut`)
with the pin `Pa.τ = tauOf Pa.x Asave` replaced by `TauVac Pa φ` in the `∀Pa`/`∀β` clause. -/
def Section16UV : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ C c1 c2 x0 : ℝ, 0 < C ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < x0 ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    Work.FITop4.IsBetaCoeff6 Pa φ z0 β → TauVac Pa φ →
    (∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z) →
    1 ≤ X → (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU →
    (X : ℝ) ^ 3 ≤ Real.exp (Real.sqrt (Real.log Pa.N)) →
    ‖Work.FITop4.Ucut (Work.FITop.radN Pa) X β‖
      ≤ C * ((Real.exp (-(c1 * (Real.log Pa.N) ^ ((1 : ℝ) / 4)))
                + Real.exp (-(c2 * Real.log Pa.N / Real.log (Pa.Pz : ℝ))))
              * (X : ℝ) ^ (5 : ℕ) * Pa.N ^ (2 : ℕ) * (Real.log (2 + Pa.N)) ^ (13 : ℕ))
        + C * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ (2 : ℕ) * Real.log Pa.N

/-! ## 5. The area-6 contract of the clean lane -/

/-- **`Area6_6V`** — *FI* Proposition 16.3 = (16.41) for the round-6 coefficient class
`IsBetaCoeff6` at **τ-vacuous** admissible data and an axis-free polar box, no pin.

Same shape as `Work.FITop4.Area6_6c` with `Pa.τ = tauOf Pa.x Asave` replaced by `TauVac Pa φ`;
this is the Prop the §16 assembly `FIArea6V/GlueV.lean` produces. -/
def Area6_6V : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ cν x0 : ℝ, 0 < cν ∧
  ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
  ∀ (X : ℕ) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
    TauVac Pa φ → Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
    (∀ z, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z) →
    1 ≤ X → (X : ℝ) ≤ (Real.log Pa.N) ^ Work.FITop4.nuU →
      (X : ℝ) ^ 3 ≤ Real.exp (Real.sqrt (Real.log Pa.N)) →
    ‖Work.FITop4.Ucut (Work.FITop.radN Pa) X β‖
      ≤ cν * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log Pa.N

end

end Work.FIArea6V
