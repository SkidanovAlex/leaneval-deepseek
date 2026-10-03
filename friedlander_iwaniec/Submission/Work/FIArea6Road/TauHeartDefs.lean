/-
# `Submission.Work.FIArea6Road.TauHeartDefs` — vocabulary of the τ-restricted §16 bookkeeping

The definitions the pinned §16 sector core `Work.FIArea6Road.TauCoreOfTauHeart` and its pieces are
stated with:

* `tsumTau` — the τ-restricted Möbius–Hecke sum `Σ_n [τ(n) ≤ Pa.τ]·tsumTerm` (the object the
  τ-restricted heart `S16TsumHeartTau` bounds);
* `SuppTau` — the τ-restricted §16 support `IsPrimary ∧ NoSmallPrimes ∧ τ ≤ Pa.τ`;
* `s16Term`, `s16Core` — the §16 summand with and without the angle factor `q(arg z − φ)`;
* `fser` — the Fourier series of the 2π-periodisation of the angle mollifier `q`, i.e.
  `Σ_ℓ q̂(ℓ)e^{iℓβ}` (absolutely convergent by `Work.FIArea5.S16.fcoef_summable`).

Nothing here is a theorem; this module exists so that the pieces of the Fourier bookkeeping can be
delegated and stated in a common vocabulary.
-/
import Mathlib
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FIArea6Hecke.S16CoreDefs
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea6.S16TsumHeartDefs
import Submission.Work.FIArea5.S16.fourier_truncation
import Submission.Work.FIArea6Road.HeartAux
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea6.TauPieces.CleanSumEqTsum

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The **τ-restricted Möbius–Hecke sum** of *FI* (16.38):
`Σ_n [τ(n) ≤ Pa.τ]·tsumTerm Pa chi m p n`.  This is the object bounded by the heart
`Work.FIArea6Road.S16TsumHeartTau`. -/
def tsumTau (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ) : ℂ :=
  ∑' n : ℕ, (if ((n.divisors.card : ℝ) ≤ Pa.τ) then
      Work.FIArea6.TauPieces.tsumTerm Pa chi m p n else 0)

/-- The τ-restricted §16 support (5.8)+(5.9) of a Gaussian integer. -/
def SuppTau (Pa : Work.FITop.Params) (z : GaussianInt) : Prop :=
  Work.FIPlan.IsPrimary z ∧ Work.FITop4.NoSmallPrimes Pa z ∧
    (((Work.FIPlan.gnorm z).divisors.card : ℝ) ≤ Pa.τ)

/-- The **§16 summand with its angle factor** `q(arg z − φ)`: the summand of `S16TauCoreP`. -/
def s16Term (Pa : Work.FITop.Params) (φ : ℝ) (j : ℤ) (chi : GaussianInt → ℂ)
    (q p : ℝ → ℝ) (z : GaussianInt) : ℂ :=
  ((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
    * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
    * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
    * chi z
    * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j

/-- The **angle-free part** of the §16 summand: `p(|z|²)·μ(|z|²)·γ(|z|²;C)·χ(z)(z/|z|)^j`. -/
def s16Core (Pa : Work.FITop.Params) (j : ℤ) (chi : GaussianInt → ℂ) (p : ℝ → ℝ)
    (z : GaussianInt) : ℂ :=
  (p (Work.FIPlan.gnorm z) : ℂ)
    * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
    * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
    * chi z
    * (z.toComplex / (Real.sqrt (Work.FIPlan.gnorm z : ℝ) : ℂ)) ^ j

/-- The **Fourier series of the periodisation** of the angle mollifier `q`, evaluated at `β`:
`Σ_ℓ q̂(ℓ)·e^{iℓβ}` (absolutely convergent by `Work.FIArea5.S16.fcoef_summable`). -/
def fser (q : ℝ → ℝ) (β : ℝ) : ℂ :=
  ∑' ℓ : ℤ, Work.FIArea5.S16.fcoef q ℓ * Complex.exp ((ℓ : ℂ) * Complex.I * β)

/-- The τ-weighted **clean §16 box sum** `Σ_{z ∈ boxN} [SuppTau z]·p(|z|²)μ(|z|²)γ(|z|²;C)·ψ_m(z)`,
i.e. the left-hand side of `CleanSumEqTsum` with the weight `[τ(|z|²) ≤ Pa.τ]`. -/
def boxCoreSum (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ) : ℂ :=
  ∑ z ∈ Work.FITop.boxN Pa,
    (if SuppTau Pa z then
      (p (Work.FIPlan.gnorm z) : ℂ) * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
        * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
        * Work.FIArea5.S16Hecke.psi chi m z
      else 0)

/-- The **§16 target box sum**: `Σ_{z ∈ boxN} [SuppTau z ∧ IsAxisFree z]·s16Term z`, i.e. the sum
bounded by the conclusion `S16TauCoreP` (with `s16Term` the summand carrying `q(arg z − φ)`). -/
def boxTermSum (Pa : Work.FITop.Params) (φ : ℝ) (j : ℤ) (chi : GaussianInt → ℂ)
    (q p : ℝ → ℝ) : ℂ :=
  ∑ z ∈ Work.FITop.boxN Pa,
    (if SuppTau Pa z ∧ Work.FITop4.IsAxisFree Pa z then s16Term Pa φ j chi q p z else 0)

/-- The **tail of the Fourier coefficients of `q`** beyond the frequency cutoff `L`:
`Σ_{|ℓ| > L} |q̂(ℓ)|` (the two one-sided `ℕ`-indexed tails). -/
def fcoefTailSum (q : ℝ → ℝ) (L : ℕ) : ℝ :=
  (∑' k : ℕ, ‖Work.FIArea5.S16.fcoef q ((k : ℤ) + L + 1)‖)
    + (∑' k : ℕ, ‖Work.FIArea5.S16.fcoef q (-((k : ℤ) + L + 1))‖)

lemma s16Term_eq (Pa : Work.FITop.Params) (φ : ℝ) (j : ℤ) (chi : GaussianInt → ℂ)
    (q p : ℝ → ℝ) (z : GaussianInt) :
    s16Term Pa φ j chi q p z
      = ((q (Complex.arg z.toComplex - φ) : ℝ) : ℂ) * s16Core Pa j chi p z := by
  unfold s16Term s16Core
  rw [Complex.ofReal_mul]
  ring

end

end Work.FIArea6Road
