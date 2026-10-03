/-
# `Submission.Work.FIArea6.TauPieces.TsumHeartDefs` — vocabulary of the §16 heart (`Tsum`)

Definitions used to state (and later prove) the §16 contour-shift bound
`Work.FIArea6.TsumHeart` for the Möbius-twisted Hecke sum

  `Tsum = Σ_{(n,Π)=1} λ_m(n)·μ(n)·γ(n;C)·p(n)`

of *FI* (16.30).  The objects isolated here are

* `tcoef` — the Dirichlet coefficient `c(n) = 1_{(n,Π)=1} λ_m(n) μ(n) γ(n;C)`;
* `Zsfun` — the Dirichlet series `Z(s) = Σ_n c(n) n^{-s}` (16.30);
* `Mfac`, `Pfac`, `Qfac` — the three factors of the Euler-product regrouping `Z = M·P·Q`
  (16.31)–(16.34);
* `Phifac` — the absolutely convergent Euler product `Φ = M·L` (16.31).

Nothing here is a theorem to be proved; this module exists so that the §16 heart can be
decomposed into lemmas stated in a common vocabulary and worked on in parallel.
-/
import Mathlib
import Submission.Work.FIArea6.S16TsumHeartDefs
import Submission.Work.FITop4.Bridge.area5_6_defs

set_option autoImplicit false

namespace Work.FIArea6.TauPieces

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The Dirichlet coefficient `c(n) = 1_{(n,Π)=1}·λ_m(n)·μ(n)·γ(n;C)` of the Möbius-twisted
Hecke series (16.30). -/
def tcoef (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (n : ℕ) : ℂ :=
  if Work.FIArea6Hecke.NoSmallPrimesNat Pa n then
    Work.FIArea5.S16Hecke.heckeLam chi m n * (ArithmeticFunction.moebius n : ℂ)
      * (Work.FIPlan.gammaTrunc Pa.C n : ℂ)
  else 0

/-- The summand `c(n)·p(n)` of `Tsum`. -/
def tsumTerm (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ)
    (n : ℕ) : ℂ :=
  if Work.FIArea6Hecke.NoSmallPrimesNat Pa n then
    Work.FIArea5.S16Hecke.heckeLam chi m n * (ArithmeticFunction.moebius n : ℂ)
      * (Work.FIPlan.gammaTrunc Pa.C n : ℂ) * (p (n : ℝ) : ℂ)
  else 0

lemma Tsum_eq_tsumTerm (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (p : ℝ → ℝ) :
    Work.FIArea6Hecke.Tsum Pa chi m p = ∑' n, tsumTerm Pa chi m p n := rfl

/-- **(16.30)**: the Dirichlet series `Z(s) = Σ_n c(n) n^{-s}` of the Möbius-twisted Hecke
eigenvalues, restricted to the integers free of the primes `≤ Pz`. -/
def Zsfun (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, tcoef Pa chi m n * (n : ℂ) ^ (-s)

/-- **(16.31)**: `M(s) = ∏_p (1 - λ(p) p^{-s})` over all rational primes. -/
def Mfac (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes,
    (1 - Work.FIArea5.S16Hecke.heckeLam chi m (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))

/-- **(16.33)**: `P(s) = ∏_{p ≤ P} (1 - λ(p) p^{-s})^{-1}` over the primes `≤ Pz`. -/
def Pfac (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) : ℂ :=
  ∏ p ∈ Nat.primesBelow (Pa.Pz + 1),
    (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹

/-- **(16.34)**: the remaining sum `Q(s) = Σ_{c ≤ C, (c,Π)=1} λ(c) c^{-s}
∏_{p|c} (1 - λ(p) p^{-s})^{-1}`. -/
def Qfac (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) : ℂ :=
  ∑ c ∈ (Finset.Icc 1 ⌊Pa.C⌋₊).filter
      (fun c => Squarefree c ∧ Nat.Coprime c (∏ p ∈ Nat.primesBelow (Pa.Pz + 1), p)),
    Work.FIArea5.S16Hecke.heckeLam chi m c * (c : ℂ) ^ (-s)
      * ∏ p ∈ c.primeFactors,
          (1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s))⁻¹

/-- The local Hecke `L`-factor at the rational prime `p`, in the form in which the Euler product
of `L(s,ψ)` is available in the workspace: the `p`-factor of `Σ_n λ(n) n^{-s}`.

The paper's display of (16.30) writes it as `(1 - λ(p)T + ε(p)T²)^{-1}` with `ε(p) = 1` for
`p ≡ 1 (mod 4)` and `ε(p) = 0` otherwise; that display is *not* correct at the inert primes
(`p ≡ 3 (mod 4)`, where `λ(p) = 0` but the local factor is `(1 - ψ((p))T²)^{-1}` with
`ψ((p)) = -λ(p²)`).  The workspace form (`heckeLam_localInverse`), which is the one used here, is
`(Σ_ν λ(p^ν)T^ν)·(1 - λ(p)T + (λ(p)² - λ(p²))T²) = 1`. -/
def localL (chi : GaussianInt → ℂ) (m : ℤ) (p : ℕ) (s : ℂ) : ℂ :=
  1 - Work.FIArea5.S16Hecke.heckeLam chi m p * (p : ℂ) ^ (-s)
    + ((Work.FIArea5.S16Hecke.heckeLam chi m p) ^ 2
        - Work.FIArea5.S16Hecke.heckeLam chi m (p ^ 2)) * ((p : ℂ) ^ (-s)) ^ 2

def Phifac (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes,
    (1 - Work.FIArea5.S16Hecke.heckeLam chi m (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))
      / localL chi m (p : ℕ) s

end

end Work.FIArea6.TauPieces
