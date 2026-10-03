/-
# FI §15: the vocabulary of the *separated* form of the smooth `ψ`-cut reduction

This module isolates the objects in which the §15 reduction of the frozen smooth `ψ`-cut
`Work.FIArea4.psiCut` is proved.  The proof has two halves, and both are stated about the
definitions below:

* **the separation half** (proved in `Submission.Work.FIArea4.S15_psi_cut_reduction`): the
  `ψ`-cut sum `TcutMod (radN Pa) (psiCut ψ X j) β` is, by the Fourier–Mellin separation
  `Work.FIArea4.Vflip.separation_ineq`, bounded by `(log N)^6` times a bound for the
  *exponential sums* `S15expLog` on the same index set; the logarithmic factor `logFac` is then
  expanded in the mollified log-sine Fourier series (`Work.FIArea4.logSine_fourier`), which turns
  `S15expLog` into `∑'_ℓ c_ℓ · (S15expSum ℓ)` — the *separated* sums.

* **the variance half** (`Work.FIArea4.S15expSum_bound`, delegated): each `S15expSum ℓ` is
  bounded by `C (log N)^{24} B E` with the §15 bracket
  `B = X^{-1/2}N + N^{1/3}X^{-1/3}N^{2/3} + N^{23/24+1/1000}` and the energy
  `E = Σ_{z ∈ boxN} τ(|Re z|) ‖β z‖²`, by the class Cauchy–Schwarz
  (`Work.FIArea4.pairSum_twisted_le_Evar`), the `e = (d,r₁) = (d,r₂)` stratification of FI
  (15.1)–(15.2) (which needs the primitivity in `IsPrimBoxCoeff`) and Proposition 14.1
  (`Work.FIArea4.p14_all_of_h11`) over each dyadic modulus range.

## The index set

The paper's (15.2) sums over the modulus `d` with `X < d`, the congruence `4d ∣ |Δ|` and the
cut, and after the separation of variables the *cut* is absorbed into the phases `e(ux)y^{it}`;
the modulus range may then be *relaxed* to the pair-independent window `X < d ≤ Y` with
`Y = ⌈N/(X·2^j)⌉` because every `d` outside the window contributes `ψ(·) = 0` (the `ψ`-argument
is then `< 1/2`) while a single fixed array then serves *all* the moduli of the window — this is
exactly what makes the class Cauchy–Schwarz and Proposition 14.1 applicable.  This is the
index set `S15ixSet` below.  (Two harmless conventions: the pairs `Δ = 0` are excluded — they
contribute `ψ 0 = 0` to the `ψ`-sum — and `d ≥ 1` is built in.)
-/
import Mathlib
import Submission.Work.FITop.Defs
import Submission.Work.FITop3.Defs3
import Submission.Work.FIArea4.S15prim_defs
import Submission.Work.FIArea4.A4varbounds

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The threshold separating the "small determinant" pairs, which are handled by a plain count,
from the bulk. -/
def S15K : ℕ := 4

/-- The relaxed upper limit `Y = ⌈N/(X·2^j)⌉ + 1` of the modulus `d`. -/
def S15Y (Pa : Work.FITop.Params) (X j : ℕ) : ℕ := ⌈Pa.N / ((X : ℝ) * (2 : ℝ) ^ j)⌉₊ + 1

/-- The triples `((z₁,z₂),d)` carrying the §15 sum. -/
abbrev S15Id : Type := (GaussianInt × GaussianInt) × ℕ

/-- The angular character `e^{iℓ(α₂-α₁)}` of the log-sine expansion (15.5), `α_i = arg z_i`. -/
def S15theta (ℓ : ℤ) (z1 z2 : GaussianInt) : ℂ :=
  Complex.exp (Complex.I * (ℓ : ℂ) *
    (((Complex.arg z2.toComplex - Complex.arg z1.toComplex : ℝ)) : ℂ))

/-- The "difference ratio" `x(z₁,z₂) = s₁/r₁ - s₂/r₂` of FI (15.3). -/
def S15x (z1 z2 : GaussianInt) : ℝ := (z1.im : ℝ) / (z1.re : ℝ) - (z2.im : ℝ) / (z2.re : ℝ)

/-- The "size" `y = |r₁r₂|/(4·X·2^j·d)` of FI (15.3). -/
def S15y (X j d : ℕ) (z1 z2 : GaussianInt) : ℝ :=
  ((z1.re * z2.re).natAbs : ℝ) / (4 * (X : ℝ) * (2 : ℝ) ^ j * (d : ℝ))

/-- The weight `(φ(d)/d)·(r₁r₂+s₁s₂ | d)` of a modulus `d` of the pair sum. -/
def S15w (i : S15Id) : ℂ :=
  (((Nat.totient i.2 : ℝ) / (i.2 : ℝ) : ℝ) : ℂ) *
    ((jacobiSym ((star i.1.1 * i.1.2).re) i.2 : ℤ) : ℂ)

/-- The coefficient `2 β_{z₁} \bar β_{z₂}` of a pair. -/
def S15coef (β : GaussianInt → ℂ) (i : S15Id) : ℂ :=
  2 * (β i.1.1 * star (β i.1.2)) * S15w i

/-- The exponential phase `e(u x)y^{it}` of FI (15.3). -/
def S15phase (X j : ℕ) (u t : ℝ) (i : S15Id) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((u : ℂ) * ((S15x i.1.1 i.1.2 : ℝ) : ℂ))) *
    (((S15y X j i.2 i.1.1 i.1.2 : ℝ) : ℂ) ^ (Complex.I * (t : ℂ)))

/-- **The relaxed §15 index set**: pairs `(z₁,z₂)` of the box `boxN Pa` with `(z₁,z₂) = 1` and
`Δ ≠ 0`, and moduli `d` with `X < d ≤ Y` and `4d ∣ |Δ|`. -/
def S15ixSet (Pa : Work.FITop.Params) (X j : ℕ) : Finset S15Id :=
  (((Work.FITop.boxN Pa).product (Work.FITop.boxN Pa)).product
      (Finset.Icc 1 (S15Y Pa X j))).filter
    (fun i => Work.FIPlan.GaussCoprime i.1.1 i.1.2 ∧ X < i.2 ∧
      4 * i.2 ∣ Work.FIPlan.absDelta i.1.1 i.1.2 ∧ 0 < Work.FIPlan.absDelta i.1.1 i.1.2)

/-- **The separated §15 sum**: `2 ∑_{(z₁,z₂,d)} β_{z₁}\barβ_{z₂} (φ(d)/d)(r₁r₂+s₁s₂|d)
e^{iℓ(α₂-α₁)} e(ux) y^{it}`, the object bounded by the variance chain. -/
def S15expSum (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ)
    (u t : ℝ) : ℂ :=
  ∑ i ∈ S15ixSet Pa X j, S15coef β i * S15theta ℓ i.1.1 i.1.2 * S15phase X j u t i

/-- The same separated sum with the *logarithmic factor* `logFac` in place of the angular
character `e^{iℓ(α₂-α₁)}`: this is the exponential sum of the separation step. -/
def S15expLog (Pa : Work.FITop.Params) (X j : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) : ℂ :=
  ∑ i ∈ S15ixSet Pa X j,
    S15coef β i * ((Work.FITop3.logFac i.1.1 i.1.2 : ℝ) : ℂ) * S15phase X j u t i

/-- The `ψ`-cut sum over the relaxed index set: by `S15psiSum_eq_TcutMod` this is the frozen
smooth-piece sum `TcutMod (radN Pa) (psiCut ψ X j) β`. -/
def S15psiSum (Pa : Work.FITop.Params) (X j : ℕ) (ψ : ℝ → ℝ) (β : GaussianInt → ℂ) : ℂ :=
  ∑ i ∈ S15ixSet Pa X j,
    S15coef β i * ((Work.FITop3.logFac i.1.1 i.1.2 : ℝ) : ℂ) *
      ((ψ (|S15x i.1.1 i.1.2| * S15y X j i.2 i.1.1 i.1.2) : ℝ) : ℂ)

/-- The §15 bracket `X^{-1/2}N + N^{1/3}X^{-1/3}N^{2/3} + N^{23/24+1/1000}` (the three terms of
Proposition 15.1 with `ε = 1/1000`). -/
def S15Br (Pa : Work.FITop.Params) (X : ℕ) : ℝ :=
  ((X : ℝ) ^ (-(1 : ℝ) / 2) * Pa.N)
    + (Pa.N ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3) * Pa.N ^ ((2 : ℝ) / 3))
    + Pa.N ^ ((23 : ℝ) / 24 + (1 : ℝ) / 1000)

/-- The energy `Σ_{z ∈ boxN} τ(|Re z|)‖β z‖²` of FI §15. -/
def S15En (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : ℝ :=
  ∑ z ∈ Work.FITop.boxN Pa,
    ((z.re.natAbs.divisors.card : ℕ) : ℝ) * Complex.normSq (β z)

lemma S15Br_nonneg (Pa : Work.FITop.Params) (X : ℕ) : 0 ≤ S15Br Pa X := by
  unfold S15Br
  have hX0 : (0 : ℝ) ≤ (X : ℝ) := Nat.cast_nonneg X
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have h1 : 0 ≤ (X : ℝ) ^ (-(1 : ℝ) / 2) * (Pa.N : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hX0 _) hN0
  have h2 : 0 ≤ (Pa.N : ℝ) ^ ((1 : ℝ) / 3) * (X : ℝ) ^ (-(1 : ℝ) / 3)
      * (Pa.N : ℝ) ^ ((2 : ℝ) / 3) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hX0 _))
      (Real.rpow_nonneg hN0 _)
  have h3 : 0 ≤ (Pa.N : ℝ) ^ ((23 : ℝ) / 24 + (1 : ℝ) / 1000) :=
    Real.rpow_nonneg hN0 _
  linarith

lemma S15En_nonneg (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : 0 ≤ S15En Pa β := by
  unfold S15En
  refine Finset.sum_nonneg (fun z _ => ?_)
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

end

end Work.FIArea4
