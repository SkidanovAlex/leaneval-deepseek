/-
# `FIArea2/R6/Inputs6.lean` — the three analytic inputs of the round-6 area-2 assembly

`Area2_6b` (`Submission/Work/FITop4/Areas6b.lean`) is

  `‖D* − D₀‖ ≤ Cb·ϑ⁻¹τ²N²(log N)^{bFun η} + C3·(τ⁻¹+θ)θ⁴M^{1/2}N^{3/2}(log N)^{2^20}`,

i.e. *FI* (9.10) plus the §10 replacement error (7.10)/(10.4).  The assembly (see
`R6/ExactMain.lean` for the exact main term `D0ex`) is the triangle inequality

  `‖D* − D₀‖ ≤ ‖D* − D₀^exact‖ + ‖D₀^exact − D₀‖`,

and the two summands are produced by the two lemmas of this round, each from precisely one
analytic input.  This module names those three inputs as `Prop`s so that the two assembly lemmas
can be stated and proved independently of whether the inputs are available yet.

* `LacProp` — the lacunarity input of *FI* §9, (9.6)–(9.9): the averaged `h`-sum of the `(u₁,u₂)`
  box weighted by `τ₄(u₁h₁² − u₂h₂²)`,
  `Σ'_h (1+h₁²/H²)⁻¹(1+h₂²/H²)⁻¹ Σ_{u₁,u₂∈[−R,R]} (u₁,u₂)τ₄(u₁h₁²−u₂h₂²)
     ≤ C(H²+1)(2R+1)²(log(H+R+2))^K` with `K ≤ 2^10`.
  This is exactly the hypothesis `hL` of `Submission.Work.FIArea2.R6.sec9Psum_le_of_Lsum_six`, so
  it is what turns the per-frequency §9 bound into (9.10).  (`Work.FIArea2.R6.hL_six` proves it.)
* `YProp` — *FI* Lemma 10.1, (10.6)/(10.7): `Σ_{(z₁,z₂)=1}‖β_{z₁}‖‖β_{z₂}‖τ₃(Δ) ≪ θ⁴N²(log N)^{2^19}`
  for a coefficient of the round-6 support.  This is the only arithmetic input of the §10
  replacement error.  (`Work.FIArea2.R6.Ybound6` proves it.)
* `FintProp` — *FI* (7.10) with the uniform error term of Lemma 7.1: the Fourier integral
  `F₀ = Fint F γ 0 0` of (6.11) is its main term `f̂(0)·log(2|z₁z₂/Δ|)` up to
  `C·Cder·(√M(1−γ²)log(2+1/(1−γ²)) + (√M)⁻¹log(2+8√|z₁z₂|))`.
  (`Work.FIArea2.R6.Fint_logFac6` proves it.)
-/
import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FIArea2.R6.ExactMain
import Submission.Work.FIArea2.R6.Pack6
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FITop4.Defs6

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The lacunarity input of §9** (the hypothesis `hL` of `sec9Psum_le_of_Lsum_six`, with the
exponent controlled by `2^10`). -/
def LacProp : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, K ≤ 2 ^ 10 ∧
    ∀ (H : ℝ), 1 ≤ H → ∀ (R : ℕ), 1 ≤ R →
      (∑' h : ℤ × ℤ, (1 + (h.1 : ℝ) ^ 2 / H ^ 2)⁻¹ * (1 + (h.2 : ℝ) ^ 2 / H ^ 2)⁻¹
        * (∑ u1 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), ∑ u2 ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
            (Nat.gcd u1.natAbs u2.natAbs : ℝ)
              * (((u1 * h.1 ^ 2 - u2 * h.2 ^ 2).natAbs.divisors.card : ℝ) ^ 4)))
        ≤ C * (H ^ 2 + 1) * ((((2 * R + 1 : ℕ)) : ℝ) ^ 2)
            * (Real.log (H + R + 2)) ^ K

/-- ***FI* Lemma 10.1** (10.6)/(10.7) for the round-6 coefficient family. -/
def YProp : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
          copInd z1 z2
            * (‖β z1‖ * ‖β z2‖ * (tau3 (Work.FIPlan.absDelta z1 z2) : ℝ)))
        ≤ C * Pa.θ ^ (4 : ℕ) * Pa.N ^ (2 : ℕ)
            * (Real.log Pa.N) ^ ((2 : ℕ) ^ (19 : ℕ))

/-- ***FI* (7.10)** with the uniform error term of Lemma 7.1 (the elliptic-integral asymptotic
`E(γ) = log(64δ^{-2}) + o(1)`, `δ = |Δ|/|z₁z₂|`, with `1 − γ² = δ²`, combined with the `f̂(0)` vs
`Fhat` discretisation).

The hypothesis `f u ≠ 0 → M/4 ≤ u ≤ 4M` is **essential**: `Fhat Pa f` sums `f(u)u^{-1/2}` over
`u ∈ [M/4, 4M]` only, while `F` itself is supported on the wider window `[A,B] ⊆ [M/64, 64M]`
(in the application `F = majF`, whose support is `[M/64, 64M]` but whose integer values vanish
outside `[M/4, 4M]`).  Without it the two sides can differ by a factor `M` (take `F ≡ Cder` on
`[8M, 24M]`, `0` outside `[6M, 32M]`: then `Fhat = 0` while `Fint ≍ Cder·M`).  With it, the
Euler–Maclaurin error is `O(Cder·M^{-1/2})` because `|F'| ≤ Cder/M` forces `F` to be within
`Cder/M` of its integer samples. -/
def FintProp : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (A B Cder : ℝ) (F : ℝ → ℝ) (f : ℤ → ℝ)
      (z1 z2 : GaussianInt),
      Pa.M / 64 ≤ A → B ≤ 64 * Pa.M → 1 ≤ Cder → 1 ≤ Pa.M →
      ContDiff ℝ 1 F → HasCompactSupport F → (∀ n : ℤ, F (n : ℝ) = f n) →
      (∀ u : ℤ, f u ≠ 0 → Pa.M / 4 ≤ (u : ℝ) ∧ (u : ℝ) ≤ 4 * Pa.M) →
      (∀ u : ℝ, 0 ≤ F u) → (∀ u : ℝ, |F u| ≤ Cder) →
      (∀ u : ℝ, F u ≠ 0 → A ≤ u ∧ u ≤ B) →
      (∀ u : ℝ, |deriv F u| ≤ Cder / Pa.M) →
      (1 / 2 : ℝ) ≤ Work.FIArea2.gamOf z1 z2 → Work.FIArea2.gamOf z1 z2 < 1 →
      Work.FIPlan.absDelta z1 z2 ≠ 0 →
      ‖Work.FIArea2.Fint F (Work.FIArea2.gamOf z1 z2) 0 0
          - ((Work.FITop3.Fhat Pa f : ℝ) : ℂ) * ((Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ)‖
        ≤ C * Cder * (Real.sqrt Pa.M * (1 - Work.FIArea2.gamOf z1 z2 ^ 2)
              * Real.log (2 + 1 / (1 - Work.FIArea2.gamOf z1 z2 ^ 2))
            + (Real.sqrt Pa.M)⁻¹
              * Real.log (2 + 8 * Real.sqrt (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ))))

end

end Work.FIArea2.R6
