/-
# `Submission.Work.FIArea7.Area7Char6` — the (17.10)/(17.13) interface of area 7

Once the (17.10) engine is assembled, the contract's area 7 is reduced to a bound on the
**character-expanded main term**

  `Work.FIArea7.WUniOmega6Pull6Char Pa X β K ε
     = 2 Σ_{b ≤ uniB Pa} Σ_{e ≤ X} (μ(b)/b) Σ_k û(k) (1/Φ(4be)) Σ_χ J(χ)|S^k_χ(β')|²`

(`Work.FIArea7.UniCharTerm6`), whose estimate is the paper's (17.13): the sum over `b ≤ X`
is controlled by *FI* Proposition 17.2 (17.18) applied to every character with modulus
`4be ≤ 4X²` (the term count being `≪ X⁹`), and the sum over `b > X` — which is *not* present in
the paper's parametrisation (`NOTES.md` §57.2) — by the elementary counting of the lattice
`{z₂ : 4be ∣ Im(z̄₁z₂)}` (`O(N/(4be) + 1)` points, `NOTES.md` §57.3).

This file fixes

* `Prop172_6` — *FI* Proposition 17.2 (17.18) in the round-6 vocabulary, as the project's
  remaining deep input (§§19–26: the Dirichlet–Jacobi-Kubota symbol, the linear/bilinear forms of
  §§21–23, Theorem 2ψ).  It is the *only* place where `L`-function technology enters area 7;
* the split `WUniOmega6Pull6Char = Low + High` at the cut `b ≤ X`.
-/
import Mathlib
import Submission.Work.FIArea7.UniCharTerm6
import Submission.Work.FIArea7.UniCharFree6
import Submission.Work.FIArea7.UniChain6
import Submission.Work.FIArea7.reflSign_separable

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- ***FI* Proposition 17.2 / (17.18), round-6 vocabulary.**  For every `η ∈ (0, 3/32)` there are
`δ₁ > 0`, `c₁ > 0` and a threshold `x₀` such that for every admissible datum, every (5.7)+(5.8)
coefficient `β` with `reflSign = ε ⊗ ε` on its polar box, every modulus `Q = 4be` (encoded as an
arbitrary `Q`), every frequency `k` and every character `χ` of `(ℤ[i]/Q)^*` with
`Q(|k|+1) ≤ N^{δ₁}`,

  `‖S^k_χ(β')‖ ≤ c₁·N^{1-δ₁}`,

`S^k_χ(β')` being the §16 coefficient sum `Work.FIArea7.uniSChar` (i.e. (17.14) with the twist
(17.8)/(17.16), conjugated — see `NOTES.md` §57.1).  This is the paper's `S^k_χ(β') ≪ N^{1-δ}`
uniformly in `d(|k|+1) ≤ N^δ`; its proof is *FI* §§19–26 and is *not* part of area 7. -/
def Prop172_6 : Prop :=
  ∀ η : ℝ, 0 < η → η < 3 / 32 →
  ∃ δ₁ c₁ x0 : ℝ, 0 < δ₁ ∧ 0 < c₁ ∧
    ∀ (Pa : Work.FITop.Params), x0 ≤ (Pa.x : ℝ) → Pa.η = η →
    ∀ (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ) (ε : GaussianInt → ℤ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      (∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 →
        Work.FITop3.InPolarBox Pa φ z2 → reflSign z1 z2 = ε z1 * ε z2) →
      ∀ (Q : ℕ) [NeZero Q] (k : ℤ)
        (χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ),
        (Q : ℝ) * (|(k : ℝ)| + 1) ≤ Pa.N ^ δ₁ →
        ‖uniSChar Pa Q ε β k χ‖ ≤ c₁ * Pa.N ^ (1 - δ₁)

/-- The part `Σ_{b ≤ X}` of the (17.10) main term — the part to which *FI* Proposition 17.2 is
applied term by term (all moduli are `≤ 4X²`, so the restriction `Q(|k|+1) ≤ N^{δ₁}` is met in
the contract's range). -/
def WUniOmega6Pull6CharLow (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) (K : ℕ)
    (ε : GaussianInt → ℤ) : ℂ :=
  2 * ∑ b ∈ (Finset.Icc 1 (uniB Pa)).filter (fun b => b ≤ X),
        ∑ e ∈ Finset.Icc 1 X, uniCharTerm Pa b e β K ε

/-- The part `Σ_{X < b ≤ uniB Pa}` of the (17.10) main term — absent from the paper's
parametrisation (`NOTES.md` §57.2), estimated here by the lattice count of
`NOTES.md` §57.3. -/
def WUniOmega6Pull6CharHigh (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) (K : ℕ)
    (ε : GaussianInt → ℤ) : ℂ :=
  2 * ∑ b ∈ (Finset.Icc 1 (uniB Pa)).filter (fun b => ¬ b ≤ X),
        ∑ e ∈ Finset.Icc 1 X, uniCharTerm Pa b e β K ε

/-! ## 3. The `b`-split of the mollified (pair) form

`Work.FIArea7.WUniOmega6Pull6Moll` (the off-diagonal-cut-free mollified pull-out sum, i.e. the
main term `Pull6Moll = uniModeSum`) carries the *explicit* divisibility guard `4be ∣ |Δ|`, which
is what the lattice count of *NOTES* §57.3 needs.  Its split at `b = X` is the form in which the
two halves are estimated. -/

/-- The `(b,e)`-sum of the pair form of the (17.10) main term, restricted to a set `s` of Möbius
levels `b`.  `Work.FIArea7.WUniOmega6Pull6Moll` is `s = Icc 1 (uniB Pa)`. -/
def WUniOmega6Pull6MollRange (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) (K : ℕ)
    (s : Finset ℕ) : ℂ :=
  2 * ∑ b ∈ s,
        ∑ e ∈ Finset.Icc 1 X,
          (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
            * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  (if Work.FIPlan.GaussCoprime z1 z2
                      ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then
                    (Work.FIArea7.reflSign z1 z2 : ℂ)
                      * omegaDetect (4 * b * e) e z1 z2
                      * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
                      * (betaPrime β z1 * star (betaPrime β z2))
                      * logFac6Series z1 z2 K
                   else 0)

/-- The `b ≤ X` half of the pair form. -/
def WUniOmega6Pull6MollLow (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) (K : ℕ) : ℂ :=
  WUniOmega6Pull6MollRange Pa X β K ((Finset.Icc 1 (uniB Pa)).filter (fun b => b ≤ X))

/-- The `X < b` half of the pair form — the levels absent from the paper's parametrisation, where
the effective modulus `4be` exceeds `4X²` (*NOTES* §57.2). -/
def WUniOmega6Pull6MollHigh (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) (K : ℕ) : ℂ :=
  WUniOmega6Pull6MollRange Pa X β K ((Finset.Icc 1 (uniB Pa)).filter (fun b => ¬ b ≤ X))

/-- **The `b`-split of the mollified form.** -/
theorem WUniOmega6Pull6Moll_eq_low_add_high (Pa : Work.FITop.Params) (X : ℕ)
    (β : GaussianInt → ℂ) (K : ℕ) :
    WUniOmega6Pull6Moll Pa X β K
      = WUniOmega6Pull6MollLow Pa X β K + WUniOmega6Pull6MollHigh Pa X β K := by
  have h := (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (uniB Pa)) (fun b => b ≤ X)
    (fun b => ∑ e ∈ Finset.Icc 1 X,
          (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
            * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
                  (if Work.FIPlan.GaussCoprime z1 z2
                      ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then
                    (Work.FIArea7.reflSign z1 z2 : ℂ)
                      * omegaDetect (4 * b * e) e z1 z2
                      * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
                      * (betaPrime β z1 * star (betaPrime β z2))
                      * logFac6Series z1 z2 K
                   else 0))).symm
  rw [WUniOmega6Pull6Moll, WUniOmega6Pull6MollLow, WUniOmega6Pull6MollHigh,
    WUniOmega6Pull6MollRange, WUniOmega6Pull6MollRange, h]
  ring

/-- **The `b`-split of the (17.10) main term.** -/
theorem WUniOmega6Pull6Char_eq_low_add_high (Pa : Work.FITop.Params) (X : ℕ)
    (β : GaussianInt → ℂ) (K : ℕ) (ε : GaussianInt → ℤ) :
    WUniOmega6Pull6Char Pa X β K ε
      = WUniOmega6Pull6CharLow Pa X β K ε + WUniOmega6Pull6CharHigh Pa X β K ε := by
  have h := (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 (uniB Pa)) (fun b => b ≤ X)
    (fun b => ∑ e ∈ Finset.Icc 1 X, uniCharTerm Pa b e β K ε)).symm
  rw [WUniOmega6Pull6Char, WUniOmega6Pull6CharLow, WUniOmega6Pull6CharHigh, h]
  ring

end

end Work.FIArea7
