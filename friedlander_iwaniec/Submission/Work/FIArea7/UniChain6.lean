/-
# `Submission.Work.FIArea7.UniChain6` — the §17 chain for the *uniform* (paper's `W`) cut

`Work.FIArea7.WUni6` (the paper's sharp `W`, cut `|Δ| ≤ 4dX`) is decomposed by §17 exactly as
`Wcut + Bcut` is: reflect `d ↦ e = |Δ|/(4d)` and expand `φ(m)/m = Σ_{b∣m} μ(b)/b`.  This file
collects the *definitions* of the three objects of that chain —

* `WUniExpanded6` — the reflected, Möbius-expanded double sum
  (`WUni6 = WUniExpanded6` is `Work.FIArea7.WUni6_eq_WUniExpanded6`, proved in
  `UniExpanded6.lean` from `Work.FIArea7.WUni_inner_totient_expansion`);
* `WUniOmega6Inner` / `WUniOmega6` — the `ω`-form of (17.9): the reflected sum with the
  pair criterion `4be ∣ |Δ|` replaced by `omegaDetect (4be) e z₁ z₂` and the symbol of the
  reflected modulus replaced by the (17.5)-insertion `reflSign·i^{(r₂−r₁)/2}·β'_{z₁}β̄'_{z₂}`;
* `WUniOmega6Pull6` — the same sum with the `(b,e)`-sums **pulled outside** the pair sums, over
  the *uniform* ranges `b ≤ uniB Pa`, `e ≤ X` (this is the form on which (16.11)/(17.10) runs).

The difference from the two-cut objects (`WBOmega6Inner`, `WBOmega6`) is exactly that the filter
on `e` is `4be ∣ |Δ| ∧ e ≤ X` instead of `4be ∣ |Δ| ∧ e ≤ X ∧ 4eX < |Δ|`: the pair-dependent
condition `4eX < |Δ|` — the image of `X < d` under the reflection — is dropped, which is what
makes the reflected range *uniform* in the pair and hence ready for the §16 character expansion.

Also here: the round-6 sector bound `absDelta_le_sector6` (*FI* (6.2)), moved out of
`area7_6.lean` so that this chain does not depend on the `sorry` of the contract statement.
-/
import Mathlib
import Submission.Work.FIArea7.UniCut6
import Submission.Work.FIArea7.WBOmega6
import Submission.Work.FIArea4.absDelta_le_sector

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The sector bound (6.2) of the round-6 polar box -/

/-- ***FI* (6.2)/(5.12) for the round-6 polar box**: for `z₁, z₂` in the same polar box (5.14)
the determinant satisfies `|Δ(z₁,z₂)| ≤ 2πθ(1+θ)N`.  This is (6.2) for the round-6 box; it is
`Work.FIArea4.absDelta_le_sector` combined with the annulus bound `|z|² ≤ (1+θ)N`, and it is what
bounds the range of the Möbius divisors `b` in (17.9) (`4be ≤ |Δ|`). -/
theorem absDelta_le_sector6 (Pa : Work.FITop.Params) (φ : ℝ) {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    (Work.FIPlan.absDelta z1 z2 : ℝ) ≤ 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) := by
  have hbase := Work.FIArea4.absDelta_le_sector Pa φ h1 h2
  have hb1 : Real.sqrt ((Work.FIPlan.gnorm z1 : ℝ)) ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) :=
    Real.sqrt_le_sqrt h1.2.2.1
  have hb2 : Real.sqrt ((Work.FIPlan.gnorm z2 : ℝ)) ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) :=
    Real.sqrt_le_sqrt h2.2.2.1
  have hNN : (0 : ℝ) ≤ (1 + Pa.θ) * Pa.N := by
    have hθ : (0 : ℝ) ≤ Pa.θ := le_of_lt Pa.hθ0
    nlinarith [Pa.hN1]
  have hmul : Real.sqrt ((Work.FIPlan.gnorm z1 : ℝ)) * Real.sqrt ((Work.FIPlan.gnorm z2 : ℝ))
      ≤ (1 + Pa.θ) * Pa.N := by
    calc Real.sqrt ((Work.FIPlan.gnorm z1 : ℝ)) * Real.sqrt ((Work.FIPlan.gnorm z2 : ℝ))
        ≤ Real.sqrt ((1 + Pa.θ) * Pa.N) * Real.sqrt ((1 + Pa.θ) * Pa.N) :=
          mul_le_mul hb1 hb2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = (1 + Pa.θ) * Pa.N := Real.mul_self_sqrt hNN
  have hπ : (0 : ℝ) ≤ 2 * Real.pi * Pa.θ := by
    have hθ : (0 : ℝ) < Pa.θ := Pa.hθ0
    positivity
  calc (Work.FIPlan.absDelta z1 z2 : ℝ)
      ≤ 2 * Real.pi * Pa.θ * Real.sqrt ((Work.FIPlan.gnorm z1 : ℝ))
          * Real.sqrt ((Work.FIPlan.gnorm z2 : ℝ)) := hbase
    _ = 2 * Real.pi * Pa.θ * (Real.sqrt ((Work.FIPlan.gnorm z1 : ℝ))
          * Real.sqrt ((Work.FIPlan.gnorm z2 : ℝ))) := by ring
    _ ≤ 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) := mul_le_mul_of_nonneg_left hmul hπ

/-- The rounding of a class congruence: `SameClass8 z₁ z₂` is componentwise congruence mod 8. -/
theorem modEq_of_sameClass8 {z1 z2 : GaussianInt} (h : Work.FITop4.SameClass8 z1 z2) :
    z1.re ≡ z2.re [ZMOD 8] ∧ z1.im ≡ z2.im [ZMOD 8] := by
  have h1 : ((z1.re : ZMod 8), (z1.im : ZMod 8)) = ((z2.re : ZMod 8), (z2.im : ZMod 8)) := h
  refine ⟨?_, ?_⟩
  · exact (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.fst h1)
  · exact (ZMod.intCast_eq_intCast_iff _ _ _).mp (congrArg Prod.snd h1)

/-- The uniform bound on the Möbius divisors `b` of (17.9): since `4be ≤ |Δ| ≤ 2πθ(1+θ)N`
(`absDelta_le_sector6`), every *contributing* `b` satisfies `b ≤ 2πθ(1+θ)N/4`.  `uniB Pa` is that
bound rounded up. -/
def uniB (Pa : Work.FITop.Params) : ℕ :=
  Nat.ceil (2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4) + 1

/-- Every `b` with `4be ≤ |Δ|` for a pair of the polar box is `≤ uniB Pa`. -/
theorem le_uniB_of_four_mul_le_absDelta {Pa : Work.FITop.Params} {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2)
    {b e : ℕ} (he : 1 ≤ e) (h : 4 * b * e ≤ Work.FIPlan.absDelta z1 z2) : b ≤ uniB Pa := by
  have hsec := absDelta_le_sector6 Pa φ h1 h2
  have h4 : ((4 * b * e : ℕ) : ℝ) ≤ (Work.FIPlan.absDelta z1 z2 : ℝ) := by exact_mod_cast h
  have hb : (b : ℝ) ≤ 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4 := by
    have he1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    have h4e : (4 : ℝ) * (b : ℝ) * (e : ℝ) ≤ 2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) := by
      have : ((4 * b * e : ℕ) : ℝ) = 4 * (b : ℝ) * (e : ℝ) := by push_cast; ring
      linarith [h4, hsec]
    nlinarith [h4e, he1]
  have hbceil : (b : ℝ)
      ≤ ((Nat.ceil (2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4) : ℕ) : ℝ) :=
    le_trans hb (Nat.le_ceil _)
  have hb' : b ≤ Nat.ceil (2 * Real.pi * Pa.θ * ((1 + Pa.θ) * Pa.N) / 4) := by
    exact_mod_cast hbceil
  exact le_trans hb' (Nat.le_succ _)

/-! ## 2. The reflected, Möbius-expanded form of the uniform cut -/

/-- **The (17.1) double sum for the paper's cut `|Δ| ≤ 4dX`.**  The analogue of
`Work.FIArea7.WBcutExpanded6` with the union cut `X < d ∧ |Δ| ≤ 4dX` replaced by the paper's
cut `|Δ| ≤ 4dX` (no condition on `d`): the reflected sum over the small divisors `e ≤ X` with
`4be ∣ |Δ|`, at the ratio symbol of the reflected modulus `|Δ|/(4e)`.  `WUni6 = WUniExpanded6` is
`Work.FIArea7.WUni6_eq_WUniExpanded6`. -/
def WUniExpanded6 (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  2 * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          (if Work.FIPlan.GaussCoprime z1 z2 then
            (β z1 * star (β z2))
              * ((WUniInner X (fun d => Work.FITop4.ratioSym z1 z2 d)
                    (Work.FITop4.logFac6 z1 z2) (Work.FIPlan.absDelta z1 z2)) : ℂ)
           else 0)

/-! ## 3. The `ω`-form (17.9) of the uniform cut -/

/-- **The `ω`-form of the uniform cut, per pair.**  `WUniOmega6Inner` is `WBOmega6Inner` with the
`e`-filter `4be ∣ |Δ| ∧ e ≤ X ∧ 4eX < |Δ|` relaxed to `4be ∣ |Δ| ∧ e ≤ X`: the congruence
`4be ∣ Δ = Im(z̄₁z₂)` is detected by `omegaDetect (4be) e z₁ z₂` (the sum over the rational
classes `ω (mod 4be)` of the weight `(ω∣e)`), the symbol of the reflected modulus is replaced by
the Lemma-17.1 product `reflSign·i^{(r₂−r₁)/2}·(β'_{z₁}β̄'_{z₂})` of (17.5)+(17.8), and the
weight `(μ(b)/b)` and the logarithmic factor are as in (17.1). -/
def WUniOmega6Inner (X : ℕ) (z1 z2 : GaussianInt) (β : GaussianInt → ℂ) : ℂ :=
  ∑ b ∈ Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1),
    ∑ e ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
        (fun e => 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 ∧ e ≤ X),
      (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
        * (Work.FIArea7.reflSign z1 z2 : ℂ)
        * omegaDetect (4 * b * e) e z1 z2
        * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
        * (betaPrime β z1 * star (betaPrime β z2))
        * (Work.FITop4.logFac6 z1 z2 : ℂ)

/-- **The `ω`-form of the uniform cut** — the left-hand side of (17.10).  `WUni6 = WUniOmega6`
is `Work.FIArea7.WUni6_eq_WUniOmega6`. -/
def WUniOmega6 (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  2 * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          (if Work.FIPlan.GaussCoprime z1 z2 then WUniOmega6Inner X z1 z2 β else 0)

/-! ## 4. The pulled-out form: the `(b,e)`-sums outside the pair sums -/

/-- **The `ω`-form with the `(b,e)`-sums pulled outside the pair sums.**  The `e`-range is the
*uniform* `Icc 1 X` and the `b`-range is the uniform `Icc 1 (uniB Pa)`
(`le_uniB_of_four_mul_le_absDelta`: only `b ≤ uniB Pa` can occur on the support), while the
pair criterion `4be ∣ |Δ|` is kept explicitly.  This is the form in which (16.11)/(17.10) is
applied: for fixed `(b,e)` the inner sum is over a *congruence* condition, hence a square of
`z`-sums (`Work.FIArea7.section16_omegaDetect_expansion`).
`WUniOmega6 = WUniOmega6Pull6` is `Work.FIArea7.WUniOmega6_eq_WUniOmega6Pull6`. -/
def WUniOmega6Pull6 (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  2 * ∑ b ∈ Finset.Icc 1 (uniB Pa),
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
                      * (Work.FITop4.logFac6 z1 z2 : ℂ)
                   else 0)

end

end Work.FIArea7
