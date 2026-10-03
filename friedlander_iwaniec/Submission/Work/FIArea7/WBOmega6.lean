/-
# `Submission.Work.FIArea7.WBOmega6` — the `ω`-form of the combined cut at the ratio symbol

*FI* §17 transforms the combined cut `W ∪ B` of (10.17) in four steps.  At the round-6 objects
(`Work.FITop4.Tcut`, whose `d`-sum carries the *ratio* symbol `Work.FITop4.ratioSym z₁ z₂ d =
(z₂/z₁|d)` of (8.14)/(10.13)) the chain is

1. the (17.1) reflection `d ↦ |Δ|/(4d)` together with the Möbius expansion
   `φ(m)/m = Σ_{b∣m} μ(b)/b` — `Work.FIArea7.Wcut6_add_Bcut6_eq_WBcutExpanded6`, giving
   `WBcutExpandedInner X (fun d => ratioSym z₁ z₂ d) logFac6 |Δ|`;
2. the square-factor rule `ratioSym (d·t²) = ratioSym d` (`Work.FIArea7.ratioSym_mul_sq`) and
   multiplicativity in the modulus (`Work.FIArea7.ratioSym_mul`), which split the symbol of the
   reflected modulus `|Δ|/(4e)` into the symbol of `|Δ|` and the symbol of the *small* modulus
   `e ≤ X`;
3. *FI* Lemma 17.1 (17.5) in the ratio form `ratioSym z₁ z₂ |Δ| = reflSign·(s₁/|r₁|)(s₂/|r₂|)`
   (`Work.FIArea7.ratioSym_absDelta_eq_general`), which replaces that symbol, together with the
   coefficients, by the twisted coefficients `β' = [z]β` of (17.8);
4. the detection of the congruence `4be ∣ Δ` by the rational classes `ω (mod 4be)`
   (`Work.FIArea7.existsUnique_omega_of_dvd_delta`) with the weight `(ω|e)`
   (`Work.FIArea7.ratioSym_eq_jacobiSym_omega`), collected in `Work.FIArea7.omegaDetect`.

The result is exactly (17.9): a triple sum over the Möbius divisors `b`, the reflected small
divisors `e ≤ X` and the rational classes `ω (mod 4be)`.

**Difference from the round-3 object `Work.FIArea7.WBOmegaInner`.**  At the ratio symbol the class
character occurs exactly *once* — the small-modulus symbol *is* `(ω|e)` — so `WBOmega6Inner`
carries only the factors `(μ(b)/b)·reflSign·omegaDetect (4be) e z₁ z₂·i^{(r₂-r₁)/2}·(β'β̄')·logFac6`,
whereas the frozen `WBOmegaInner` carries, besides those, the two extra symbols `(N z₂|e)`,
`(N z₁||Δ|)` and the `2`-adic correction `twCorr`.  In particular the weight of the character
expansion (17.10) is the *single* class character `(ω|e)`
(`Work.FIArea7.sum_omegaDetect_eq_ratWeight`), which is what *FI* §16 consumes.
-/
import Mathlib
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea7.WBOmega
import Submission.Work.FIArea7.ratioSym_mul_sq
import Submission.Work.FIArea7.ratioSym_mul
import Submission.Work.FIArea7.ratioSym_eq_jacobiSym_omega
import Submission.Work.FIArea7.twCorr_eq_one_of_sameClass8
import Submission.Work.FIArea7.ratioSym_absDelta_eq_general
import Submission.Work.FIArea7.existsUnique_omega_of_dvd_delta
import Submission.Work.FIArea7.coprime_gnorm_absDelta
import Submission.Work.FIArea7.coprime_re_absDelta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The `ω`-form of the inner sum, per pair -/

/-- **The `ω`-form of the inner sum of (17.9) at the ratio symbol, per pair.**  `b` runs over the
Möbius divisors of `m = |Δ|/(4e)`, `e` over the reflected small divisors `e ≤ X`, `4eX < |Δ|` of
the combined cut `W ∪ B`, and `ω` over the rational classes mod `4be` (through `omegaDetect`); the
weight is the single class character `(ω|e)` and the coefficients are the twisted ones
`β' = [z]β`.  The mixed-sign correction `reflSign z₁ z₂` is present because the round-6 polar box
(5.14) has arbitrary `φ` and may straddle the imaginary axis; it is `1` whenever `0 < r₁r₂`. -/
def WBOmega6Inner (X : ℕ) (z1 z2 : GaussianInt) (β : GaussianInt → ℂ) : ℂ :=
  ∑ b ∈ Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1),
    ∑ e ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
        (fun e => 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 ∧ e ≤ X
          ∧ 4 * e * X < Work.FIPlan.absDelta z1 z2),
      (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
        * (Work.FIArea7.reflSign z1 z2 : ℂ)
        * omegaDetect (4 * b * e) e z1 z2
        * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
        * (betaPrime β z1 * star (betaPrime β z2))
        * (Work.FITop4.logFac6 z1 z2 : ℂ)

/-- **The `ω`-form of the combined cut `W ∪ B` at the ratio symbol** — the left-hand side of
*FI* (17.10). -/
def WBOmega6 (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  2 * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          (if Work.FIPlan.GaussCoprime z1 z2 then WBOmega6Inner X z1 z2 β else 0)

/-! ## 2. Two elementary ingredients of the pair identity -/

/-- `omegaDetect` at a nonzero modulus is the sum over the classes `ω (mod Q)` of the weight
`(ω|e)`, restricted to the congruence `z₁ ≡ ω z₂ (mod Q)`. -/
lemma omegaDetect_unfold6 (Q e : ℕ) [NeZero Q] (z1 z2 : GaussianInt) :
    omegaDetect Q e z1 z2
      = ∑ ω : ZMod Q, (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
          ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
        then (jacobiSym (ω.val : ℤ) e : ℂ) else 0) := by
  rw [omegaDetect, dif_neg (NeZero.ne Q)]

/-- When the congruence `z₁ ≡ ω z₂ (mod Q)` has the unique solution `ω₀`, the detection sum
`omegaDetect` collapses to the single weight `(ω₀|e)`.  This is the form in which the pair
identity of (17.9) consumes the `ω`-sum: the symbol of the small modulus `e` *is* that weight. -/
lemma omegaDetect_eq_of_unique (Q e : ℕ) [NeZero Q] (z1 z2 : GaussianInt) {ω₀ : ZMod Q}
    (huniq : ∀ ω : ZMod Q, (((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
        ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))) ↔ ω = ω₀) :
    omegaDetect Q e z1 z2 = (jacobiSym (ω₀.val : ℤ) e : ℂ) := by
  rw [omegaDetect_unfold6]
  have hstep : ∀ ω : ZMod Q,
      (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
          ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
        then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)
      = (if ω = ω₀ then (jacobiSym (ω.val : ℤ) e : ℂ) else 0) := by
    intro ω
    by_cases h : ω = ω₀
    · rw [if_pos ((huniq ω).mpr h), if_pos h]
    · rw [if_neg (fun hc => h ((huniq ω).mp hc)), if_neg h]
  rw [Finset.sum_congr rfl (fun ω _ => hstep ω), Finset.sum_ite_eq']
  simp

/-- **The algebraic core of the (17.5) insertion at the ratio symbol**: on primary `z₁, z₂` whose
imaginary parts are coprime to their real parts, the product of the two `JKCoeff`-values, applied
to `β_{z₁}β̄_{z₂}`, is the twisted pair `β'_{z₁}β̄'_{z₂}` up to the power of `i` of the
Jacobi–Kubota symbol (`Work.FIArea7.jksym_mul_star`); no hypothesis on the *size* of `Δ`, on
squarefreeness or on coprimality is used. -/
lemma jkcoeff_pair_mul (z1 z2 : GaussianInt) (β : GaussianInt → ℂ) :
    ((jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs : ℤ) : ℂ)
        * (β z1 * star (β z2))
      = Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
        * (betaPrime β z1 * star (betaPrime β z2)) := by
  have hbp : betaPrime β z1 * star (betaPrime β z2)
      = Complex.I ^ (((z1.re - 1) / 2 : ℤ) - ((z2.re - 1) / 2 : ℤ))
        * (JKCoeff z1 * JKCoeff z2) * (β z1 * star (β z2)) := by
    rw [betaPrime, betaPrime, star_mul]
    rw [show JKSym z1 * β z1 * (star (β z2) * star (JKSym z2))
        = (JKSym z1 * star (JKSym z2)) * (β z1 * star (β z2)) by ring]
    rw [jksym_mul_star]
  have hJK : (JKCoeff z1 * JKCoeff z2 : ℂ)
      = ((jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs : ℤ) : ℂ) := by
    rw [JKCoeff, JKCoeff]; push_cast; ring
  have hIprod : Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
      * Complex.I ^ (((z1.re - 1) / 2 : ℤ) - ((z2.re - 1) / 2 : ℤ)) = 1 := by
    rw [← zpow_add₀ Complex.I_ne_zero]
    have hz : (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
        + (((z1.re - 1) / 2 : ℤ) - ((z2.re - 1) / 2 : ℤ)) = 0 := by ring
    rw [hz, zpow_zero]
  rw [hbp, hJK]
  rw [show Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
        * (Complex.I ^ (((z1.re - 1) / 2 : ℤ) - ((z2.re - 1) / 2 : ℤ))
          * ((jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs : ℤ) : ℂ)
          * (β z1 * star (β z2)))
      = (Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
          * Complex.I ^ (((z1.re - 1) / 2 : ℤ) - ((z2.re - 1) / 2 : ℤ)))
        * (((jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs : ℤ) : ℂ)
          * (β z1 * star (β z2))) by ring]
  rw [hIprod, one_mul]

/-- **The (17.5)+(17.8) insertion at the ratio symbol, general sign.**  Under the source's side
conditions (17.2)–(17.4) in the form in which the round-6 objects supply them — primarity,
squarefree norms, coprimality, `z₁ ≡ z₂ (mod 8)`, `r_i ≠ 0`, `Δ ≠ 0` — the ratio symbol of the
large modulus acts on the coefficient pair as the mixed-sign correction, the Kubota power of `i`
and the twisted pair:

  `(z₂/z₁||Δ|)·β_{z₁}β̄_{z₂} = reflSign·i^{(r₂-r₁)/2}·β'_{z₁}β̄'_{z₂}`,

with `β' = [z]β`.  This is `Work.FIArea7.ratioSym_absDelta_eq_general` (Lemma 17.1 in ratio form)
followed by `Work.FIArea7.jkcoeff_pair_mul`. -/
theorem reflection_pair_betaPrime6_general (z1 z2 : GaussianInt) (β : GaussianInt → ℂ)
    (hP1 : Work.FIPlan.IsPrimary z1) (hP2 : Work.FIPlan.IsPrimary z2)
    (hs1 : Squarefree (Work.FIPlan.gnorm z1)) (hs2 : Squarefree (Work.FIPlan.gnorm z2))
    (hc : IsCoprime z1 z2)
    (hcc : IsCoprime ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ))
    (h8r : z1.re ≡ z2.re [ZMOD 8]) (h8i : z1.im ≡ z2.im [ZMOD 8])
    (hr1 : z1.re ≠ 0) (hr2 : z2.re ≠ 0) (hD : 0 < Work.FIPlan.absDelta z1 z2) :
    (Work.FIArea7.ratioSym z1 z2 (Work.FIPlan.absDelta z1 z2) : ℂ) * (β z1 * star (β z2))
      = (Work.FIArea7.reflSign z1 z2 : ℂ)
        * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
        * (betaPrime β z1 * star (betaPrime β z2)) := by
  have htw : Work.FIArea7.twCorr z1 z2 = 1 :=
    Work.FIArea7.twCorr_eq_one_of_sameClass8 z1 z2 hP1 hP2 h8r h8i
  have h := Work.FIArea7.ratioSym_absDelta_eq_general z1 z2 hP1 hP2 hs1 hs2 hc hcc h8r h8i htw
    hr1 hr2 hD
  have h1 : (Work.FIArea7.ratioSym z1 z2 (Work.FIPlan.absDelta z1 z2) : ℂ)
      = (Work.FIArea7.reflSign z1 z2 : ℂ)
        * ((jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs : ℤ) : ℂ) := by
    rw [h]; push_cast; ring
  rw [h1]
  rw [show (Work.FIArea7.reflSign z1 z2 : ℂ)
        * ((jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs : ℤ) : ℂ)
        * (β z1 * star (β z2))
      = (Work.FIArea7.reflSign z1 z2 : ℂ)
        * (((jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs : ℤ) : ℂ)
          * (β z1 * star (β z2))) by ring]
  rw [jkcoeff_pair_mul]
  ring

end

end Work.FIArea7
