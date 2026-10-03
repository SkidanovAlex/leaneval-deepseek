/-
# `Submission.Work.FIArea7.WBOmega` — the `ω`-form of the combined cut (`FI` (17.9))

*FI* §17 transforms the combined cut `W ∪ B` in four steps, all now proved in this directory:

1. reflect `d ↦ |∆|/(4d)` and expand `φ(m)/m = Σ_{b|m} μ(b)/b` — *FI* (17.1) — giving
   `WBcutExpanded` (`WcutExpand.lean`);
2. split the symbol of the complementary modulus, `(a | M/(4e)) = (a | M)(a | e)` — the
   square-factor rule `ReflectAlg.jacobiSym_eq_of_four_dvd`;
3. insert Lemma 17.1 in its general (mixed-sign, mod-4) form —
   `reflection_pair_betaPrime_general` — which turns `J(Re, M)·β_{z₁}β̄_{z₂}` into
   `tw·δ·i^{(r₂−r₁)/2}·J(|z₁|²,M)·β'_{z₁}β̄'_{z₂}`;
4. detect the congruence `4be ∣ ∆` by the rational classes `ω (mod 4be)`, replacing the symbol
   `(Re | e)` by `(Σ_ω (ω|e))·(N z₂ | e)` — `jacobiSym_div_four_mul_eq`, whose input is the
   orthogonality step `reflSymbol_mul_omegaSum`.

The result is exactly (17.9): the triple sum over `b`, `e` and the rational class `ω`, with the
weight `(ω|d)` (here `d = e`, the reflected small divisor) and the twisted coefficients `β'`.

`WBOmega` is the object (17.10) is derived from: it is the left-hand side of the Fourier
expansion over the characters of `(ℤ[i]/4be)^*`.
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FIArea7.ReflectAlg
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.reflection_pair_betaPrime_general
import Submission.Work.FIArea7.existsUnique_omega_of_dvd_delta
import Submission.Work.FIArea7.coprime_gnorm_absDelta
import Submission.Work.FIArea7.coprime_re_absDelta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

open Classical


/-- The `2`-adic correction `tw` of the (17.5)-insertion at the modulus `|∆(z₁,z₂)|`
(`(χ₂(Re(z̄₁z₂))·χ₂(|z₁|²))^{ν₂(|∆|)}`, the `tw` of `Work.FIArea7.reflection_pair_betaPrime_general`). -/
def twCorr (z1 z2 : GaussianInt) : ℤ :=
  (kronTwo ((star z1 * z2).re) * kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ))
    ^ ((Work.FIPlan.absDelta z1 z2).factorization 2)

/-- **The congruence detection of (17.9).**  Summed over the classes `ω` mod `Q`, the value
`(ω|e)` on the (unique) class with `z₁ ≡ ω z₂ (mod Q)`.  By `jacobiSym_div_four_mul_eq` this is
`(Re(z̄₁z₂)|e)/(N z₂|e)`. -/
def omegaDetect (Q e : ℕ) (z1 z2 : GaussianInt) : ℂ :=
  if hQ : Q = 0 then 0
  else
    haveI : NeZero Q := ⟨hQ⟩
    ∑ ω : ZMod Q,
      (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
          ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
        then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)

/-- **The `ω`-form of the inner sum of (17.9), per pair.**  `b` runs over the Möbius divisors of
`m = |∆|/(4e)`, `e` over the reflected small divisors `e ≤ X`, `4eX < |∆|` of the combined cut
`W ∪ B`, and `ω` over the rational classes mod `4be`; the weight is `(ω|e)` and the coefficients
are the twisted ones `β' = [z]β`. -/
def WBOmegaInner (X : ℕ) (z1 z2 : GaussianInt) (β : GaussianInt → ℂ) : ℂ :=
  ∑ b ∈ Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1),
    ∑ e ∈ (Finset.Icc 1 (Work.FIPlan.absDelta z1 z2 / 4 + 1)).filter
        (fun e => 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 ∧ e ≤ X
          ∧ 4 * e * X < Work.FIPlan.absDelta z1 z2),
      (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)
        * omegaDetect (4 * b * e) e z1 z2
        * (jacobiSym ((Work.FIPlan.gnorm z2 : ℕ) : ℤ) e : ℂ)
        * (twCorr z1 z2 : ℂ) * (reflSign z1 z2 : ℂ)
        * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
        * (jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2) : ℂ)
        * (betaPrime β z1 * star (betaPrime β z2))
        * (Work.FITop3.logFac z1 z2 : ℂ)

/-- **The `ω`-form of the combined cut `W ∪ B`** — the left-hand side of *FI* (17.10). -/
def WBOmega (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ) : ℂ :=
  2 * ∑ z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
        ∑ z2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa),
          (if Work.FIPlan.GaussCoprime z1 z2 then WBOmegaInner X z1 z2 β else 0)

end

end Work.FIArea7
