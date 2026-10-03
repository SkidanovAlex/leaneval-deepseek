/-
# Round-6 §15: the per-modulus vocabulary of `pDng6_le_EvarG`

This module collects the definitions (and their elementary bounds) used by the round-6 per-modulus
bound `Work.FIArea4.A6psi.pDng6_le_EvarG`: the round-6 summand `ssTerm6`, the `z`-side /
`w`-side / class-Cauchy–Schwarz strata `ssZ6`/`ssW6`/`ssT6`, and the two sums
`stratumSumE6`/`diagSum6` of the fibre decomposition.

The *frozen* (§15) counterparts live in `Submission.Work.FIArea4.S15red.stratumSumE_le_EvarG`
(namespace `Work.FIArea4.S15red.SSE`) and are reused verbatim wherever the round-6 symbol does
not intervene.
-/
import Mathlib
import Submission.Work.FIArea4.A6psi.Defs
import Submission.Work.FIArea4.S15red.stratumSumE_le_EvarG
import Submission.Work.FIArea4.S15theta_phase_factor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.A6psi

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The round-6 summand -/

/-- The single summand of the round-6 pair sum, separated into the `d`-factor, *FI*'s ratio
symbol and the angular/phase factor. -/
def ssTerm6 (X j d : ℕ) (u t : ℝ) (ℓ : ℤ) (z1 z2 : GaussianInt) : ℂ :=
  ((((Nat.totient d : ℝ) / (d : ℝ) : ℝ)) : ℂ)
    * (((Work.FIArea7.ratioSym z1 z2 d : ℤ)) : ℂ)
    * (Work.FIArea4.S15theta ℓ z1 z2 * Work.FIArea4.S15phase X j u t ((z1, z2), d))

/-- `S15coef6` in terms of `ssTerm6`. -/
lemma summand_eq6 (X j d : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ) (z1 z2 : GaussianInt) :
    S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
      * Work.FIArea4.S15phase X j u t ((z1, z2), d)
    = 2 * (β z1 * star (β z2)) * ssTerm6 X j d u t ℓ z1 z2 := by
  unfold S15coef6 S15w6 ssTerm6
  ring

/-- The coefficient `S15coef6` vanishes when one of the two coefficients does. -/
lemma S15coef6_eq_zero_of (β : GaussianInt → ℂ) (d : ℕ) {z1 z2 : GaussianInt}
    (h : β z1 = 0 ∨ β z2 = 0) : S15coef6 β ((z1, z2), d) = 0 := by
  rcases h with h | h <;> simp [S15coef6, h]

/-- `ratioSym` has modulus at most `1`. -/
lemma norm_ratioSym_le (z1 z2 : GaussianInt) (d : ℕ) :
    ‖(((Work.FIArea7.ratioSym z1 z2 d : ℤ)) : ℂ)‖ ≤ 1 := by
  unfold Work.FIArea7.ratioSym
  rcases jacobiSym.trichotomy _ _ with h | h | h <;> rw [h] <;> norm_num

/-- `S15w6` has modulus at most `1`. -/
lemma norm_S15w6_le (i : Work.FIArea4.S15Id) : ‖S15w6 i‖ ≤ 1 := by
  have hsq : Complex.normSq (S15w6 i) ≤ 1 := by
    rw [S15w6, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_intCast]
    have htot : ((Nat.totient i.2 : ℝ)/(i.2:ℝ))^2 ≤ 1 := by
      rcases Nat.eq_zero_or_pos i.2 with h|h
      · rw [h]; simp [Nat.totient_zero]
      · have hle : (Nat.totient i.2 : ℝ) ≤ (i.2 : ℝ) := by exact_mod_cast Nat.totient_le i.2
        have hpos : (0:ℝ) < (i.2:ℝ) := by exact_mod_cast h
        have hnn : (0:ℝ) ≤ (Nat.totient i.2:ℝ) := Nat.cast_nonneg _
        rw [div_pow, div_le_one (by positivity)]
        nlinarith
    have hjac : ((Work.FIArea7.ratioSym i.1.1 i.1.2 i.2 : ℤ) : ℝ) *
        ((Work.FIArea7.ratioSym i.1.1 i.1.2 i.2 : ℤ) : ℝ) ≤ 1 := by
      unfold Work.FIArea7.ratioSym
      rcases jacobiSym.trichotomy _ _ with h|h|h <;> rw [h] <;> norm_num
    have hnn : (0:ℝ) ≤ ((Nat.totient i.2 : ℝ)/(i.2:ℝ))^2 := sq_nonneg _
    nlinarith [htot, hjac, hnn]
  have h2 : ‖S15w6 i‖ ^ 2 ≤ 1 := by
    rw [← Complex.normSq_eq_norm_sq]; exact hsq
  nlinarith [norm_nonneg (S15w6 i)]

/-- `S15coef6` has modulus at most `2 ‖β z₁‖ ‖β z₂‖`. -/
lemma norm_S15coef6_le (β : GaussianInt → ℂ) (i : Work.FIArea4.S15Id) :
    ‖S15coef6 β i‖ ≤ 2 * ‖β i.1.1‖ * ‖β i.1.2‖ := by
  have hw := norm_S15w6_le i
  have hb : ‖(2:ℂ) * (β i.1.1 * star (β i.1.2)) * S15w6 i‖
      = 2 * (‖β i.1.1‖ * ‖β i.1.2‖) * ‖S15w6 i‖ := by
    rw [norm_mul, norm_mul, norm_mul, norm_star]; norm_num
  rw [S15coef6, hb]
  calc 2 * (‖β i.1.1‖ * ‖β i.1.2‖) * ‖S15w6 i‖
      ≤ 2 * (‖β i.1.1‖ * ‖β i.1.2‖) * 1 := by
        refine mul_le_mul_of_nonneg_left hw (by positivity)
    _ = 2 * ‖β i.1.1‖ * ‖β i.1.2‖ := by ring

/-! ## 2. The three strata of the round-6 per-modulus sum -/

/-- The `z`-side round-6 stratum summand. -/
def ssZ6 (X j d e : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (z1 z2 : GaussianInt) : ℂ :=
  if Nat.gcd d z1.re.natAbs = e ∧ X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
    (β z1 * star (β z2)) * ssTerm6 X j d u t ℓ z1 z2 else 0

/-- The `w`-side round-6 stratum summand (before the class factorisation). -/
def ssW6 (X j d e : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ) (w1 w2 : GaussianInt) : ℂ :=
  if Nat.gcd d (Work.FIArea4.scalePt e w1).re.natAbs = e ∧ X < d
      ∧ 4 * d ∣ Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2) then
    (β (Work.FIArea4.scalePt e w1) * star (β (Work.FIArea4.scalePt e w2)))
      * ssTerm6 X j d u t ℓ (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2) else 0

/-- The class-Cauchy–Schwarz form of the round-6 stratum summand: the class factor is the
*square* `ssFac²` of the frozen class factor `ssFac` (the round-6 ratio symbol cancels one copy of
`(e²+a²|d')` against the twist `(|z₁|²|d)` and leaves the other). -/
def ssT6 (Pa : Work.FITop.Params) (X j d e : ℕ) (β : GaussianInt → ℂ) (u t : ℝ) (ℓ : ℤ)
    (w1 w2 : GaussianInt) : ℂ :=
  if (Work.FIPlan.Delta w1 w2 : ZMod (4 * (d / e))) = 0 then
    (Work.FIArea4.S15red.SSE.ssConst X j d t * (Work.FIArea4.S15red.SSE.ssFac e (d / e)
        ((w1.im : ZMod (4 * (d / e))) * ((w1.re : ZMod (4 * (d / e))))⁻¹)) ^ 2)
      * (Work.FIArea4.S15red.SSE.ssU Pa e (d / e) β u t ℓ w1
          * star (Work.FIArea4.S15red.SSE.ssV Pa e (d / e) β u t ℓ w2))
  else 0

/-! ## 3. The two sums of the fibre decomposition -/

/-- **The `e`-stratum of the round-6 per-modulus sum**: the pairs `(z₁,z₂)` of the box with
`X < d`, `4d ∣ |Δ(z₁,z₂)|` and `(d, Re z₁) = e`, weighted by the round-6 summand. -/
def stratumSumE6 (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ)
    (u t : ℝ) (e : ℕ) : ℂ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if Nat.gcd d z1.re.natAbs = e ∧ X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2 then
      S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
        * Work.FIArea4.S15phase X j u t ((z1, z2), d)
     else 0)

/-- **The `Δ = 0` part of the round-6 per-modulus sum.** -/
def diagSum6 (Pa : Work.FITop.Params) (X j d : ℕ) (β : GaussianInt → ℂ) (ℓ : ℤ)
    (u t : ℝ) : ℂ :=
  ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
    (if Work.FIPlan.absDelta z1 z2 = 0 ∧ X < d then
      S15coef6 β ((z1, z2), d) * Work.FIArea4.S15theta ℓ z1 z2
        * Work.FIArea4.S15phase X j u t ((z1, z2), d)
     else 0)

end

end Work.FIArea4.A6psi
