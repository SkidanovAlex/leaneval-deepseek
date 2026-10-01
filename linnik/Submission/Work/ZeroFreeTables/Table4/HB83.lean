/-
# ZeroFreeTables/Table4/HB83 — HB Lemma 8.3

This file proves `Work.ZeroFreeTables.HBLemma8_3`, the `P₃` engine of Heath-Brown's
Table 4 (HB Lemma 8.3, p. 42; see `Table4Defs.lean` for the statement and provenance).

Layer 1 (below): the elementary real-variable content -- the explicit value of
`Re P₃(α/(β+it))`, HB's comparison `Re P₃(α/(β+it)) ⋛ (8/3)(αβ/(β²+t²))³` according as
`β ⋛ α`, the positivity `Re P₃ ≥ 0` for `β ≥ α` (HB (4.11)), the `A₁`-bracket
monotonicity giving `A ≥ 0` and `B ≥ 0` from condition (8.6), the boundary case
`λ₁ ≥ 15`, and the final rearrangement into `p83`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Table4Defs
import Submission.Work.ZeroFreeTables.Table4.Engine8A
import Submission.Work.ZeroFreeTables.Table4.HB83Aux
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.P3.DefsL
import Submission.Work.ZeroFreeTables.P9.Defs
import Submission.Work.ZeroFreeTables.P9.HbCombinationL_nonneg
import Submission.Work.ZeroFreeTables.P9.invNearSum_eq_tsum
import Submission.Work.ZeroFreeTables.P9.prim.SigmaP3L_eq_moments
import Submission.Work.ZeroFreeTables.P9.prim.iteratedDeriv_logDeriv_re
import Submission.Work.ZeroFreeTables.P9.lDiffExplicit_gen
import Submission.Work.ZeroFreeTables.P9.zeroSum_invSq_tsum
import Submission.Work.ZeroFreeTables.P3Pos
import Submission.Work.LinnikAreas.FarRepel.zeroMult_eq_analyticOrderNatAt_of_isPrimitive
import Submission.Work.LinnikAreas.l31free.lemma3_1_free_gen_real
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Work.ZeroFreeTables.Table4.invSqSum_le
import Submission.Work.ZeroFreeTables.Table4.trivSeries_le
import Submission.Work.ZeroFreeTables.Table4.zeroMult_conj
import Submission.Work.ZeroFreeTables.Table4.point_bound83
import Submission.Work.ZeroFreeTables.Table4.principal_bound_clean
import Submission.Work.ZeroFreeTables.Table4.zeroMult_changeLevel
import Submission.Work.ZeroFreeTables.Table4.SigmaP3L_primitive_le
import Submission.Work.ZeroFreeTables.Table4.error_budget
import Submission.Work.ZeroFreeTables.Table4.loglogPow4_le_mul
import Submission.Work.LinnikAreas.boxMaxZero

open Work.LinnikContract
open Complex DirichletCharacter
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.Table4

open Work.ZeroFreeTables

/-! ## The explicit value of `Re P₃(α/(β+it))` -/

/-- `Re P₃(α/(β+it))`: the near-zero weight of HB §8.2. -/
def P3AB (α β t : ℝ) : ℝ := (P3 ((α : ℂ) / ((β : ℂ) + (t : ℂ) * Complex.I))).re

theorem P3AB_eq (α β t : ℝ) (hβ : 0 < β) :
    P3AB α β t
      = α * β / (β ^ 2 + t ^ 2) + α ^ 2 * (β ^ 2 - t ^ 2) / (β ^ 2 + t ^ 2) ^ 2
        + (2 / 3) * α ^ 3 * (β ^ 3 - 3 * β * t ^ 2) / (β ^ 2 + t ^ 2) ^ 3 := by
  have hD : β ^ 2 + t ^ 2 ≠ 0 := by positivity
  set w : ℂ := (α : ℂ) / ((β : ℂ) + (t : ℂ) * Complex.I) with hw
  have hre : w.re = α * β / (β ^ 2 + t ^ 2) := by
    rw [hw]
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply]
    ring
  have him : w.im = -(α * t / (β ^ 2 + t ^ 2)) := by
    rw [hw]
    simp only [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply]
    ring
  have h2re : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by rw [pow_two, Complex.mul_re]; ring
  have h2im : (w ^ 2).im = 2 * w.re * w.im := by rw [pow_two, Complex.mul_im]; ring
  have h3re : (w ^ 3).re = w.re ^ 3 - 3 * w.re * w.im ^ 2 := by
    rw [show w ^ 3 = w ^ 2 * w by ring, Complex.mul_re, h2re, h2im]; ring
  have hval : (P3 w).re
      = w.re + (w.re ^ 2 - w.im ^ 2) + (2 / 3) * (w.re ^ 3 - 3 * w.re * w.im ^ 2) := by
    rw [P3]
    simp only [Complex.add_re, Complex.mul_re]
    rw [h2re, h3re]
    norm_num
  show (P3 w).re = _
  rw [hval, hre, him]
  field_simp

theorem P3AB_sub (α β t : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    P3AB α β t - (8 / 3) * (α * β / (β ^ 2 + t ^ 2)) ^ 3
      = (β - α) * (α * β ^ 3 * (β + 2 * α) + 2 * α * β * t ^ 2 * (β + α) + α * t ^ 4)
          / (β ^ 2 + t ^ 2) ^ 3 := by
  rw [P3AB_eq α β t hβ]
  field_simp
  ring

theorem bracket_nonneg (α β t : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    0 ≤ α * β ^ 3 * (β + 2 * α) + 2 * α * β * t ^ 2 * (β + α) + α * t ^ 4 := by
  have h1 : 0 ≤ α * β ^ 3 * (β + 2 * α) := by positivity
  have h2 : 0 ≤ 2 * α * β * t ^ 2 * (β + α) := by positivity
  have h3 : 0 ≤ α * t ^ 4 := by positivity
  linarith

/-- **HB's comparison, positive side** (HB §8.2): for `0 < α ≤ β`,
`Re P₃(α/(β+it)) ≥ (8/3)(αβ/(β²+t²))³`. -/
theorem P3AB_ge (α β t : ℝ) (hα : 0 < α) (hβ : 0 < β) (h : α ≤ β) :
    (8 / 3) * (α * β / (β ^ 2 + t ^ 2)) ^ 3 ≤ P3AB α β t := by
  have hD : 0 < (β ^ 2 + t ^ 2) ^ 3 := by positivity
  have h1 : 0 ≤ (β - α) * (α * β ^ 3 * (β + 2 * α) + 2 * α * β * t ^ 2 * (β + α) + α * t ^ 4)
      / (β ^ 2 + t ^ 2) ^ 3 := by
    apply div_nonneg _ hD.le
    exact mul_nonneg (by linarith) (bracket_nonneg α β t hα hβ)
  linarith [P3AB_sub α β t hα hβ, h1]

/-- **HB's comparison, negative side**: for `0 < β ≤ α`,
`Re P₃(α/(β+it)) ≤ (8/3)(αβ/(β²+t²))³`. -/
theorem P3AB_le (α β t : ℝ) (hα : 0 < α) (hβ : 0 < β) (h : β ≤ α) :
    P3AB α β t ≤ (8 / 3) * (α * β / (β ^ 2 + t ^ 2)) ^ 3 := by
  have hD : 0 < (β ^ 2 + t ^ 2) ^ 3 := by positivity
  have h1 : (β - α) * (α * β ^ 3 * (β + 2 * α) + 2 * α * β * t ^ 2 * (β + α) + α * t ^ 4)
      / (β ^ 2 + t ^ 2) ^ 3 ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hD.le
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (bracket_nonneg α β t hα hβ)
  linarith [P3AB_sub α β t hα hβ, h1]

/-- **HB (4.11)-type positivity** (the dropping rule): for `0 < α ≤ β`,
`0 ≤ Re P₃(α/(β+it))`. -/
theorem P3AB_nonneg (α β t : ℝ) (hα : 0 < α) (hβ : 0 < β) (h : α ≤ β) :
    0 ≤ P3AB α β t := by
  have h1 : 0 ≤ (8 / 3) * (α * β / (β ^ 2 + t ^ 2)) ^ 3 := by positivity
  linarith [P3AB_ge α β t hα hβ h]

theorem P3_ofReal (u : ℝ) : P3 ((u : ℂ)) = ((P3R u : ℝ) : ℂ) := by
  unfold P3 P3R
  push_cast
  ring

/-- The boundary value: `P3AB α β 0 = P3R (α/β)`. -/
theorem P3AB_zero (α β : ℝ) : P3AB α β 0 = P3R (α / β) := by
  unfold P3AB
  rw [show ((α : ℂ) / ((β : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) = (((α / β : ℝ)) : ℂ) by
    push_cast; ring]
  rw [P3_ofReal]
  simp

/-- **Evenness of `P3AB` in `t`** (for `0 < β`).  In the explicit formula `P3AB_eq` the
variable `t` occurs only through `t ^ 2`. -/
theorem P3AB_neg (α β t : ℝ) (hβ : 0 < β) : P3AB α β (-t) = P3AB α β t := by
  rw [P3AB_eq α β (-t) hβ, P3AB_eq α β t hβ]
  ring

/-- `Re P₃(α/((s-u)L))` in the `P3AB` normal form: `β = (Re s - Re u)L`, `t = (Im s - Im u)L`. -/
theorem P3_div_eq_P3AB (α L : ℝ) (s u : ℂ) :
    (P3 (α / ((s - u) * (L : ℂ)))).re
      = P3AB α ((s.re - u.re) * L) ((s.im - u.im) * L) := by
  have h : ((s - u) * (L : ℂ))
      = ((((s.re - u.re) * L : ℝ)) : ℂ) + ((((s.im - u.im) * L : ℝ)) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  unfold P3AB
  rw [h]

/-! ## The bracket `A₁`, and `A ≥ 0`, `B ≥ 0` -/

theorem bracket_le (a lam mu : ℝ) (ha : 0 < a) (hlam : 0 ≤ lam) :
    a ^ 6 / (a + lam) ^ 3
      ≤ (a + lam) ^ 3 * (a ^ 2 + mu ^ 2) ^ 3 / ((a + lam) ^ 2 + mu ^ 2) ^ 3 := by
  have hD : 0 < (a + lam) ^ 2 + mu ^ 2 := by positivity
  have ha2 : a ^ 2 ≤ (a + lam) ^ 2 := by nlinarith
  have hkey : a ^ 2 * ((a + lam) ^ 2 + mu ^ 2) ≤ (a ^ 2 + mu ^ 2) * (a + lam) ^ 2 := by
    have := mul_le_mul_of_nonneg_left ha2 (sq_nonneg mu)
    nlinarith [this]
  have h3 : (a ^ 2 * ((a + lam) ^ 2 + mu ^ 2)) ^ 3
      ≤ ((a ^ 2 + mu ^ 2) * (a + lam) ^ 2) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hkey 3
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (a + lam) ^ 3) (by positivity : (0:ℝ) < ((a+lam)^2+mu^2)^3)]
  calc a ^ 6 * (((a + lam) ^ 2 + mu ^ 2) ^ 3)
      = (a ^ 2 * ((a + lam) ^ 2 + mu ^ 2)) ^ 3 := by ring
    _ ≤ ((a ^ 2 + mu ^ 2) * (a + lam) ^ 2) ^ 3 := h3
    _ = (a + lam) ^ 3 * (a ^ 2 + mu ^ 2) ^ 3 * (a + lam) ^ 3 := by ring

/-- Elementary consequence of (8.6). -/
theorem cond86_key {a lam₁ lam₀ : ℝ} (ha : 0 < a) (h : cond86 lam₁ lam₀ a) :
    0 ≤ a ^ 6 / (a + lam₀) ^ 3 + a ^ 6 / (a + lam₁) ^ 3 - a ^ 3 := by
  have h1 : 1 / a ^ 3 ≤ 1 / (a + lam₀) ^ 3 + 1 / (a + lam₁) ^ 3 := h
  have h2 : a ^ 6 * (1 / a ^ 3) ≤ a ^ 6 * (1 / (a + lam₀) ^ 3 + 1 / (a + lam₁) ^ 3) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : a ^ 6 * (1 / a ^ 3) = a ^ 3 := by field_simp
  have h4 : a ^ 6 * (1 / (a + lam₀) ^ 3 + 1 / (a + lam₁) ^ 3)
      = a ^ 6 / (a + lam₀) ^ 3 + a ^ 6 / (a + lam₁) ^ 3 := by ring
  linarith [h2, h3, h4]

/-- **`A ≥ 0`** (HB (8.7)): with (8.6) and `0 ≤ λ₁ ≤ λ₀`,
`(K²+1)P(a+λ₀,µ⁰) + 2K P(a+λ₁,µ⁰) - 2K P(a,µ⁰) ≥ 0`. -/
theorem A83_nonneg {a lam₁ lam₀ K mu : ℝ} (ha : 0 < a) (hlam₁ : 0 ≤ lam₁)
    (hle : lam₁ ≤ lam₀) (hK : 0 < K) (hcond : cond86 lam₁ lam₀ a) :
    0 ≤ (K ^ 2 + 1) * P3AB (a + lam₁) (a + lam₀) mu
      + 2 * K * P3AB (a + lam₁) (a + lam₁) mu - 2 * K * P3AB (a + lam₁) a mu := by
  have hα : 0 < a + lam₁ := by linarith
  have h0 : 0 < a + lam₀ := by linarith
  have hP0 : (8 / 3) * ((a + lam₁) * (a + lam₀) / ((a + lam₀) ^ 2 + mu ^ 2)) ^ 3
      ≤ P3AB (a + lam₁) (a + lam₀) mu := P3AB_ge _ _ _ hα h0 (by linarith)
  have hP1 : (8 / 3) * ((a + lam₁) * (a + lam₁) / ((a + lam₁) ^ 2 + mu ^ 2)) ^ 3
      ≤ P3AB (a + lam₁) (a + lam₁) mu := P3AB_ge _ _ _ hα hα le_rfl
  have hPa : P3AB (a + lam₁) a mu
      ≤ (8 / 3) * ((a + lam₁) * a / (a ^ 2 + mu ^ 2)) ^ 3 := P3AB_le _ _ _ hα ha (by linarith)
  have hcoef : 2 * K ≤ K ^ 2 + 1 := by nlinarith [sq_nonneg (K - 1)]
  have hkey := cond86_key (lam₁ := lam₁) (lam₀ := lam₀) ha hcond
  have hbr : a ^ 6 / (a + lam₀) ^ 3 + a ^ 6 / (a + lam₁) ^ 3 - a ^ 3
      ≤ (a + lam₀) ^ 3 * (a ^ 2 + mu ^ 2) ^ 3 / ((a + lam₀) ^ 2 + mu ^ 2) ^ 3
        + (a + lam₁) ^ 3 * (a ^ 2 + mu ^ 2) ^ 3 / ((a + lam₁) ^ 2 + mu ^ 2) ^ 3 - a ^ 3 := by
    have h1 := bracket_le a lam₁ mu ha hlam₁
    have h2 := bracket_le a lam₀ mu ha (le_trans hlam₁ hle)
    linarith
  have hA1 : 0 ≤ (a + lam₀) ^ 3 * (a ^ 2 + mu ^ 2) ^ 3 / ((a + lam₀) ^ 2 + mu ^ 2) ^ 3
        + (a + lam₁) ^ 3 * (a ^ 2 + mu ^ 2) ^ 3 / ((a + lam₁) ^ 2 + mu ^ 2) ^ 3 - a ^ 3 :=
    le_trans hkey hbr
  set D : ℝ := a ^ 2 + mu ^ 2 with hD
  have hDa : 0 < D := by rw [hD]; positivity
  have hfac : (8 / 3) * ((a + lam₁) * (a + lam₀) / ((a + lam₀) ^ 2 + mu ^ 2)) ^ 3
      + (8 / 3) * ((a + lam₁) * (a + lam₁) / ((a + lam₁) ^ 2 + mu ^ 2)) ^ 3
      - (8 / 3) * ((a + lam₁) * a / D) ^ 3
      = (8 / 3) * ((a + lam₁) / D) ^ 3 *
        ((a + lam₀) ^ 3 * D ^ 3 / ((a + lam₀) ^ 2 + mu ^ 2) ^ 3
          + (a + lam₁) ^ 3 * D ^ 3 / ((a + lam₁) ^ 2 + mu ^ 2) ^ 3 - a ^ 3) := by
    rw [hD]; field_simp
  have hmul : 0 ≤ (8 / 3) * ((a + lam₁) / D) ^ 3 *
      ((a + lam₀) ^ 3 * D ^ 3 / ((a + lam₀) ^ 2 + mu ^ 2) ^ 3
        + (a + lam₁) ^ 3 * D ^ 3 / ((a + lam₁) ^ 2 + mu ^ 2) ^ 3 - a ^ 3) := by
    apply mul_nonneg (by positivity)
    rw [hD]; exact hA1
  have hP0nn : 0 ≤ P3AB (a + lam₁) (a + lam₀) mu := le_trans (by positivity) hP0
  have hstep : 2 * K * P3AB (a + lam₁) (a + lam₀) mu
      ≤ (K ^ 2 + 1) * P3AB (a + lam₁) (a + lam₀) mu := by nlinarith [hcoef, hP0nn]
  have hsum : (8 / 3) * ((a + lam₁) * a / D) ^ 3
      ≤ (8 / 3) * ((a + lam₁) * (a + lam₀) / ((a + lam₀) ^ 2 + mu ^ 2)) ^ 3
        + (8 / 3) * ((a + lam₁) * (a + lam₁) / ((a + lam₁) ^ 2 + mu ^ 2)) ^ 3 := by
    linarith [hfac, hmul]
  have hmid : 0 ≤ 2 * K * (P3AB (a + lam₁) (a + lam₀) mu + P3AB (a + lam₁) (a + lam₁) mu
      - P3AB (a + lam₁) a mu) := by
    apply mul_nonneg (by linarith)
    linarith [hP0, hP1, hPa, hsum]
  linarith [hstep, hmid, hP0nn]

/-- **`B ≥ 0`** (HB (8.7)): with `K ≥ 1/4` and (8.6),
`2K P(a+λ₀,2µ⁰) + (1/2)P(a+λ₁,2µ⁰) - (1/2)P(a,2µ⁰) ≥ 0`. -/
theorem B83_nonneg {a lam₁ lam₀ K mu : ℝ} (ha : 0 < a) (hlam₁ : 0 ≤ lam₁)
    (hle : lam₁ ≤ lam₀) (hK : 1 / 4 ≤ K) (hcond : cond86 lam₁ lam₀ a) :
    0 ≤ 2 * K * P3AB (a + lam₁) (a + lam₀) (2 * mu)
      + (1 / 2) * P3AB (a + lam₁) (a + lam₁) (2 * mu)
      - (1 / 2) * P3AB (a + lam₁) a (2 * mu) := by
  have hα : 0 < a + lam₁ := by linarith
  have h0 : 0 < a + lam₀ := by linarith
  have hP0 : (8 / 3) * ((a + lam₁) * (a + lam₀) / ((a + lam₀) ^ 2 + (2 * mu) ^ 2)) ^ 3
      ≤ P3AB (a + lam₁) (a + lam₀) (2 * mu) := P3AB_ge _ _ _ hα h0 (by linarith)
  have hP1 : (8 / 3) * ((a + lam₁) * (a + lam₁) / ((a + lam₁) ^ 2 + (2 * mu) ^ 2)) ^ 3
      ≤ P3AB (a + lam₁) (a + lam₁) (2 * mu) := P3AB_ge _ _ _ hα hα le_rfl
  have hPa : P3AB (a + lam₁) a (2 * mu)
      ≤ (8 / 3) * ((a + lam₁) * a / (a ^ 2 + (2 * mu) ^ 2)) ^ 3 := P3AB_le _ _ _ hα ha (by linarith)
  have hcoef : (1 / 2 : ℝ) ≤ 2 * K := by linarith
  have hkey := cond86_key (lam₁ := lam₁) (lam₀ := lam₀) ha hcond
  have hbr : a ^ 6 / (a + lam₀) ^ 3 + a ^ 6 / (a + lam₁) ^ 3 - a ^ 3
      ≤ (a + lam₀) ^ 3 * (a ^ 2 + (2 * mu) ^ 2) ^ 3 / ((a + lam₀) ^ 2 + (2 * mu) ^ 2) ^ 3
        + (a + lam₁) ^ 3 * (a ^ 2 + (2 * mu) ^ 2) ^ 3 / ((a + lam₁) ^ 2 + (2 * mu) ^ 2) ^ 3
        - a ^ 3 := by
    have h1 := bracket_le a lam₁ (2 * mu) ha hlam₁
    have h2 := bracket_le a lam₀ (2 * mu) ha (le_trans hlam₁ hle)
    linarith
  have hA1 : 0 ≤ (a + lam₀) ^ 3 * (a ^ 2 + (2 * mu) ^ 2) ^ 3 / ((a + lam₀) ^ 2 + (2 * mu) ^ 2) ^ 3
        + (a + lam₁) ^ 3 * (a ^ 2 + (2 * mu) ^ 2) ^ 3 / ((a + lam₁) ^ 2 + (2 * mu) ^ 2) ^ 3
        - a ^ 3 := le_trans hkey hbr
  set D : ℝ := a ^ 2 + (2 * mu) ^ 2 with hD
  have hDa : 0 < D := by rw [hD]; positivity
  have hfac : (8 / 3) * ((a + lam₁) * (a + lam₀) / ((a + lam₀) ^ 2 + (2 * mu) ^ 2)) ^ 3
      + (8 / 3) * ((a + lam₁) * (a + lam₁) / ((a + lam₁) ^ 2 + (2 * mu) ^ 2)) ^ 3
      - (8 / 3) * ((a + lam₁) * a / D) ^ 3
      = (8 / 3) * ((a + lam₁) / D) ^ 3 *
        ((a + lam₀) ^ 3 * D ^ 3 / ((a + lam₀) ^ 2 + (2 * mu) ^ 2) ^ 3
          + (a + lam₁) ^ 3 * D ^ 3 / ((a + lam₁) ^ 2 + (2 * mu) ^ 2) ^ 3 - a ^ 3) := by
    rw [hD]; field_simp
  have hmul : 0 ≤ (8 / 3) * ((a + lam₁) / D) ^ 3 *
      ((a + lam₀) ^ 3 * D ^ 3 / ((a + lam₀) ^ 2 + (2 * mu) ^ 2) ^ 3
        + (a + lam₁) ^ 3 * D ^ 3 / ((a + lam₁) ^ 2 + (2 * mu) ^ 2) ^ 3 - a ^ 3) := by
    apply mul_nonneg (by positivity)
    rw [hD]; exact hA1
  have hP0nn : 0 ≤ P3AB (a + lam₁) (a + lam₀) (2 * mu) := le_trans (by positivity) hP0
  have hP1nn : 0 ≤ P3AB (a + lam₁) (a + lam₁) (2 * mu) := le_trans (by positivity) hP1
  have hstep : (1 / 2) * P3AB (a + lam₁) (a + lam₀) (2 * mu)
      ≤ 2 * K * P3AB (a + lam₁) (a + lam₀) (2 * mu) := by nlinarith [hcoef, hP0nn]
  have hsum : (8 / 3) * ((a + lam₁) * a / D) ^ 3
      ≤ (8 / 3) * ((a + lam₁) * (a + lam₀) / ((a + lam₀) ^ 2 + (2 * mu) ^ 2)) ^ 3
        + (8 / 3) * ((a + lam₁) * (a + lam₁) / ((a + lam₁) ^ 2 + (2 * mu) ^ 2)) ^ 3 := by
    linarith [hfac, hmul]
  have hmid : 0 ≤ (1 / 2) * (P3AB (a + lam₁) (a + lam₀) (2 * mu)
      + P3AB (a + lam₁) (a + lam₁) (2 * mu) - P3AB (a + lam₁) a (2 * mu)) := by
    apply mul_nonneg (by norm_num)
    linarith [hP0, hP1, hPa, hsum]
  linarith [hstep, hmid, hP1nn, hP0nn]


/-! ## The boundary case `λ₁ ≥ 15`

HB's Lemma 8.3 is used in Table 4 only for `λ₁ ≤ 15`; for `λ₁ ≥ 15` the side condition (8.6)
alone already forces (8.7), by a purely elementary argument: (8.6) gives
`(a+λ₁)³ ≤ 2a³` (because `λ₀ ≥ λ₁`), whence `a+λ₁ ≤ (13/10)a` and `a ≥ 10λ₁/3`, so that
`a + λ₁ ≥ 13λ₁/3 ≥ 65`; and `P₃` is increasing on `[0,∞)` with `P₃(1) = 8/3`, so
`p83 ≥ (65/8)(K+1)² - (16/3)K > 0` for every `K ≥ 1/4`. -/

/-- `P₃` is increasing on `[0,∞)`. -/
theorem P3R_mono {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) : P3R y ≤ P3R x := by
  have hx : 0 ≤ x := le_trans hy hyx
  have h : P3R x - P3R y = (x - y) * (1 + (x + y) + (2 / 3) * (x ^ 2 + x * y + y ^ 2)) := by
    unfold P3R; ring
  have h2 : 0 ≤ (x - y) * (1 + (x + y) + (2 / 3) * (x ^ 2 + x * y + y ^ 2)) := by
    apply mul_nonneg (by linarith)
    have h3 : 0 ≤ x ^ 2 + x * y + y ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg hx hy]
    linarith
  linarith [h, h2]

/-- **The boundary case** of HB Lemma 8.3: for `λ₁ ≥ 15`, `p83 ≥ 0` from (8.6) alone. -/
theorem p83_nonneg_of_large {a lam₁ lam₀ K : ℝ} (ha : 0 < a) (hK : 1/4 ≤ K)
    (hlam₁ : 0 ≤ lam₁) (hle : lam₁ ≤ lam₀) (h15 : 15 ≤ lam₁) (hcond : cond86 lam₁ lam₀ a) :
    0 ≤ p83 lam₁ lam₀ a K := by
  have hK0 : 0 ≤ K := by linarith
  have hT : a + lam₁ ≤ a + lam₀ := by linarith
  have hT0 : 0 < a + lam₀ := by linarith
  have hS0 : 0 < a + lam₁ := by linarith
  -- `1/(a+λ₀)³ ≤ 1/(a+λ₁)³`, so (8.6) gives `(a+λ₁)³ ≤ 2a³`
  have h1 : 1 / (a + lam₀) ^ 3 ≤ 1 / (a + lam₁) ^ 3 := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by linarith) hT 3
  have h2 : 1 / a ^ 3 ≤ 2 * (1 / (a + lam₁) ^ 3) := by
    have h := hcond
    unfold cond86 at h
    linarith
  have h3 : (a + lam₁) ^ 3 ≤ 2 * a ^ 3 := by
    have ha3 : (0 : ℝ) < a ^ 3 := by positivity
    have hS3 : (0 : ℝ) < (a + lam₁) ^ 3 := by positivity
    have h2b : 1 ≤ (2 * a ^ 3) / (a + lam₁) ^ 3 := by
      have h2' : 1 ≤ 2 * (1 / (a + lam₁) ^ 3) * a ^ 3 := by
        rw [div_le_iff₀ ha3] at h2
        linarith [h2]
      convert h2' using 1
      ring
    rw [le_div_iff₀ hS3] at h2b
    linarith [h2b]
  -- hence `a + λ₁ ≤ (13/10)a`, i.e. `a ≥ 10λ₁/3`
  have h4 : a + lam₁ ≤ (13 / 10) * a := by
    by_contra hcon
    push_neg at hcon
    have h5 : (2 : ℝ) * a ^ 3 < (a + lam₁) ^ 3 := by
      have h6 : ((13 : ℝ) / 10) ^ 3 * a ^ 3 < (a + lam₁) ^ 3 := by
        have h7 : ((13 : ℝ) / 10 * a) ^ 3 < (a + lam₁) ^ 3 :=
          pow_lt_pow_left₀ hcon (by linarith : (0 : ℝ) ≤ (13 : ℝ) / 10 * a) (by norm_num)
        rwa [mul_pow] at h7
      have h8 : ((13 : ℝ) / 10) ^ 3 = 2197 / 1000 := by norm_num
      rw [h8] at h6
      nlinarith [h6, pow_pos ha 3]
    linarith [h5, h3]
  have h6 : 10 * lam₁ ≤ 3 * a := by linarith [h4]
  have h7 : 65 ≤ a + lam₁ := by nlinarith [h6, h15]
  -- the `P₃` bounds
  have hA : P3R 1 ≤ P3R ((a + lam₁) / a) := by
    apply P3R_mono (y := 1) (x := (a + lam₁) / a) (by norm_num)
    rw [le_div_iff₀ ha]
    linarith
  have hB : P3R ((a + lam₁) / (a + lam₀)) ≤ P3R 1 := by
    apply P3R_mono (x := 1) (y := (a + lam₁) / (a + lam₀)) (by positivity)
    rw [div_le_one hT0]
    linarith
  have hP31 : P3R 1 = 8 / 3 := by unfold P3R; norm_num
  have hcoef : 0 ≤ K ^ 2 + 1 / 2 := by positivity
  rw [p83]
  have hterm1 : 0 ≤ (K ^ 2 + 1 / 2) * (P3R ((a + lam₁) / a) - P3R 1) :=
    mul_nonneg hcoef (by linarith)
  have hterm2' : 2 * K * P3R ((a + lam₁) / (a + lam₀)) ≤ 2 * K * (8 / 3) := by
    have h2 : P3R ((a + lam₁) / (a + lam₀)) ≤ 8 / 3 := by rw [← hP31]; exact hB
    exact mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * K)
  have hterm3 : (65 / 8) * (K + 1) ^ 2 ≤ (K + 1) ^ 2 * (a + lam₁) * (1 / 8) := by
    have h2 : 0 ≤ (K + 1) ^ 2 * (1 / 8) := by positivity
    nlinarith [h7, h2]
  have hlast : 0 ≤ -(2 * K * (8 / 3)) + (65 / 8) * (K + 1) ^ 2 := by
    have h2 : (65 / 8) * (K + 1) ^ 2 - 2 * K * (8 / 3)
        = (65 / 8) * K ^ 2 + (131 / 12) * K + 65 / 8 := by ring
    nlinarith [h2, hK0, sq_nonneg K, hK]
  linarith [hterm1, hterm2', hterm3, hlast]


/-! ## The three-point assembly of HB (8.5)–(8.7)

Given the pointwise inequality (8.5) at the three points `σ, σ+iγ⁰, σ+2iγ⁰` and, at each
of them, the two upper bounds (for `χ₁` and for the principal character) on `Σ(s,χ)`, the
combination is pure algebra: the `P₃`-terms of the zeros `ρ₁, ρ₀, ρ̄₀` reassemble as
`(K²+½)(P₃(α/a) - P₃(1)) - 2K P₃(α/(a+λ₀)) - A - B`, and `A, B ≥ 0` (from (8.6)) are dropped.
-/

/-- **The three-point assembly of HB Lemma 8.3.** -/
theorem assembly_core {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q)
    {a K ε L lam₁ lam₀ μ εL εP E0 E1 E2 F0 F1 F2 : ℝ}
    (ha : 0 < a) (hK : 1/4 ≤ K) (hlam₁ : 0 ≤ lam₁) (hle : lam₁ ≤ lam₀) (hcond : cond86 lam₁ lam₀ a)
    {s0 s1 s2 : ℂ}
    (h85 : 0 ≤ (K ^ 2 + 1 / 2) * (SigmaP3L q L 1 s0 a lam₁ + SigmaP3L q L χ₁ s0 a lam₁)
      + 2 * K * (SigmaP3L q L 1 s1 a lam₁ + SigmaP3L q L χ₁ s1 a lam₁)
      + (1 / 2) * (SigmaP3L q L 1 s2 a lam₁ + SigmaP3L q L χ₁ s2 a lam₁))
    (hχ0 : SigmaP3L q L χ₁ s0 a lam₁
      ≤ -(P3AB (a + lam₁) (a + lam₁) 0) - P3AB (a + lam₁) (a + lam₀) μ
        + (a + lam₁) * (1 / 8 + εL) + E0 + F0)
    (hχ1 : SigmaP3L q L χ₁ s1 a lam₁
      ≤ -(P3AB (a + lam₁) (a + lam₁) μ) - P3AB (a + lam₁) (a + lam₀) 0
        - P3AB (a + lam₁) (a + lam₀) (2 * μ) + (a + lam₁) * (1 / 8 + εL) + E1 + F1)
    (hχ2 : SigmaP3L q L χ₁ s2 a lam₁
      ≤ -(P3AB (a + lam₁) (a + lam₀) μ) - P3AB (a + lam₁) (a + lam₁) (2 * μ)
        + (a + lam₁) * (1 / 8 + εL) + E2 + F2)
    (hp0 : SigmaP3L q L 1 s0 a lam₁ ≤ P3AB (a + lam₁) a 0 + (a + lam₁) * εP)
    (hp1 : SigmaP3L q L 1 s1 a lam₁ ≤ P3AB (a + lam₁) a μ + (a + lam₁) * εP)
    (hp2 : SigmaP3L q L 1 s2 a lam₁ ≤ P3AB (a + lam₁) a (2 * μ) + (a + lam₁) * εP)
    (hErr : (K ^ 2 + 1 / 2) * ((a + lam₁) * (1 / 8 + εL) + E0 + F0)
        + 2 * K * ((a + lam₁) * (1 / 8 + εL) + E1 + F1)
        + (1 / 2) * ((a + lam₁) * (1 / 8 + εL) + E2 + F2)
        + ((K ^ 2 + 1 / 2) + 2 * K + 1 / 2) * ((a + lam₁) * εP)
      ≤ (K + 1) ^ 2 * (a + lam₁) * (1 / 8) + (K + 1) ^ 2 * (a + lam₁) * ε) :
    0 ≤ p83 lam₁ lam₀ a K + (K + 1) ^ 2 * (a + lam₁) * ε := by
  have hK0 : 0 ≤ K := by linarith
  have hα0 : 0 < a + lam₁ := by linarith
  have hA := A83_nonneg (a := a) (lam₁ := lam₁) (lam₀ := lam₀) (K := K) (mu := μ) ha hlam₁ hle
    (by linarith) hcond
  have hB := B83_nonneg (a := a) (lam₁ := lam₁) (lam₀ := lam₀) (K := K) (mu := μ) ha hlam₁ hle hK hcond
  have hx0 : P3AB (a + lam₁) a 0 = P3R ((a + lam₁) / a) := P3AB_zero (a + lam₁) a
  have hy1 : P3AB (a + lam₁) (a + lam₁) 0 = P3R 1 := by
    rw [P3AB_zero]
    congr 1
    field_simp
  have hz0 : P3AB (a + lam₁) (a + lam₀) 0 = P3R ((a + lam₁) / (a + lam₀)) := P3AB_zero (a + lam₁) (a + lam₀)
  have hsub : (0 : ℝ) ≤ (K ^ 2 + 1 / 2) * (P3AB (a + lam₁) a 0 - P3AB (a + lam₁) (a + lam₁) 0)
      - 2 * K * P3AB (a + lam₁) (a + lam₀) 0
      - ((K ^ 2 + 1) * P3AB (a + lam₁) (a + lam₀) μ + 2 * K * P3AB (a + lam₁) (a + lam₁) μ
          - 2 * K * P3AB (a + lam₁) a μ)
      - (2 * K * P3AB (a + lam₁) (a + lam₀) (2 * μ) + (1 / 2) * P3AB (a + lam₁) (a + lam₁) (2 * μ)
          - (1 / 2) * P3AB (a + lam₁) a (2 * μ))
      + ((K ^ 2 + 1 / 2) * ((a + lam₁) * (1 / 8 + εL) + E0 + F0)
          + 2 * K * ((a + lam₁) * (1 / 8 + εL) + E1 + F1)
          + (1 / 2) * ((a + lam₁) * (1 / 8 + εL) + E2 + F2)
          + ((K ^ 2 + 1 / 2) + 2 * K + 1 / 2) * ((a + lam₁) * εP)) := by
    nlinarith [h85, hχ0, hχ1, hχ2, hp0, hp1, hp2]
  calc (0 : ℝ) ≤ _ := hsub
    _ ≤ (K ^ 2 + 1 / 2) * (P3R ((a + lam₁) / a) - P3R 1) - 2 * K * P3R ((a + lam₁) / (a + lam₀))
          + (K + 1) ^ 2 * (a + lam₁) * (1 / 8) + (K + 1) ^ 2 * (a + lam₁) * ε := by
        rw [hx0, hy1, hz0]
        nlinarith [hA, hB, hErr, sq_nonneg (K + 1), hK0]
    _ = p83 lam₁ lam₀ a K + (K + 1) ^ 2 * (a + lam₁) * ε := by
        rw [p83]

/-- `Re P₃(α/((s-u)L))` when `β = a + λ` and `s.re = 1 + a/L`: the normal form `P3AB α (a+λ) t`. -/
theorem P3term_at_zero {a lam L α t : ℝ} (hL : L ≠ 0) {s u : ℂ}
    (hs : s.re = 1 + a / L) (hu : u.re = 1 - lam / L) (ht : (s.im - u.im) * L = t) :
    (P3 (α / ((s - u) * (L : ℂ)))).re = P3AB α (a + lam) t := by
  rw [P3_div_eq_P3AB α L s u, ht]
  congr 1
  show (s.re - u.re) * L = a + lam
  rw [hs, hu]
  field_simp
  ring

/-- The principal-character point: `Re P₃(α/((s-1)L))` with `s.re = 1 + a/L`. -/
theorem P3term_at_one {a L α t : ℝ} (hL : L ≠ 0) {s : ℂ} (hs : s.re = 1 + a / L)
    (ht : s.im * L = t) :
    (P3 (α / ((s - 1) * (L : ℂ)))).re = P3AB α a t := by
  rw [P3_div_eq_P3AB α L s 1]
  have h1 : (s.re - (1 : ℂ).re) * L = a := by
    simp only [Complex.one_re]
    rw [hs]; field_simp; ring
  have h2 : (s.im - (1 : ℂ).im) * L = t := by
    simp only [Complex.one_im, sub_zero]
    exact ht
  rw [h1, h2]

set_option maxHeartbeats 40000000 in
/-- The three-point assembly of HB Lemma 8.3, instantiated. -/
theorem HB83 : Work.ZeroFreeTables.HBLemma8_3 := by
  intro a K ε ha hK hε
  -- the analytic inputs
  obtain ⟨L0log, δ, hδ0, hδ1, hlogHyp⟩ := HB83aux.logDerivHyp_eighth (e := ε / 4) (by linarith)
  obtain ⟨L0ζ, hζ⟩ := principal_bound_clean (a := a) (M := 15) (ε := ε / 4) ha (by linarith)
  obtain ⟨C0, hC0pos, hCin⟩ := invSqSum_le
  obtain ⟨Ct, hCt0pos, hCt⟩ := trivSeries_le
  obtain ⟨Cs, hCs0pos, htransf⟩ := SigmaP3L_primitive_le
  -- the shape constants
  set Amax : ℝ := a + 15 with hAmax
  set A1 : ℝ := 3 * C0 * (1 + 4 / δ ^ 2) + Ct with hA1
  set A2 : ℝ := 3 * C0 * (2 / δ) * (1 + 4 / δ ^ 2) + Ct with hA2
  set c4 : ℝ := ε / (4 * Cs * (1 + Amax + Amax ^ 2)) with hc4
  obtain ⟨X4, hX4⟩ := loglogPow4_le_mul (c := c4) (by rw [hc4]; positivity)
  -- the threshold
  set Θ1 : ℝ := max 3 L0log with hΘ1
  set Θ2 : ℝ := max Θ1 L0ζ with hΘ2
  set Θ3 : ℝ := max Θ2 (2 * Amax / δ) with hΘ3
  set Θ4 : ℝ := max Θ3 (Real.exp a) with hΘ4
  set Θ5 : ℝ := max Θ4 (Real.exp (1 / a)) with hΘ5
  set Θ6 : ℝ := max Θ5 (4 * (Amax * A1 + Amax ^ 2 * A2 + 24 / δ) / ε) with hΘ6
  set Θ7 : ℝ := max Θ6 X4 with hΘ7
  have h37 : Θ1 ≤ Θ7 :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))))
  have h47 : Θ2 ≤ Θ7 :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) (le_max_left _ _))))
  have h57 : Θ3 ≤ Θ7 :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
      (le_max_left _ _)))
  have h67 : Θ4 ≤ Θ7 :=
    le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have h77 : Θ5 ≤ Θ7 := le_trans (le_max_left _ _) (le_max_left _ _)
  have h87 : Θ6 ≤ Θ7 := le_max_left _ _
  have h97 : X4 ≤ Θ7 := le_max_right _ _
  have hΘ1a : (3 : ℝ) ≤ Θ1 := le_max_left _ _
  have hΘ1b : L0log ≤ Θ1 := le_max_right _ _
  have hΘ2b : L0ζ ≤ Θ2 := le_max_right _ _
  have hΘ3b : 2 * Amax / δ ≤ Θ3 := le_max_right _ _
  have hΘ4b : Real.exp a ≤ Θ4 := le_max_right _ _
  have hΘ5b : Real.exp (1 / a) ≤ Θ5 := le_max_right _ _
  have hΘ6b : 4 * (Amax * A1 + Amax ^ 2 * A2 + 24 / δ) / ε ≤ Θ6 := le_max_right _ _
  refine ⟨⌈Real.exp Θ7⌉₊ + 1, ?_⟩
  intro q hq hqne χ₁ ρ₁ ρ₀ hMin hsq hχ₁ him1 hZ1 hZ0 hne him0 hle hcond
  have hq_exp : Real.exp Θ7 ≤ (q : ℝ) := by
    have h1 : Real.exp Θ7 ≤ ((⌈Real.exp Θ7⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : (⌈Real.exp Θ7⌉₊ : ℕ) ≤ q := by omega
    exact le_trans h1 (by exact_mod_cast h2)
  have hq3 : 3 ≤ q := by
    have h1 : (3 : ℝ) ≤ Real.exp Θ7 := by
      have h2 : (3 : ℝ) ≤ Real.exp 3 := by
        have h3 := Real.add_one_le_exp (3 : ℝ)
        linarith
      exact le_trans h2 (Real.exp_le_exp.mpr (le_trans hΘ1a h37))
    exact_mod_cast le_trans h1 hq_exp
  have hΘL : Θ7 ≤ Real.log (q : ℝ) := by
    rw [← Real.log_exp Θ7]
    exact Real.log_le_log (Real.exp_pos Θ7) hq_exp
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have hLΘ : Θ7 ≤ L := hΘL
  have hL3 : 3 ≤ L := le_trans (le_trans hΘ1a h37) hLΘ
  have hLpos : 0 < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hL1 : 1 ≤ L := by linarith
  have hL1' : 1 < L := by linarith
  have haLpos : 0 < a / L := div_pos ha hLpos
  have haLnn : 0 ≤ a / L := le_of_lt haLpos
  have hK1pos : 0 < 1 + Amax + Amax ^ 2 := by nlinarith [sq_nonneg Amax]
  have hlogLpos : 0 < Real.log L := Real.log_pos (by linarith)
  have hL0log : L0log ≤ L := le_trans (le_trans hΘ1b h37) hLΘ
  have hL0ζ : L0ζ ≤ L := le_trans (le_trans hΘ2b h47) hLΘ
  have h2Amaxδ : 2 * Amax / δ ≤ L := le_trans (le_trans hΘ3b h57) hLΘ
  have hexpa : Real.exp a ≤ L := le_trans (le_trans hΘ4b h67) hLΘ
  have hexp1a : Real.exp (1 / a) ≤ L := le_trans (le_trans hΘ5b h77) hLΘ
  have hThr : 4 * (Amax * A1 + Amax ^ 2 * A2 + 24 / δ) / ε ≤ L :=
    le_trans (le_trans hΘ6b h87) hLΘ
  have hX4L : X4 ≤ L := le_trans h97 hLΘ
  -- the two lambda's
  set lam₁ : ℝ := Work.LinnikContract.lamOf q ρ₁ with hlam1
  set lam₀ : ℝ := Work.LinnikContract.lamOf q ρ₀ with hlam0
  set α : ℝ := a + lam₁ with hα
  have hlam₁nn : 0 ≤ lam₁ := by
    have h1 : ρ₁.re < 1 := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ₁ hZ1.2.1
    rw [hlam1, Work.LinnikContract.lamOf]
    exact mul_nonneg (by linarith) (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q)))
  have hαpos : 0 < α := by rw [hα]; linarith
  have hαnn : 0 ≤ α := le_of_lt hαpos
  by_cases hbig : 15 ≤ lam₁
  · -- the boundary case
    have h0 : 0 ≤ p83 lam₁ lam₀ a K :=
      p83_nonneg_of_large (a := a) (lam₁ := lam₁) (lam₀ := lam₀) (K := K) ha hK hlam₁nn hle hbig hcond
    have h1 : 0 ≤ (K + 1) ^ 2 * α * ε := by positivity
    linarith only [h0, h1]
  · push_neg at hbig
    have hαAmax : α ≤ Amax := by rw [hα, hAmax]; linarith
    letI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
    have hχs_ne1 : χ₁.primitiveCharacter ≠ 1 := by
      intro hh
      refine hχ₁ ?_
      rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, hh, map_one]
    have hχs_prim : χ₁.primitiveCharacter.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ₁
    have hsqs : χ₁.primitiveCharacter ^ 2 = 1 := by
      have h : DirichletCharacter.changeLevel χ₁.conductor_dvd_level (χ₁.primitiveCharacter ^ 2) = 1 := by
        rw [map_pow, DirichletCharacter.changeLevel_primitiveCharacter, hsq]
      exact (DirichletCharacter.changeLevel_eq_one_iff χ₁.conductor_dvd_level).mp h
    have hlogcond : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ L := by
      have hcpos : (0:ℝ) < ((χ₁.conductor : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero χ₁.conductor_ne_zero
      rw [hLdef]
      exact Real.log_le_log hcpos (by exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ₁.conductor_dvd_level)
    have hzm : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁.primitiveCharacter u
        = Work.LinnikContract.zeroMult χ₁ u := by
      intro u
      have h := zeroMult_changeLevel (N := χ₁.conductor) (q := q)
        (DirichletCharacter.conductor_dvd_level χ₁) χ₁.primitiveCharacter u
      rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
      exact h.symm
    -- the moving pieces
    set μ : ℝ := ρ₀.im * L with hμ
    set s0 : ℂ := ((1 + a / L : ℝ) : ℂ) with hs0
    set s1 : ℂ := ((1 + a / L : ℝ) : ℂ) + (ρ₀.im : ℂ) * Complex.I with hs1
    set s2 : ℂ := ((1 + a / L : ℝ) : ℂ) + ((2 * ρ₀.im : ℝ) : ℂ) * Complex.I with hs2
    set Cj : ℝ := C0 * (L + 2) with hCj
    set ErrT : ℝ := Cs * (α + α ^ 2 + α ^ 3) * (Real.log L + 2) ^ 4 / L with hErrT
    set E : ℝ := (α ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
      + (2 / 3) * (α ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) + ErrT with hE
    set F0 : ℝ := 2 * (8 * α / (δ * L)) with hF0
    set F1 : ℝ := 3 * (8 * α / (δ * L)) with hF1
    set F2 : ℝ := 2 * (8 * α / (δ * L)) with hF2
    have hμeq : μ = ρ₀.im * L := hμ
    have hρ₁re : ρ₁.re = 1 - lam₁ / L := by
      have h2 : lam₁ = (1 - ρ₁.re) * L := by rw [hlam1, Work.LinnikContract.lamOf, hLdef]
      have h3 : lam₁ / L = 1 - ρ₁.re := by
        rw [div_eq_iff hLne]
        exact h2
      linarith
    have hρ₀re : ρ₀.re = 1 - lam₀ / L := by
      have h2 : lam₀ = (1 - ρ₀.re) * L := by rw [hlam0, Work.LinnikContract.lamOf, hLdef]
      have h3 : lam₀ / L = 1 - ρ₀.re := by
        rw [div_eq_iff hLne]
        exact h2
      linarith
    have hconjre : (starRingEnd ℂ ρ₀).re = 1 - lam₀ / L := by
      rw [show (starRingEnd ℂ ρ₀).re = ρ₀.re by simp, hρ₀re]
    have hconjim : (starRingEnd ℂ ρ₀).im = -ρ₀.im := by simp
    have hs0re : s0.re = 1 + a / L := by simp [s0]
    have hs1re : s1.re = 1 + a / L := by simp [s1]
    have hs2re : s2.re = 1 + a / L := by simp [s2]
    have hs0im : s0.im = 0 := by simp [s0]
    have hs1im : s1.im = ρ₀.im := by simp [s1]
    have hs2im : s2.im = 2 * ρ₀.im := by simp [s2]
    have himρ₀ : |ρ₀.im| ≤ 1 := hZ0.2.2
    have hs0im3 : |s0.im| ≤ 3 := by rw [hs0im]; norm_num
    have hs1im3 : |s1.im| ≤ 3 := by rw [hs1im]; linarith [abs_nonneg ρ₀.im, himρ₀]
    have hs2im3 : |s2.im| ≤ 3 := by
      rw [hs2im, abs_mul]
      have h2 : |(2:ℝ)| = 2 := by norm_num
      rw [h2]
      nlinarith [abs_nonneg ρ₀.im, himρ₀]
    have hs0im4 : |s0.im| ≤ 4 := by linarith [hs0im3]
    have hs1im4 : |s1.im| ≤ 4 := by linarith [hs1im3]
    have hs2im4 : |s2.im| ≤ 4 := by linarith [hs2im3]
    -- the log-derivative input at the three points
    have hlogPoint : ∀ s : ℂ, s.re = 1 + a / L → |s.im| ≤ 3 →
        (-logDeriv (DirichletCharacter.LFunction χ₁.primitiveCharacter) s).re
          + Work.ZeroFreeTables.P9.nearInvSum χ₁.conductor χ₁.primitiveCharacter s δ
          ≤ (1 / 8 + ε / 4) * L := by
      intro s hsre hsim
      have hreg1 : 1 + 1 / (L * Real.log L) ≤ s.re := by
        rw [hsre]
        have h1 : 1 / a ≤ Real.log L := by
          have h2 : Real.log (Real.exp (1 / a)) ≤ Real.log L :=
            Real.log_le_log (Real.exp_pos _) hexp1a
          rwa [Real.log_exp] at h2
        have h3 : 1 ≤ a * Real.log L := by
          rw [div_le_iff₀ ha] at h1
          linarith
        have h4 : 1 / (L * Real.log L) ≤ a / L := by
          rw [div_le_div_iff₀ (by positivity) hLpos]
          nlinarith
        linarith
      have hreg2 : s.re ≤ 1 + Real.log L / L := by
        rw [hsre]
        have h1 : a ≤ Real.log L := by
          have h2 : Real.log (Real.exp a) ≤ Real.log L := Real.log_le_log (Real.exp_pos _) hexpa
          rwa [Real.log_exp] at h2
        have h2 : a / L ≤ Real.log L / L := by
          rw [div_le_div_iff₀ hLpos hLpos]
          nlinarith only [h1, hLpos.le]
        linarith
      have hreg3 : |s.im| ≤ L := by linarith [hsim, hL3]
      have h1 := hlogHyp (N := χ₁.conductor) χ₁.primitiveCharacter hχs_ne1 hχs_prim hsqs
        hL0log hlogcond s hreg1 hreg2 hreg3
      rwa [Work.ZeroFreeTables.P9.invNearSum_eq_tsum χ₁.primitiveCharacter hχs_ne1 hχs_prim
        (by linarith) hδ0 (le_of_lt hδ1)] at h1
    -- the minimality input for the pointwise engine
    have hmin0 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 →
        |u.im| ≤ 10 → lam₁ ≤ (1 - u.re) * L := by
      intro u hz him
      have hz1 : Work.LinnikContract.zeroMult χ₁ u ≠ 0 := by rwa [hzm u] at hz
      have h1 : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u :=
        hMin.2 χ₁ u hχ₁ hz1 him
      have h2 : Work.LinnikContract.lamOf q u = (1 - u.re) * L := by
        rw [Work.LinnikContract.lamOf, hLdef]
      rw [← hlam1, h2] at h1
      exact h1
    -- the parity and the trivial-zero sums
    set par : ℕ := if χ₁.primitiveCharacter.Even then 0 else 1 with hpar
    have hpar0 : χ₁.primitiveCharacter.Even → par = 0 := by intro h; rw [hpar, if_pos h]
    have hpar1 : χ₁.primitiveCharacter.Odd → par = 1 := by intro h; rw [hpar, if_neg h.not_even]
    have hpar2 : par ≤ 2 := by rw [hpar]; split <;> omega
    have hS2_0 : |∑' n : ℕ, (((1 / (s0 + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct :=
      (hCt.1 (s := s0) (by rw [hs0re]; linarith only [haLnn]) par hpar2).1
    have hS3_0 : |∑' n : ℕ, (((1 / (s0 + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct :=
      (hCt.1 (s := s0) (by rw [hs0re]; linarith only [haLnn]) par hpar2).2
    have hS2_1 : |∑' n : ℕ, (((1 / (s1 + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct :=
      (hCt.1 (s := s1) (by rw [hs1re]; linarith only [haLnn]) par hpar2).1
    have hS3_1 : |∑' n : ℕ, (((1 / (s1 + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct :=
      (hCt.1 (s := s1) (by rw [hs1re]; linarith only [haLnn]) par hpar2).2
    have hS2_2 : |∑' n : ℕ, (((1 / (s2 + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct :=
      (hCt.1 (s := s2) (by rw [hs2re]; linarith only [haLnn]) par hpar2).1
    have hS3_2 : |∑' n : ℕ, (((1 / (s2 + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct :=
      (hCt.1 (s := s2) (by rw [hs2re]; linarith only [haLnn]) par hpar2).2
    -- the inverse-square zero sums
    have hJ0 : Work.ZeroFreeTables.P9.invSqSum χ₁.conductor χ₁.primitiveCharacter s0 ≤ Cj := by
      have h1 := hCin χ₁.primitiveCharacter hχs_ne1 hχs_prim (s := s0)
        (by rw [hs0re]; linarith only [haLnn]) (by rw [hs0im]; norm_num)
      have h2 : C0 * (Real.log ((χ₁.conductor : ℕ) : ℝ) + 2) ≤ C0 * (L + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0pos.le
      rw [hCj]
      linarith
    have hJ1 : Work.ZeroFreeTables.P9.invSqSum χ₁.conductor χ₁.primitiveCharacter s1 ≤ Cj := by
      have h1 := hCin χ₁.primitiveCharacter hχs_ne1 hχs_prim (s := s1)
        (by rw [hs1re]; linarith only [haLnn]) (by rw [hs1im]; linarith only [abs_nonneg ρ₀.im, himρ₀])
      have h2 : C0 * (Real.log ((χ₁.conductor : ℕ) : ℝ) + 2) ≤ C0 * (L + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0pos.le
      rw [hCj]
      linarith
    have hJ2 : Work.ZeroFreeTables.P9.invSqSum χ₁.conductor χ₁.primitiveCharacter s2 ≤ Cj := by
      have h1 := hCin χ₁.primitiveCharacter hχs_ne1 hχs_prim (s := s2)
        (by rw [hs2re]; linarith only [haLnn]) (by rw [hs2im, abs_mul]; norm_num; linarith only [abs_nonneg ρ₀.im, himρ₀])
      have h2 : C0 * (Real.log ((χ₁.conductor : ℕ) : ℝ) + 2) ≤ C0 * (L + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0pos.le
      rw [hCj]
      linarith
    -- the far budget
    have hαδL : 2 * α ≤ δ * L := by
      have h1 : 2 * Amax ≤ δ * L := by
        rw [div_le_iff₀ hδ0] at h2Amaxδ
        linarith
      nlinarith [hαAmax]
    have haδL : 2 * a ≤ δ * L := by nlinarith [hαδL, hα, ha]
    -- the memberships of the three zero sets
    have hρ₀_ne_c : ρ₀ ≠ starRingEnd ℂ ρ₀ := by
      intro h
      have h1 : ρ₀.im = (starRingEnd ℂ ρ₀).im := congrArg Complex.im h
      rw [hconjim] at h1
      exact him0 (by linarith only [h1])
    have hρ₁_ne_c : ρ₁ ≠ starRingEnd ℂ ρ₀ := by
      intro h
      have h1 : ρ₁.im = (starRingEnd ℂ ρ₀).im := congrArg Complex.im h
      rw [hconjim, him1] at h1
      exact him0 (by linarith only [h1])
    have hT0mem : ∀ u ∈ ({ρ₁, ρ₀} : Finset ℂ),
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rw [hzm u]
      rcases hu with rfl | rfl
      · exact hZ1.2.1
      · exact hZ0.2.1
    have hT1mem : ∀ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ),
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rw [hzm u]
      rcases hu with rfl | rfl | rfl
      · exact hZ1.2.1
      · exact hZ0.2.1
      · rw [zeroMult_conj χ₁ hsq ρ₀]; exact hZ0.2.1
    -- the P₃-terms of the individual zeros
    have hterm_ρ₁ : ∀ (s : ℂ) (j : ℝ), s.re = 1 + a / L → s.im = j * ρ₀.im →
        (P3 (α / ((s - ρ₁) * (L : ℂ)))).re = P3AB α α (j * μ) := by
      intro s j hsre hsim
      refine P3term_at_zero (a := a) (lam := lam₁) (L := L) (α := α) (t := j * μ) hLne hsre hρ₁re ?_
      rw [hsim, him1, sub_zero, mul_assoc, ← hμ]
    have hterm_ρ₀ : ∀ (s : ℂ) (j : ℝ), s.re = 1 + a / L → s.im = j * ρ₀.im →
        (P3 (α / ((s - ρ₀) * (L : ℂ)))).re = P3AB α (a + lam₀) ((j - 1) * μ) := by
      intro s j hsre hsim
      refine P3term_at_zero (a := a) (lam := lam₀) (L := L) (α := α) (t := (j - 1) * μ) hLne hsre hρ₀re ?_
      rw [hsim]
      have h1 : (j * ρ₀.im - ρ₀.im) * L = (j - 1) * μ := by rw [hμ]; ring
      rw [h1]
    have hterm_c : ∀ (s : ℂ) (j : ℝ), s.re = 1 + a / L → s.im = j * ρ₀.im →
        (P3 (α / ((s - starRingEnd ℂ ρ₀) * (L : ℂ)))).re = P3AB α (a + lam₀) ((j + 1) * μ) := by
      intro s j hsre hsim
      refine P3term_at_zero (a := a) (lam := lam₀) (L := L) (α := α) (t := (j + 1) * μ) hLne hsre hconjre ?_
      rw [hsim, hconjim]
      have h1 : (j * ρ₀.im - -ρ₀.im) * L = (j + 1) * μ := by rw [hμ]; ring
      rw [h1]
    -- the sums over the zero sets
    have hsum0 : (∑ u ∈ ({ρ₁, ρ₀} : Finset ℂ), (P3 (α / ((s0 - u) * (L : ℂ)))).re)
        = P3AB α α 0 + P3AB α (a + lam₀) μ := by
      rw [Finset.sum_pair hne.symm, hterm_ρ₁ s0 0 hs0re (by simp [hs0im])]
      rw [hterm_ρ₀ s0 0 hs0re (by simp [hs0im])]
      norm_num
      rw [P3AB_neg α (a + lam₀) μ (by linarith only [ha, hlam₁nn, hle])]
    have hsum1 : (∑ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ), (P3 (α / ((s1 - u) * (L : ℂ)))).re)
        = P3AB α α μ + P3AB α (a + lam₀) 0 + P3AB α (a + lam₀) (2 * μ) := by
      rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hne.symm, hρ₁_ne_c⟩), Finset.sum_pair hρ₀_ne_c]
      rw [hterm_ρ₁ s1 1 hs1re (by simp [hs1im])]
      rw [hterm_ρ₀ s1 1 hs1re (by simp [hs1im])]
      rw [hterm_c s1 1 hs1re (by simp [hs1im])]
      norm_num
      ring
    have hsum2 : (∑ u ∈ ({ρ₁, ρ₀} : Finset ℂ), (P3 (α / ((s2 - u) * (L : ℂ)))).re)
        = P3AB α α (2 * μ) + P3AB α (a + lam₀) μ := by
      rw [Finset.sum_pair hne.symm, hterm_ρ₁ s2 2 hs2re (by simp [hs2im])]
      rw [hterm_ρ₀ s2 2 hs2re (by simp [hs2im])]
      norm_num
    -- the three χ-bounds
    have hχ0 : Work.ZeroFreeTables.SigmaP3L q L χ₁ s0 a lam₁
        ≤ -(P3AB α α 0) - P3AB α (a + lam₀) μ + α * (1 / 8 + ε / 4) + E + F0 := by
      have htr := htransf (N := χ₁.conductor) (q := q) (DirichletCharacter.conductor_dvd_level χ₁)
        χ₁.primitiveCharacter hχs_ne1 hq3 (s := s0) (by rw [hs0re]; linarith only [haLpos])
        (L := L) (a := a) (lam₁ := lam₁) hL1 hLdef.le (by rw [← hα]; exact hαnn)
      rw [DirichletCharacter.changeLevel_primitiveCharacter] at htr
      have hErreq : Cs * (α + α ^ 2 + α ^ 3) * (Real.log (Real.log (q : ℝ)) + 2) ^ 4 / L = ErrT := by
        rw [hErrT]
      rw [hErreq] at htr
      have hpb := point_bound83 (N := χ₁.conductor) (χ := χ₁.primitiveCharacter) hχs_ne1 hχs_prim
        (L := L) (a := a) (lam₁ := lam₁) (δ := δ) (c := 1 / 8 + ε / 4) (Cj := Cj) (Ct := Ct)
        ha hlam₁nn hδ0 hδ1 hL1' haδL hαδL (s := s0) hs0re hs0im3 (hlogPoint s0 hs0re hs0im3)
        par hpar0 hpar1 hS2_0 hS3_0 hJ0 hmin0 ({ρ₁, ρ₀} : Finset ℂ) hT0mem
      have hcast : ((a : ℂ) + (lam₁ : ℂ)) = (α : ℂ) := by rw [hα]; push_cast; ring
      simp only [hcast] at hpb
      rw [hsum0] at hpb
      have hcard : ((({ρ₁, ρ₀} : Finset ℂ)).card : ℝ) = 2 := by
        rw [Finset.card_pair hne.symm]; norm_num
      rw [hcard, ← hα] at hpb
      have hEeq : E = (α ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
          + (2 / 3) * (α ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) + ErrT := hE
      have hF0eq : F0 = 2 * (8 * α / (δ * L)) := hF0
      linarith [htr, hpb, hEeq, hF0eq]
    have hχ1 : Work.ZeroFreeTables.SigmaP3L q L χ₁ s1 a lam₁
        ≤ -(P3AB α α μ) - P3AB α (a + lam₀) 0 - P3AB α (a + lam₀) (2 * μ)
          + α * (1 / 8 + ε / 4) + E + F1 := by
      have htr := htransf (N := χ₁.conductor) (q := q) (DirichletCharacter.conductor_dvd_level χ₁)
        χ₁.primitiveCharacter hχs_ne1 hq3 (s := s1) (by rw [hs1re]; linarith only [haLpos])
        (L := L) (a := a) (lam₁ := lam₁) hL1 hLdef.le (by rw [← hα]; exact hαnn)
      rw [DirichletCharacter.changeLevel_primitiveCharacter] at htr
      have hErreq : Cs * (α + α ^ 2 + α ^ 3) * (Real.log (Real.log (q : ℝ)) + 2) ^ 4 / L = ErrT := by
        rw [hErrT]
      rw [hErreq] at htr
      have hpb := point_bound83 (N := χ₁.conductor) (χ := χ₁.primitiveCharacter) hχs_ne1 hχs_prim
        (L := L) (a := a) (lam₁ := lam₁) (δ := δ) (c := 1 / 8 + ε / 4) (Cj := Cj) (Ct := Ct)
        ha hlam₁nn hδ0 hδ1 hL1' haδL hαδL (s := s1) hs1re hs1im3 (hlogPoint s1 hs1re hs1im3)
        par hpar0 hpar1 hS2_1 hS3_1 hJ1 hmin0 ({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ) hT1mem
      have hcast : ((a : ℂ) + (lam₁ : ℂ)) = (α : ℂ) := by rw [hα]; push_cast; ring
      simp only [hcast] at hpb
      rw [hsum1] at hpb
      have hcard : ((({ρ₁, ρ₀, starRingEnd ℂ ρ₀} : Finset ℂ)).card : ℝ) = 3 := by
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              exact ⟨hne.symm, hρ₁_ne_c⟩), Finset.card_pair hρ₀_ne_c]
        norm_num
      rw [hcard, ← hα] at hpb
      have hEeq : E = (α ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
          + (2 / 3) * (α ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) + ErrT := hE
      have hF1eq : F1 = 3 * (8 * α / (δ * L)) := hF1
      linarith [htr, hpb, hEeq, hF1eq]
    have hχ2 : Work.ZeroFreeTables.SigmaP3L q L χ₁ s2 a lam₁
        ≤ -(P3AB α (a + lam₀) μ) - P3AB α α (2 * μ) + α * (1 / 8 + ε / 4) + E + F2 := by
      have htr := htransf (N := χ₁.conductor) (q := q) (DirichletCharacter.conductor_dvd_level χ₁)
        χ₁.primitiveCharacter hχs_ne1 hq3 (s := s2) (by rw [hs2re]; linarith only [haLpos])
        (L := L) (a := a) (lam₁ := lam₁) hL1 hLdef.le (by rw [← hα]; exact hαnn)
      rw [DirichletCharacter.changeLevel_primitiveCharacter] at htr
      have hErreq : Cs * (α + α ^ 2 + α ^ 3) * (Real.log (Real.log (q : ℝ)) + 2) ^ 4 / L = ErrT := by
        rw [hErrT]
      rw [hErreq] at htr
      have hpb := point_bound83 (N := χ₁.conductor) (χ := χ₁.primitiveCharacter) hχs_ne1 hχs_prim
        (L := L) (a := a) (lam₁ := lam₁) (δ := δ) (c := 1 / 8 + ε / 4) (Cj := Cj) (Ct := Ct)
        ha hlam₁nn hδ0 hδ1 hL1' haδL hαδL (s := s2) hs2re hs2im3 (hlogPoint s2 hs2re hs2im3)
        par hpar0 hpar1 hS2_2 hS3_2 hJ2 hmin0 ({ρ₁, ρ₀} : Finset ℂ) hT0mem
      have hcast : ((a : ℂ) + (lam₁ : ℂ)) = (α : ℂ) := by rw [hα]; push_cast; ring
      simp only [hcast] at hpb
      rw [hsum2] at hpb
      have hcard : ((({ρ₁, ρ₀} : Finset ℂ)).card : ℝ) = 2 := by
        rw [Finset.card_pair hne.symm]; norm_num
      rw [hcard, ← hα] at hpb
      have hEeq : E = (α ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
          + (2 / 3) * (α ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) + ErrT := hE
      have hF2eq : F2 = 2 * (8 * α / (δ * L)) := hF2
      linarith [htr, hpb, hEeq, hF2eq]
    -- the principal-character bounds
    have hp0 : Work.ZeroFreeTables.SigmaP3L q L 1 s0 a lam₁ ≤ P3AB α a 0 + α * (ε / 4) := by
      have h1 := hζ L hL0ζ (q := q) hLdef.symm s0 hs0re hs0im4 lam₁ hlam₁nn (le_of_lt hbig)
      have hcast : ((a : ℂ) + (lam₁ : ℂ)) = (α : ℂ) := by rw [hα]; push_cast; ring
      have h2 : (P3 (((a : ℂ) + (lam₁ : ℂ)) / ((s0 - 1) * (L : ℂ)))).re = P3AB α a 0 := by
        rw [hcast]
        exact P3term_at_one (a := a) (L := L) (α := α) (t := 0) hLne hs0re (by simp [hs0im])
      rw [h2, ← hα] at h1
      exact h1
    have hp1 : Work.ZeroFreeTables.SigmaP3L q L 1 s1 a lam₁ ≤ P3AB α a μ + α * (ε / 4) := by
      have h1 := hζ L hL0ζ (q := q) hLdef.symm s1 hs1re hs1im4 lam₁ hlam₁nn (le_of_lt hbig)
      have hcast : ((a : ℂ) + (lam₁ : ℂ)) = (α : ℂ) := by rw [hα]; push_cast; ring
      have h2 : (P3 (((a : ℂ) + (lam₁ : ℂ)) / ((s1 - 1) * (L : ℂ)))).re = P3AB α a μ := by
        rw [hcast]
        exact P3term_at_one (a := a) (L := L) (α := α) (t := μ) hLne hs1re (by rw [hs1im, hμ])
      rw [h2, ← hα] at h1
      exact h1
    have hp2 : Work.ZeroFreeTables.SigmaP3L q L 1 s2 a lam₁ ≤ P3AB α a (2 * μ) + α * (ε / 4) := by
      have h1 := hζ L hL0ζ (q := q) hLdef.symm s2 hs2re hs2im4 lam₁ hlam₁nn (le_of_lt hbig)
      have hcast : ((a : ℂ) + (lam₁ : ℂ)) = (α : ℂ) := by rw [hα]; push_cast; ring
      have h2 : (P3 (((a : ℂ) + (lam₁ : ℂ)) / ((s2 - 1) * (L : ℂ)))).re = P3AB α a (2 * μ) := by
        rw [hcast]
        exact P3term_at_one (a := a) (L := L) (α := α) (t := 2 * μ) hLne hs2re (by rw [hs2im, hμ]; ring)
      rw [h2, ← hα] at h1
      exact h1
    -- the pointwise inequality HB (8.5)
    have h85 : 0 ≤ (K ^ 2 + 1 / 2) * (Work.ZeroFreeTables.SigmaP3L q L 1 s0 a lam₁
          + Work.ZeroFreeTables.SigmaP3L q L χ₁ s0 a lam₁)
        + 2 * K * (Work.ZeroFreeTables.SigmaP3L q L 1 s1 a lam₁
          + Work.ZeroFreeTables.SigmaP3L q L χ₁ s1 a lam₁)
        + (1 / 2) * (Work.ZeroFreeTables.SigmaP3L q L 1 s2 a lam₁
          + Work.ZeroFreeTables.SigmaP3L q L χ₁ s2 a lam₁) := by
      have h := HB83aux.hb85 (q := q) χ₁ hsq (K := K) (σ := 1 + a / L) (γ := ρ₀.im)
        (a := a) (lam₁ := lam₁) (by linarith) (by linarith only [haLpos]) ha hlam₁nn
      rw [← hLdef, ← hs0, ← hs1, ← hs2] at h
      exact h
    -- the error bookkeeping
    have hlog4 : Cs * (1 + Amax + Amax ^ 2) * (Real.log L + 2) ^ 4 / L ≤ ε / 4 := by
      have h1 : (Real.log L + 2) ^ 4 ≤ c4 * L := hX4 L hX4L
      have h2 : Cs * (1 + Amax + Amax ^ 2) * (Real.log L + 2) ^ 4
          ≤ Cs * (1 + Amax + Amax ^ 2) * (c4 * L) := by
        apply mul_le_mul_of_nonneg_left h1
        positivity
      have h3 : Cs * (1 + Amax + Amax ^ 2) * (c4 * L) = (ε / 4) * L := by
        have hden : Cs * (1 + Amax + Amax ^ 2) ≠ 0 :=
          mul_ne_zero (ne_of_gt hCs0pos) (ne_of_gt hK1pos)
        rw [hc4, mul_assoc]
        field_simp
      rw [div_le_iff₀ hLpos]
      linarith
    have hbud := error_budget (α := α) (δ := δ) (L := L) (ε := ε) (C := C0) (Ct := Ct)
      (Cs := Cs) (Amax := Amax) hαpos hαAmax hδ0 (le_of_lt hδ1) hε hC0pos.le hCt0pos.le
      hCs0pos.le hL1 hThr hlog4
    have hbud' : E + F1 ≤ α * ε / 2 := by
      rw [hE, hErrT, hCj, hF1]
      linarith only [hbud]
    have hF0le : F0 ≤ F1 := by
      rw [hF0, hF1]
      have hx : 0 ≤ 8 * α / (δ * L) := by positivity
      linarith
    have hF2le : F2 ≤ F1 := by
      rw [hF2, hF1]
      have hx : 0 ≤ 8 * α / (δ * L) := by positivity
      linarith
    have hErr : (K ^ 2 + 1 / 2) * ((a + lam₁) * (1 / 8 + ε / 4) + E + F0)
        + 2 * K * ((a + lam₁) * (1 / 8 + ε / 4) + E + F1)
        + (1 / 2) * ((a + lam₁) * (1 / 8 + ε / 4) + E + F2)
        + ((K ^ 2 + 1 / 2) + 2 * K + 1 / 2) * ((a + lam₁) * (ε / 4))
        ≤ (K + 1) ^ 2 * (a + lam₁) * (1 / 8) + (K + 1) ^ 2 * (a + lam₁) * ε := by
      have hkey : α * (1 / 8 + ε / 4) + E + F1 + α * (ε / 4) ≤ α * (1 / 8) + α * ε := by
        nlinarith [hbud', hαpos, hε]
      have hw0 : (0:ℝ) ≤ K ^ 2 + 1 / 2 := by positivity
      have hw1 : (0:ℝ) ≤ 2 * K := by linarith
      have hw2 : (0:ℝ) ≤ (1 / 2 : ℝ) := by norm_num
      have hsumW : (K ^ 2 + 1 / 2) + 2 * K + 1 / 2 = (K + 1) ^ 2 := by ring
      have hsq : (0:ℝ) ≤ (K + 1) ^ 2 := by positivity
      rw [← hα]
      nlinarith [hkey, hF0le, hF2le, hw0, hw1, hw2, hsumW, hsq]
    exact assembly_core (q := q) χ₁ (a := a) (K := K) (ε := ε) (L := L) (lam₁ := lam₁)
      (lam₀ := lam₀) (μ := μ) (εL := ε / 4) (εP := ε / 4) (E0 := E) (E1 := E) (E2 := E)
      (F0 := F0) (F1 := F1) (F2 := F2) ha hK hlam₁nn hle hcond h85 hχ0 hχ1 hχ2 hp0 hp1 hp2 hErr


end Work.ZeroFreeTables.Table4
