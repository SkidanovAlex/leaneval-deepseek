import Mathlib
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL2.Lavaurs.Windows
import Submission.Work.PARIMPL2.Lavaurs.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Work.PARIMPL2.Lavaurs

open Complex
open Work.Implosion
open Work.Implosion.Approx
open scoped BigOperators

noncomputable section

/-! ## The tools, with the germ-dependent constants made uniform

This file proves `Work.PARIMPL2.Lavaurs.approxEcal_transit_rot_unif` by copying the delivered
per-germ proof `Work.PARIMPL.approxEcal_transit_rot` and replacing the two germ-dependent
constants by constants depending only on `A`, `r`, `B` with `‖h1‖ ≤ B`.

The only genuinely new ingredient is `norm_S_le_rot_B`: the explicit second-order algebraic
constant of `Work.PARIMPL.norm_S_le_rot` (which is uniform in `κ`, using `‖κ‖ ≤ 1 + ‖h1‖`)
is bounded by its value at `B`. -/

/-- The seven-term triangle inequality. -/
private lemma norm_seven_le (x1 x2 x3 x4 x5 x6 x7 : ℂ) :
    ‖x1 + x2 + x3 + x4 + x5 + x6 + x7‖ ≤ ‖x1‖+‖x2‖+‖x3‖+‖x4‖+‖x5‖+‖x6‖+‖x7‖ := by
  have h1 : ‖x1+x2+x3+x4+x5+x6+x7‖ ≤ ‖x1+x2+x3+x4+x5+x6‖ + ‖x7‖ := norm_add_le _ _
  have h2 : ‖x1+x2+x3+x4+x5+x6‖ ≤ ‖x1+x2+x3+x4+x5‖ + ‖x6‖ := norm_add_le _ _
  have h3 : ‖x1+x2+x3+x4+x5‖ ≤ ‖x1+x2+x3+x4‖ + ‖x5‖ := norm_add_le _ _
  have h4 : ‖x1+x2+x3+x4‖ ≤ ‖x1+x2+x3‖ + ‖x4‖ := norm_add_le _ _
  have h5 : ‖x1+x2+x3‖ ≤ ‖x1+x2‖ + ‖x3‖ := norm_add_le _ _
  have h6 : ‖x1+x2‖ ≤ ‖x1‖ + ‖x2‖ := norm_add_le _ _
  linarith

/-- For `0 ≤ x ≤ 1`, `x³ ≤ x²`. -/
private lemma cube_le_sq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x^3 ≤ x^2 := by
  calc x^3 = x^2 * x := by ring
    _ ≤ x^2 * 1 := by gcongr
    _ = x^2 := by ring

/-- **The second-order algebraic estimate in the rotated normalisation, uniform in the germ.**
This is the private `norm_S_le_rot` of `Work.PARIMPL.approxEcal_transit_rot` with the constant
expressed through a bound `B ≥ ‖h1‖` (whence `‖κ‖ = ‖τ − h1/τ‖ ≤ 1 + ‖h1‖ ≤ 1 + B`). -/
private lemma norm_S_le_rot_B (ζ τ h1 κ a e : ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hhe : ‖e‖ ≤ A*‖ζ‖^2) (hκ : κ * τ = τ^2 - h1) (hτ : ‖τ‖ = 1) (hh1 : ‖h1‖ ≤ B)
    (hhz : ‖τ + h1*ζ + e‖ ≤ 3/2) (hζ1 : ‖ζ‖ ≤ 1/4) (ha1 : ‖a‖ ≤ 1/4) :
    ‖τ - (1 - κ*a)*(τ + h1*ζ + e) + (1 - κ*a)*ζ*(τ + h1*ζ + e)^2
        - κ*(ζ + a)*(τ + h1*ζ + e)‖
      ≤ (2*B + 2*A + (B + A)^2 + B*(1 + B) + A + (1 + B)*A + 9*(1 + B)/8)
          * (‖ζ‖^2 + ‖a‖^2) := by
  set hz : ℂ := τ + h1*ζ + e with hzdef
  have hzdecomp : hz = τ + h1*ζ + e := hzdef
  have hhz' : ‖hz‖ ≤ 3/2 := by rw [hzdecomp]; exact hhz
  have hS : τ - (1 - κ*a)*hz + (1 - κ*a)*ζ*hz^2 - κ*(ζ + a)*hz
      = ζ*(τ^2 - h1 - κ*τ) + (2*τ*h1*ζ^2 + 2*τ*ζ*e + ζ*(h1*ζ + e)^2 - h1*κ*ζ^2
          - e - κ*ζ*e - κ*a*ζ*hz^2) := by
    show τ - (1 - κ*a)*hz + (1 - κ*a)*ζ*hz^2 - κ*(ζ + a)*hz
      = ζ*(τ^2 - h1 - κ*τ) + (2*τ*h1*ζ^2 + 2*τ*ζ*e + ζ*(h1*ζ + e)^2 - h1*κ*ζ^2
          - e - κ*ζ*e - κ*a*ζ*hz^2)
    rw [hzdecomp]; ring
  rw [hS, show τ^2 - h1 - κ*τ = 0 from by linear_combination -hκ, mul_zero, zero_add]
  have hζ0 : (0:ℝ) ≤ ‖ζ‖ := norm_nonneg ζ
  have hhz0 : (0:ℝ) ≤ ‖hz‖ := norm_nonneg hz
  have hζsq : ‖ζ‖^2 ≤ ‖ζ‖ := by
    have : (0:ℝ) ≤ ‖ζ‖*(1 - ‖ζ‖) := mul_nonneg hζ0 (by linarith)
    linarith
  have hX1 : ‖2*τ*h1*ζ^2‖ ≤ 2*‖h1‖*‖ζ‖^2 := by
    have heq : ‖2*τ*h1*ζ^2‖ = 2*‖h1‖*‖ζ‖^2 := by
      simp only [norm_mul, norm_pow, Complex.norm_ofNat, hτ, mul_one]
    exact heq.le
  have hX2 : ‖2*τ*ζ*e‖ ≤ 2*A*‖ζ‖^2 := by
    have heq : ‖2*τ*ζ*e‖ = 2*‖ζ‖*‖e‖ := by
      simp only [norm_mul, Complex.norm_ofNat, hτ, mul_one]
    rw [heq]
    have h3 : ‖ζ‖^3 ≤ ‖ζ‖^2 := cube_le_sq hζ0 (by linarith)
    calc 2*‖ζ‖*‖e‖ ≤ 2*‖ζ‖*(A*‖ζ‖^2) := mul_le_mul_of_nonneg_left hhe (by positivity)
      _ = 2*A*‖ζ‖^3 := by ring
      _ ≤ 2*A*‖ζ‖^2 := mul_le_mul_of_nonneg_left h3 (by linarith)
  have hX3 : ‖ζ*(h1*ζ + e)^2‖ ≤ (‖h1‖ + A)^2*‖ζ‖^2 := by
    have h1' : ‖h1*ζ + e‖ ≤ (‖h1‖ + A)*‖ζ‖ := by
      have h2 : ‖h1*ζ + e‖ ≤ ‖h1‖*‖ζ‖ + A*‖ζ‖^2 := by
        have hh2 := norm_add_le (h1*ζ) e
        rw [norm_mul] at hh2
        linarith [hh2, hhe]
      have h3 : A*‖ζ‖^2 ≤ A*‖ζ‖ := mul_le_mul_of_nonneg_left hζsq hA
      calc ‖h1*ζ + e‖ ≤ ‖h1‖*‖ζ‖ + A*‖ζ‖^2 := h2
        _ ≤ ‖h1‖*‖ζ‖ + A*‖ζ‖ := by linarith
        _ = (‖h1‖ + A)*‖ζ‖ := by ring
    have h5 : ‖ζ*(h1*ζ + e)^2‖ = ‖ζ‖ * ‖h1*ζ + e‖^2 := by
      simp only [norm_mul, norm_pow]
    rw [h5]
    have h6 : ‖h1*ζ + e‖^2 ≤ ((‖h1‖ + A)*‖ζ‖)^2 := pow_le_pow_left₀ (norm_nonneg _) h1' 2
    have h7 : ‖ζ‖ * ((‖h1‖ + A)*‖ζ‖)^2 = (‖h1‖ + A)^2 * ‖ζ‖^3 := by ring
    have h3 : ‖ζ‖^3 ≤ ‖ζ‖^2 := cube_le_sq hζ0 (by linarith)
    calc ‖ζ‖ * ‖h1*ζ + e‖^2 ≤ ‖ζ‖ * ((‖h1‖ + A)*‖ζ‖)^2 :=
          mul_le_mul_of_nonneg_left h6 (norm_nonneg ζ)
      _ = (‖h1‖ + A)^2 * ‖ζ‖^3 := h7
      _ ≤ (‖h1‖ + A)^2 * ‖ζ‖^2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
  have hX4 : ‖h1*κ*ζ^2‖ ≤ ‖h1‖*‖κ‖*‖ζ‖^2 := by
    have heq : ‖h1*κ*ζ^2‖ = ‖h1‖*‖κ‖*‖ζ‖^2 := by
      simp only [norm_mul, norm_pow]
    exact heq.le
  have hX5 : ‖e‖ ≤ A*‖ζ‖^2 := hhe
  have hX6 : ‖κ*ζ*e‖ ≤ ‖κ‖*A*‖ζ‖^2 := by
    have heq : ‖κ*ζ*e‖ = ‖κ‖*‖ζ‖*‖e‖ := by
      simp only [norm_mul]
    rw [heq]
    have h3 : ‖ζ‖^3 ≤ ‖ζ‖^2 := cube_le_sq hζ0 (by linarith)
    calc ‖κ‖*‖ζ‖*‖e‖ ≤ ‖κ‖*‖ζ‖*(A*‖ζ‖^2) := mul_le_mul_of_nonneg_left hhe (by positivity)
      _ = ‖κ‖*A*‖ζ‖^3 := by ring
      _ ≤ ‖κ‖*A*‖ζ‖^2 := mul_le_mul_of_nonneg_left h3 (by positivity)
  have hX7 : ‖κ*a*ζ*hz^2‖ ≤ (9*‖κ‖/8)*(‖ζ‖^2 + ‖a‖^2) := by
    have heq : ‖κ*a*ζ*hz^2‖ = ‖κ‖*‖a‖*‖ζ‖*‖hz‖^2 := by
      simp only [norm_mul, norm_pow]
    rw [heq]
    have hhz2 : ‖hz‖^2 ≤ 9/4 := by nlinarith [hhz', hhz0]
    have h9 : ‖κ‖*‖a‖*‖ζ‖*‖hz‖^2 ≤ ‖κ‖*‖a‖*‖ζ‖*(9/4) :=
      mul_le_mul_of_nonneg_left hhz2 (by positivity)
    have h10 : ‖a‖*‖ζ‖ ≤ (‖ζ‖^2 + ‖a‖^2)/2 := by nlinarith [sq_nonneg (‖ζ‖ - ‖a‖)]
    have h11 : (9/4)*‖κ‖*(‖a‖*‖ζ‖) ≤ (9/4)*‖κ‖*((‖ζ‖^2 + ‖a‖^2)/2) :=
      mul_le_mul_of_nonneg_left h10 (by positivity)
    have h12 : ‖κ‖*‖a‖*‖ζ‖*(9/4) = (9/4)*‖κ‖*(‖a‖*‖ζ‖) := by ring
    have h13 : (9/4)*‖κ‖*((‖ζ‖^2 + ‖a‖^2)/2) = (9*‖κ‖/8)*(‖ζ‖^2 + ‖a‖^2) := by ring
    linarith [h9, h11]
  have htri : ‖2*τ*h1*ζ^2 + 2*τ*ζ*e + ζ*(h1*ζ + e)^2 - h1*κ*ζ^2 - e - κ*ζ*e
        - κ*a*ζ*hz^2‖
      ≤ ‖2*τ*h1*ζ^2‖ + ‖2*τ*ζ*e‖ + ‖ζ*(h1*ζ + e)^2‖ + ‖h1*κ*ζ^2‖ + ‖e‖ + ‖κ*ζ*e‖
        + ‖κ*a*ζ*hz^2‖ := by
    have h := norm_seven_le (2*τ*h1*ζ^2) (2*τ*ζ*e) (ζ*(h1*ζ + e)^2) (-(h1*κ*ζ^2)) (-e)
      (-(κ*ζ*e)) (-(κ*a*ζ*hz^2))
    simpa only [norm_neg, sub_eq_add_neg, add_assoc] using h
  refine htri.trans ?_
  have hgoal1 : ‖2*τ*h1*ζ^2‖ + ‖2*τ*ζ*e‖ + ‖ζ*(h1*ζ + e)^2‖ + ‖h1*κ*ζ^2‖ + ‖e‖ + ‖κ*ζ*e‖
        + ‖κ*a*ζ*hz^2‖
      ≤ 2*‖h1‖*‖ζ‖^2 + 2*A*‖ζ‖^2 + (‖h1‖ + A)^2*‖ζ‖^2 + ‖h1‖*‖κ‖*‖ζ‖^2 + A*‖ζ‖^2
        + ‖κ‖*A*‖ζ‖^2 + (9*‖κ‖/8)*(‖ζ‖^2 + ‖a‖^2) := by
    linarith [hX1, hX2, hX3, hX4, hX5, hX6, hX7]
  refine hgoal1.trans ?_
  -- the uniform bound on κ and on the coefficients
  have hτ0 : τ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hτ; norm_num at hτ
  have hκb : ‖κ‖ ≤ 1 + B := by
    have hκeq : κ = (τ^2 - h1)/τ := (eq_div_iff hτ0).mpr hκ
    have h2 : (τ^2 - h1)/τ = τ - h1/τ := by field_simp
    calc ‖κ‖ = ‖τ - h1/τ‖ := by rw [hκeq, h2]
      _ ≤ ‖τ‖ + ‖h1/τ‖ := norm_sub_le _ _
      _ = 1 + ‖h1‖ := by rw [norm_div, hτ, div_one]
      _ ≤ 1 + B := by linarith
  have hκ0 : (0:ℝ) ≤ ‖κ‖ := norm_nonneg κ
  have hh10 : (0:ℝ) ≤ ‖h1‖ := norm_nonneg h1
  have hD : 2*‖h1‖ + 2*A + (‖h1‖ + A)^2 + ‖h1‖*‖κ‖ + A + ‖κ‖*A
      ≤ 2*B + 2*A + (B + A)^2 + B*(1 + B) + A + (1 + B)*A := by
    have h1' : (‖h1‖ + A)^2 ≤ (B + A)^2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2' : ‖h1‖*‖κ‖ ≤ B*(1 + B) := mul_le_mul hh1 hκb hκ0 (by linarith)
    have h3' : ‖κ‖*A ≤ (1 + B)*A := mul_le_mul hκb le_rfl hA (by linarith)
    have h4' : 2*‖h1‖ ≤ 2*B := by linarith
    linarith
  have hD0 : (0:ℝ) ≤ 2*B + 2*A + (B + A)^2 + B*(1 + B) + A + (1 + B)*A := by
    have h1' : (0:ℝ) ≤ (B + A)^2 := sq_nonneg _
    have h2' : (0:ℝ) ≤ B*(1 + B) := mul_nonneg hB (by linarith)
    have h3' : (0:ℝ) ≤ (1 + B)*A := mul_nonneg (by linarith) hA
    have h4' : (0:ℝ) ≤ 2*B := by linarith
    have h5' : (0:ℝ) ≤ 2*A := by linarith
    linarith
  have hE : 9*‖κ‖/8 ≤ 9*(1 + B)/8 := by linarith
  have hexp : 2*‖h1‖*‖ζ‖^2 + 2*A*‖ζ‖^2 + (‖h1‖ + A)^2*‖ζ‖^2 + ‖h1‖*‖κ‖*‖ζ‖^2
        + A*‖ζ‖^2 + ‖κ‖*A*‖ζ‖^2 + (9*‖κ‖/8)*(‖ζ‖^2 + ‖a‖^2)
      = (2*‖h1‖ + 2*A + (‖h1‖+A)^2 + ‖h1‖*‖κ‖ + A + ‖κ‖*A)*‖ζ‖^2
        + (9*‖κ‖/8)*(‖ζ‖^2 + ‖a‖^2) := by ring
  rw [hexp]
  have hle1 : (2*‖h1‖ + 2*A + (‖h1‖+A)^2 + ‖h1‖*‖κ‖ + A + ‖κ‖*A)*‖ζ‖^2
      ≤ (2*B + 2*A + (B + A)^2 + B*(1 + B) + A + (1 + B)*A)*‖ζ‖^2 :=
    mul_le_mul_of_nonneg_right hD (sq_nonneg _)
  have hle2 : (9*‖κ‖/8)*(‖ζ‖^2 + ‖a‖^2) ≤ (9*(1 + B)/8)*(‖ζ‖^2 + ‖a‖^2) :=
    mul_le_mul_of_nonneg_right hE (by positivity)
  have hle3 : (0:ℝ) ≤ (2*B + 2*A + (B + A)^2 + B*(1 + B) + A + (1 + B)*A)*‖a‖^2 :=
    mul_nonneg hD0 (sq_nonneg _)
  linarith [hle1, hle2, hle3]

/-! ## The per-step error, uniform in the germ -/

/-- **The per-step error of the rotated approximate Fatou coordinate, uniform in the germ.** -/
private theorem step_rot_unif (A r B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℂ → ℂ) (τ h1 : ℂ), Work.PARIMPL.ParBounds h τ h1 A r →
      ‖h1‖ ≤ B → ∀ (lam R : ℝ) (a : ℂ), 0 < lam → a = (lam : ℂ) * Complex.I →
      ∀ u : ℂ, Work.PARIMPL.GoodTransitRot a h τ lam R u → ‖Work.Implosion.ecalPt a u‖ < r →
      (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        Complex.sinh (a * (u + (t : ℂ) * Work.Implosion.modelDisp a h u)) / a
          ∈ Complex.slitPlane) →
      ‖Work.Implosion.approxEcal a (τ - h1 / τ) (u + Work.Implosion.modelDisp a h u)
        - Work.Implosion.approxEcal a (τ - h1 / τ) u + τ‖
        ≤ C * (‖Work.Implosion.ecalPt a u‖ ^ 2 + lam ^ 2) := by
  let KB : ℝ := 2*B + 2*A + (B + A)^2 + B*(1 + B) + A + (1 + B)*A + 9*(1 + B)/8
  let C : ℝ := KB + 32*(1 + (1 + B)/4) + 9*(1 + B)/2
  have hKB0 : 0 ≤ KB := by
    dsimp only [KB]
    have h1' : (0:ℝ) ≤ (B + A)^2 := sq_nonneg _
    have h2' : (0:ℝ) ≤ B*(1 + B) := mul_nonneg hB (by linarith)
    have h3' : (0:ℝ) ≤ (1 + B)*A := mul_nonneg (by linarith) hA
    have h4' : (0:ℝ) ≤ 9*(1 + B)/8 := by positivity
    have h5' : (0:ℝ) ≤ 2*B := by linarith
    have h6' : (0:ℝ) ≤ 2*A := by linarith
    linarith
  have hC0 : 0 ≤ C := by dsimp only [C]; nlinarith [hKB0, hB]
  refine ⟨C, hC0, ?_⟩
  intro h τ h1 hb hh1B lam R a hlam ha u hgt hzr hslit
  set κ : ℂ := τ - h1 / τ with hκdef
  have hτnorm : ‖τ‖ = 1 := hb.2.1
  have hτne : τ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hτnorm
    norm_num at hτnorm
  have hκ : κ * τ = τ^2 - h1 := by
    rw [hκdef, sub_mul, div_mul_cancel₀ h1 hτne]
    ring
  have hκb : ‖κ‖ ≤ 1 + B := by
    calc ‖κ‖ = ‖τ - h1/τ‖ := by rw [hκdef]
      _ ≤ ‖τ‖ + ‖h1/τ‖ := norm_sub_le _ _
      _ = 1 + ‖h1‖ := by rw [norm_div, hτnorm, div_one]
      _ ≤ 1 + B := by linarith
  subst ha
  obtain ⟨hstrip, hR4, hsmall, hhτ, hh1, hh2, hZslit⟩ := hgt
  rw [mem_transitStrip_iff] at hstrip
  obtain ⟨hstr1, hstr2⟩ := hstrip
  have hane : ((lam : ℂ) * I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast ne_of_gt hlam) Complex.I_ne_zero
  have hna : ‖((lam : ℂ) * I)‖ = lam := by
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_of_nonneg hlam.le]
  set ζ : ℂ := ecalPt ((lam : ℂ) * I) u with hζdef
  set Φ : ℂ := modelDisp ((lam : ℂ) * I) h u with hΦdef
  simp only [approxEcal]
  set W : ℂ := Complex.sinh (((lam : ℂ) * I) * (u + Φ)) / ((lam : ℂ) * I) with hWdef
  set Z : ℂ := Complex.sinh (((lam : ℂ) * I) * u) / ((lam : ℂ) * I) with hZdef
  have hsum : ‖ζ‖ + lam ≤ 1/4 := by linarith [hsmall]
  have hζle : ‖ζ‖ ≤ 1/4 := by linarith [hsum, norm_nonneg ζ]
  have hlamle : lam ≤ 1/4 := by linarith [hsum, norm_nonneg ζ]
  have hζ3 : ‖h ζ‖ ≤ 3/2 := by
    calc ‖h ζ‖ = ‖(h ζ - τ) + τ‖ := by ring_nf
      _ ≤ ‖h ζ - τ‖ + ‖τ‖ := norm_add_le _ _
      _ ≤ 1/2 + 1 := by rw [hτnorm]; linarith
      _ = 3/2 := by norm_num
  have hζr : ‖ζ‖ < r := by simpa [← hζdef] using hzr
  have he : ‖h ζ - τ - h1*ζ‖ ≤ A*‖ζ‖^2 := hb.2.2.1 ζ hζr
  have hRΦ : ‖Φ + h ζ - ζ*h ζ^2‖ ≤ 32*(‖ζ‖^2 + lam^2) := by
    have h4 : 4 * (‖ecalPt ((lam:ℂ)*I) u‖ + ‖((lam:ℂ)*I)‖) ≤ 1 := by
      have hζ' : ‖ecalPt ((lam:ℂ)*I) u‖ = ‖ζ‖ := by rw [← hζdef]
      rw [hζ', hna]; exact hsmall
    have hres := modelDisp_second_order ((lam:ℂ)*I) h u hane h4 hh2
    simpa [← hΦdef, ← hζdef, hna] using hres
  have hΦn : ‖Φ‖ ≤ 65/16 := by
    have h1 : Φ = (Φ + h ζ - ζ*h ζ^2) - h ζ + ζ*h ζ^2 := by ring
    have htri : ‖(Φ + h ζ - ζ*h ζ^2) - h ζ + ζ*h ζ^2‖
        ≤ ‖Φ + h ζ - ζ*h ζ^2‖ + ‖h ζ‖ + ‖ζ*h ζ^2‖ := by
      have hadd := norm_add_le ((Φ + h ζ - ζ*h ζ^2) - h ζ) (ζ*h ζ^2)
      have hsub2 := norm_sub_le (Φ + h ζ - ζ*h ζ^2) (h ζ)
      linarith [hadd, hsub2]
    have h32 : 32*(‖ζ‖^2 + lam^2) ≤ 2 := by nlinarith [hsum, norm_nonneg ζ]
    have hz1 : ‖ζ*h ζ^2‖ ≤ (1/4)*(3/2)^2 := by
      rw [norm_mul, norm_pow]
      have h2 : ‖h ζ‖^2 ≤ (3/2)^2 := pow_le_pow_left₀ (norm_nonneg _) hζ3 2
      nlinarith [hζle, h2, norm_nonneg ζ]
    rw [h1]
    linarith [htri, hRΦ, h32, hz1, hζ3]
  have hA2decomp : dispNum2 ((lam:ℂ)*I) h u = (ζ + (lam:ℂ)*I) * h ζ := by
    rw [show dispNum2 ((lam:ℂ)*I) h u
        = (ecalPt ((lam:ℂ)*I) u + (lam:ℂ)*I) * h (ecalPt ((lam:ℂ)*I) u) from rfl,
      ← hζdef]
  have hA1decomp : dispNum1 ((lam:ℂ)*I) h u = (ζ - (lam:ℂ)*I) * h ζ := by
    rw [show dispNum1 ((lam:ℂ)*I) h u
        = (ecalPt ((lam:ℂ)*I) u - (lam:ℂ)*I) * h (ecalPt ((lam:ℂ)*I) u) from rfl,
      ← hζdef]
  have hA2le : ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := by
    rw [hA2decomp, norm_mul]
    have h1' : ‖ζ + ((lam:ℂ)*I)‖ ≤ ‖ζ‖ + lam := by
      have := norm_add_le ζ ((lam:ℂ)*I); rwa [hna] at this
    exact mul_le_mul h1' hζ3 (norm_nonneg _) (by positivity)
  have hA2n : ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ 3/8 := by
    calc ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := hA2le
      _ ≤ 3/8 := by nlinarith [hsum]
  have hA1le : ‖dispNum1 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := by
    rw [hA1decomp, norm_mul]
    have h1' : ‖ζ - ((lam:ℂ)*I)‖ ≤ ‖ζ‖ + lam := by
      have := norm_sub_le ζ ((lam:ℂ)*I); rwa [hna] at this
    exact mul_le_mul h1' hζ3 (norm_nonneg _) (by positivity)
  have hA1n : ‖dispNum1 ((lam:ℂ)*I) h u‖ ≤ 3/8 := by
    calc ‖dispNum1 ((lam:ℂ)*I) h u‖ ≤ (‖ζ‖ + lam)*(3/2) := hA1le
      _ ≤ 3/8 := by nlinarith [hsum]
  have hA2small : ‖dispNum2 ((lam:ℂ)*I) h u‖ ≤ 1/2 := by linarith
  have hA1ne : 1 + dispNum1 ((lam:ℂ)*I) h u ≠ 0 := by
    intro hh
    have h2 : dispNum1 ((lam:ℂ)*I) h u = -1 := by linear_combination hh
    rw [h2, norm_neg, norm_one] at hA1n
    linarith
  have hA2ne : 1 + dispNum2 ((lam:ℂ)*I) h u ≠ 0 := by
    intro hh
    have h2 : dispNum2 ((lam:ℂ)*I) h u = -1 := by linear_combination hh
    rw [h2, norm_neg, norm_one] at hA2n
    linarith
  have hEne : ecalE ((lam:ℂ)*I) u ≠ 1 := by
    intro hE
    have hmem : u ∈ periodLattice ((lam:ℂ)*I) := hE
    rw [mem_periodLattice_iff _ _ hane] at hmem
    obtain ⟨n, hn⟩ := hmem
    have hratio : Real.pi * I / ((lam:ℂ)*I) = ((Real.pi/lam : ℝ) : ℂ) := by
      rw [mul_div_mul_right _ _ Complex.I_ne_zero]
      exact (Complex.ofReal_div _ _).symm
    rw [hratio] at hn
    have hure : u.re = (n:ℝ) * (Real.pi/lam) := by
      rw [hn]; simp [Complex.mul_re]
    have hπ : 0 < Real.pi/lam := div_pos Real.pi_pos hlam
    have h1' : (n:ℝ) * (Real.pi/lam) ≥ R := by rw [← hure]; exact hstr1
    have hpos : 0 < (n:ℝ) := by
      by_contra hc
      rw [not_lt] at hc
      nlinarith [h1', hπ, hR4]
    have hposZ : (0:ℤ) < n := by exact_mod_cast hpos
    have hn1 : (1:ℤ) ≤ n := Int.lt_iff_add_one_le.mp hposZ
    have hn1R : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    have h2' : u.re ≥ Real.pi/lam := by
      rw [hure]; nlinarith [hn1R, hπ]
    linarith [hstr2, h2']
  have hWslit : W ∈ Complex.slitPlane := by
    have hh := hslit 1 (by norm_num)
    simpa [hWdef, hΦdef] using hh
  have hZre : 0 < Z.re := by
    rw [hZdef]
    exact sinh_mul_I_div_re_pos lam R hlam hR4 u hstr1 hstr2
  have hWne : W ≠ 0 := Complex.slitPlane_ne_zero hWslit
  have hZne : Z ≠ 0 := Complex.slitPlane_ne_zero hZslit
  have hiden : W * (1 + dispNum2 ((lam:ℂ)*I) h u)
      = Z * Complex.exp (-(((lam:ℂ)*I) * Φ)) := by
    rw [hWdef, hZdef, hΦdef]
    exact sinh_modelDisp_identity ((lam:ℂ)*I) h u hane hA1ne hA2ne hEne
  have hΔ : Complex.log W - Complex.log Z
      = -(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u) := by
    refine eq_of_exp_eq_of_im_lt (Complex.log W - Complex.log Z)
      (-(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)) ?_ ?_
    · rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_log hWne, Complex.exp_log hZne,
        Complex.exp_log hA2ne]
      rw [div_eq_div_iff hZne hA2ne]
      rw [hiden]; ring
    · have hWpi : W.arg < Real.pi := by
        have hWslit' : 0 < W.re ∨ W.im ≠ 0 := hWslit
        rw [Complex.arg_lt_pi_iff]
        rcases hWslit' with hh | hh
        · exact Or.inl (le_of_lt hh)
        · exact Or.inr hh
      have hargW : |W.arg| < Real.pi := (abs_lt).mpr ⟨Complex.neg_pi_lt_arg W, hWpi⟩
      have hargZ : |Z.arg| < Real.pi/2 :=
        Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hZre)
      have hImval : ((Complex.log W - Complex.log Z)
          - (-(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u))).im
          = W.arg - Z.arg + (((lam:ℂ)*I) * Φ).im
            + (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im := by
        simp only [Complex.sub_im, Complex.neg_im, Complex.log_im]
        ring
      rw [hImval]
      have haΦ : |((((lam:ℂ)*I) * Φ)).im| ≤ lam*(65/16) := by
        calc |((((lam:ℂ)*I) * Φ)).im| ≤ ‖((lam:ℂ)*I) * Φ‖ := Complex.abs_im_le_norm _
          _ = ‖((lam:ℂ)*I)‖ * ‖Φ‖ := norm_mul _ _
          _ = lam * ‖Φ‖ := by rw [hna]
          _ ≤ lam*(65/16) := by gcongr
      have hLa2 : |(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im| ≤ 33/64 := by
        have hlog : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u‖ ≤ ‖dispNum2 ((lam:ℂ)*I) h u‖^2 :=
          norm_log_one_add_sub_self_le_of_le_half hA2small
        have h1' : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)‖
            ≤ ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
              - dispNum2 ((lam:ℂ)*I) h u‖ + ‖dispNum2 ((lam:ℂ)*I) h u‖ := by
          have h := norm_add_le (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u) (dispNum2 ((lam:ℂ)*I) h u)
          rwa [sub_add_cancel] at h
        have hnorm : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)‖ ≤ 33/64 := by
          nlinarith [h1', hlog, hA2n, sq_nonneg ‖dispNum2 ((lam:ℂ)*I) h u‖,
            norm_nonneg (dispNum2 ((lam:ℂ)*I) h u)]
        have h2 := Complex.abs_im_le_norm (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u))
        linarith [h2, hnorm]
      have htri : |W.arg - Z.arg + (((lam:ℂ)*I) * Φ).im
          + (Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im|
          ≤ |W.arg - Z.arg| + |((((lam:ℂ)*I) * Φ)).im|
            + |(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im| := by
        have h1 := abs_add_le (W.arg - Z.arg + (((lam:ℂ)*I) * Φ).im)
          ((Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)).im)
        have h2 := abs_add_le (W.arg - Z.arg) ((((lam:ℂ)*I) * Φ).im)
        linarith [h1, h2]
      have hsub : |W.arg - Z.arg| ≤ |W.arg| + |Z.arg| := by
        calc |W.arg - Z.arg| = |W.arg + (-Z.arg)| := by rw [sub_eq_add_neg]
          _ ≤ |W.arg| + |-Z.arg| := abs_add_le _ _
          _ = |W.arg| + |Z.arg| := by rw [abs_neg]
      have hpi : (49:ℝ)/16 < Real.pi := lt_trans (by norm_num) Real.pi_gt_d20
      linarith [htri, hsub, hargW, hargZ, haΦ, hLa2, hpi]
  have happrox : (u + Φ) + κ*Complex.log W - (u + κ*Complex.log Z) + τ
      = Φ + κ*(Complex.log W - Complex.log Z) + τ := by ring
  rw [happrox, hΔ]
  have hsimpl : Φ + κ*(-(((lam:ℂ)*I) * Φ) - Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)) + τ
      = (1 - κ*((lam:ℂ)*I))*Φ + τ - κ*Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u) := by ring
  rw [hsimpl]
  set S : ℂ := τ - (1 - κ*((lam:ℂ)*I))*(h ζ) + (1 - κ*((lam:ℂ)*I))*ζ*(h ζ)^2
      - κ*(ζ + ((lam:ℂ)*I))*(h ζ) with hSdef
  have hdecomp : (1 - κ*((lam:ℂ)*I))*Φ + τ - κ*Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
      = S + (1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)
        - κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u) - dispNum2 ((lam:ℂ)*I) h u) := by
    rw [hSdef, hA2decomp]; ring
  rw [hdecomp]
  have hSbound : ‖S‖ ≤ KB * (‖ζ‖^2 + lam^2) := by
    have hconv : S = τ - (1 - κ*((lam:ℂ)*I))*(τ + h1*ζ + (h ζ - τ - h1*ζ))
        + (1 - κ*((lam:ℂ)*I))*ζ*(τ + h1*ζ + (h ζ - τ - h1*ζ))^2
        - κ*(ζ + ((lam:ℂ)*I))*(τ + h1*ζ + (h ζ - τ - h1*ζ)) := by
      rw [hSdef]; ring
    rw [hconv]
    have hbase : τ + h1*ζ + (h ζ - τ - h1*ζ) = h ζ := by ring
    have hres := norm_S_le_rot_B ζ τ h1 κ ((lam:ℂ)*I) (h ζ - τ - h1*ζ) A B hA hB
      (by simpa using he) hκ hτnorm hh1B (by rw [hbase]; exact hζ3) hζle
      (by rw [hna]; exact hlamle)
    have hna2 : ‖((lam:ℂ)*I)‖^2 = lam^2 := by rw [hna]
    dsimp only [KB]
    rw [← hna2]
    exact hres
  have hRΦb : ‖(1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)‖
      ≤ 32*(1+(1+B)/4)*(‖ζ‖^2 + lam^2) := by
    rw [norm_mul]
    have hconst : ‖1 - κ*((lam:ℂ)*I)‖ ≤ 1 + (1+B)/4 := by
      calc ‖1 - κ*((lam:ℂ)*I)‖ ≤ ‖(1:ℂ)‖ + ‖κ*((lam:ℂ)*I)‖ := norm_sub_le _ _
        _ = 1 + ‖κ‖*lam := by rw [norm_one, norm_mul, hna]
        _ ≤ 1 + (1+B)*lam := by
            have := mul_le_mul_of_nonneg_right hκb hlam.le
            linarith
        _ ≤ 1 + (1+B)/4 := by nlinarith [hlamle, hB]
    calc ‖1 - κ*((lam:ℂ)*I)‖ * ‖Φ + h ζ - ζ*(h ζ)^2‖
        ≤ (1 + (1+B)/4) * (32*(‖ζ‖^2+lam^2)) := by gcongr
      _ = 32*(1+(1+B)/4)*(‖ζ‖^2+lam^2) := by ring
  have hA22 : ‖dispNum2 ((lam:ℂ)*I) h u‖^2 ≤ (9/2)*(‖ζ‖^2 + lam^2) := by
    have h2 : ((‖ζ‖+lam)*(3/2))^2 ≤ (9/2)*(‖ζ‖^2+lam^2) := by
      nlinarith [sq_nonneg (‖ζ‖ - lam), norm_nonneg ζ]
    calc ‖dispNum2 ((lam:ℂ)*I) h u‖^2 ≤ ((‖ζ‖+lam)*(3/2))^2 :=
          pow_le_pow_left₀ (norm_nonneg _) hA2le 2
      _ ≤ (9/2)*(‖ζ‖^2+lam^2) := h2
  have hE2b : ‖κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
        - dispNum2 ((lam:ℂ)*I) h u)‖ ≤ (9*(1+B)/2)*(‖ζ‖^2 + lam^2) := by
    rw [norm_mul]
    have hlog : ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
        - dispNum2 ((lam:ℂ)*I) h u‖ ≤ ‖dispNum2 ((lam:ℂ)*I) h u‖^2 :=
      norm_log_one_add_sub_self_le_of_le_half hA2small
    calc ‖κ‖ * ‖Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
          - dispNum2 ((lam:ℂ)*I) h u‖
        ≤ ‖κ‖ * ‖dispNum2 ((lam:ℂ)*I) h u‖^2 := by gcongr
      _ ≤ (1+B) * ‖dispNum2 ((lam:ℂ)*I) h u‖^2 :=
          mul_le_mul_of_nonneg_right hκb (by positivity)
      _ ≤ (1+B) * ((9/2)*(‖ζ‖^2+lam^2)) := by gcongr
      _ = (9*(1+B)/2)*(‖ζ‖^2+lam^2) := by ring
  have hfin : ‖S + (1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)
        - κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u)‖ ≤ C * (‖ζ‖^2 + lam^2) := by
    have htri2 : ‖S + (1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)
        - κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
            - dispNum2 ((lam:ℂ)*I) h u)‖
        ≤ ‖S‖ + ‖(1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2)‖
          + ‖κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
              - dispNum2 ((lam:ℂ)*I) h u)‖ := by
      have hsub3 := norm_sub_le (S + (1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2))
        (κ*(Complex.log (1 + dispNum2 ((lam:ℂ)*I) h u)
          - dispNum2 ((lam:ℂ)*I) h u))
      have hadd2 := norm_add_le S ((1 - κ*((lam:ℂ)*I))*(Φ + h ζ - ζ*(h ζ)^2))
      linarith [hsub3, hadd2]
    refine htri2.trans ?_
    have hCexp : C = KB + 32*(1+(1+B)/4) + 9*(1+B)/2 := by dsimp only [C]
    rw [hCexp]
    nlinarith [hSbound, hRΦb, hE2b, sq_nonneg ‖ζ‖, sq_nonneg lam]
  exact hfin

/-- Telescoping with a constant step `c`: `f n − f 0 + n·c = ∑_{k<n} (f(k+1) − f k + c)`. -/
private lemma telescopes_mul (f : ℕ → ℂ) (c : ℂ) (N : ℕ) :
    f N - f 0 + (N : ℂ) * c = ∑ k ∈ Finset.range N, (f (k+1) - f k + c) := by
  induction N with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      push_cast
      ring

/-! ## The transit error, uniform in the germ -/

/-- **The transit error of the rotated approximate Écalle coordinate, uniform in the germ.**
`Work.PARIMPL.approxEcal_transit_rot` with the constant depending only on `A`, `r`, `B` (a bound
on `‖h1‖`) — see `Work.PARIMPL2.Lavaurs.approxEcal_step_rot_unif` for why uniformity is needed.
The conclusion `≤ C (1/R + lam)` is the design's `C₁(1/R + λ)` of
`NOTES_LEAD_mandelbar_implosion.md` §3.5 step 2(b).  The proof is the telescoping sum of the
per-step errors `approxEcal_step_rot_unif` (times `n`, controlled by `n ≲ π/λ` through the strip
hypotheses), exactly as in the delivered per-germ version. -/
theorem approxEcal_transit_rot_unif (A r B : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℂ → ℂ) (τ h1 : ℂ), Work.PARIMPL.ParBounds h τ h1 A r →
      ‖h1‖ ≤ B → ∀ (lam R : ℝ) (a : ℂ) (u0 : ℂ) (n : ℕ),
        0 < lam → a = (lam : ℂ) * Complex.I →
      (∀ k : ℕ, k ≤ n → Work.PARIMPL.GoodTransitRot a h τ lam R
        (Work.Implosion.modelOrbit a h k u0)) →
      (∀ k : ℕ, k ≤ n → ‖Work.Implosion.ecalPt a (Work.Implosion.modelOrbit a h k u0)‖ < r) →
      (∀ k : ℕ, k < n → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        Complex.sinh (a * (Work.Implosion.modelOrbit a h k u0
          + (t : ℂ) * Work.Implosion.modelDisp a h (Work.Implosion.modelOrbit a h k u0))) / a
          ∈ Complex.slitPlane) →
      ‖Work.Implosion.approxEcal a (τ - h1 / τ) (Work.Implosion.modelOrbit a h n u0)
        - Work.Implosion.approxEcal a (τ - h1 / τ) u0 + (n : ℂ) * τ‖
        ≤ C * (1 / R + lam) := by
  set B' : ℝ := max B 0 with hB'def
  have hB'0 : 0 ≤ B' := le_max_right B 0
  obtain ⟨Cst, hCst0, hstep⟩ := step_rot_unif A r B' hA hB'0
  refine ⟨Cst * 32200 + 1, by positivity, ?_⟩
  intro h τ h1 hb hh1 lam R a u0 n hlam ha hGT hζr hslit
  have hh1B' : ‖h1‖ ≤ B' := by
    rw [hB'def]; exact le_max_of_le_left hh1
  subst ha
  set aa : ℂ := (lam : ℂ) * I with haa
  -- extract the GoodTransitRot data
  have hR4 : 4 ≤ R := (hGT 0 (Nat.zero_le n)).2.1
  have hsmall : ∀ k : ℕ, k ≤ n → 4 * (‖ecalPt aa (modelOrbit aa h k u0)‖ + lam) ≤ 1 :=
    fun k hk => (hGT k hk).2.2.1
  have hh1 : ∀ k : ℕ, k ≤ n → ‖h (ecalPt aa (modelOrbit aa h k u0)) - 1‖ ≤ 1/2 :=
    fun k hk => (hGT k hk).2.2.2.2.1
  have hstrip : ∀ k : ℕ, k ≤ n →
      R ≤ (modelOrbit aa h k u0).re ∧ (modelOrbit aa h k u0).re ≤ Real.pi/lam - R := by
    intro k hk
    have hk' := (hGT k hk).1
    rwa [mem_transitStrip_iff] at hk'
  have hRpos : (0:ℝ) < R := by linarith
  -- step decrease
  have stepdec : ∀ k : ℕ, k < n →
      (modelOrbit aa h (k+1) u0).re ≤ (modelOrbit aa h k u0).re - 1/40 := by
    intro k hk
    have hk1 : k ≤ n := Nat.le_of_lt hk
    have hs' : ‖ecalPt aa (modelOrbit aa h k u0)‖ + lam ≤ 1/4 := by linarith [hsmall k hk1]
    have hbnd := modelDisp_bounds lam h (modelOrbit aa h k u0) hlam hs' (hh1 k hk1)
    have hsucc : modelOrbit aa h (k+1) u0
        = modelOrbit aa h k u0 + modelDisp aa h (modelOrbit aa h k u0) :=
      modelOrbit_succ aa h k u0
    rw [hsucc, Complex.add_re]
    linarith [hbnd.1]
  -- monotonicity in k
  have hmono : ∀ k : ℕ, k ≤ n →
      (modelOrbit aa h k u0).re ≤ (modelOrbit aa h 0 u0).re - (k:ℝ)/40 := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ j ih =>
        intro hk
        have hj : j < n := Nat.lt_of_succ_le hk
        have hdec := stepdec j hj
        have ih' := ih (Nat.le_of_lt hj)
        push_cast
        linarith
  -- the number of steps is at most 40*pi/lam
  have hn : (n:ℝ) ≤ 40 * Real.pi / lam := by
    rw [mul_div_assoc]
    have hxn := (hstrip n le_rfl).1
    have hx0 := (hstrip 0 (Nat.zero_le n)).2
    have hm := hmono n le_rfl
    linarith
  have hnlam : (n:ℝ) * lam^2 ≤ 40 * Real.pi * lam := by
    have h1 : (n:ℝ) * lam^2 ≤ (40*Real.pi/lam) * lam^2 := by
      have hpos : (0:ℝ) ≤ lam^2 := sq_nonneg lam
      exact mul_le_mul_of_nonneg_right hn hpos
    have h2 : (40*Real.pi/lam) * lam^2 = 40*Real.pi*lam := by field_simp
    rw [h2] at h1; exact h1
  have hlampos : (0:ℝ) < lam := hlam
  -- ===== the main estimate =====
  have htel : approxEcal aa (τ - h1/τ) (modelOrbit aa h n u0)
        - approxEcal aa (τ - h1/τ) u0 + (n : ℂ) * τ
      = ∑ k ∈ Finset.range n,
          (approxEcal aa (τ - h1/τ) (modelOrbit aa h (k+1) u0)
            - approxEcal aa (τ - h1/τ) (modelOrbit aa h k u0) + τ) :=
    telescopes_mul (fun k => approxEcal aa (τ - h1/τ) (modelOrbit aa h k u0)) τ n
  rw [htel]
  -- the per-step error bound
  have herr : ∀ k : ℕ, k < n →
      ‖approxEcal aa (τ - h1/τ) (modelOrbit aa h (k+1) u0)
        - approxEcal aa (τ - h1/τ) (modelOrbit aa h k u0) + τ‖
      ≤ Cst * (‖ecalPt aa (modelOrbit aa h k u0)‖^2 + lam^2) := by
    intro k hk
    have hk1 : k ≤ n := Nat.le_of_lt hk
    have hw : modelOrbit aa h (k+1) u0
        = modelOrbit aa h k u0 + modelDisp aa h (modelOrbit aa h k u0) :=
      modelOrbit_succ aa h k u0
    have hres := hstep h τ h1 hb hh1B' lam R aa hlam haa (modelOrbit aa h k u0)
      (hGT k hk1) (hζr k hk1)
      (by intro t ht; simpa [hw] using hslit k hk t ht)
    simpa [hw] using hres
  -- the sums
  have hSx0 : ∑ k ∈ Finset.range n, (1 / ((modelOrbit aa h k u0).re)^2)
      ≤ 1/R^2 + 1/((1/40)*R) := by
    refine le_trans ?_ (sum_inv_sq_le_of_mono (fun k => (modelOrbit aa h k u0).re) (1/40) R n
      (by norm_num) hRpos (Or.inl stepdec) (fun k hk => (hstrip k hk).1))
    rw [Finset.sum_range_succ]
    have : 0 ≤ 1 / ((modelOrbit aa h n u0).re)^2 := by
      have := (hstrip n le_rfl).1
      positivity
    linarith
  have hSy0 : ∑ k ∈ Finset.range n, (1 / (Real.pi/lam - (modelOrbit aa h k u0).re)^2)
      ≤ 1/R^2 + 1/((1/40)*R) := by
    refine le_trans ?_ (sum_inv_sq_le_of_mono (fun k => Real.pi/lam - (modelOrbit aa h k u0).re)
      (1/40) R n (by norm_num) hRpos
      (Or.inr (fun k hk => by have := stepdec k hk; linarith))
      (fun k hk => by have := (hstrip k hk).2; linarith))
    rw [Finset.sum_range_succ]
    have : 0 ≤ 1 / (Real.pi/lam - (modelOrbit aa h n u0).re)^2 := by
      have hx := (hstrip n le_rfl).2
      have hpos : 0 < Real.pi/lam - (modelOrbit aa h n u0).re := by linarith
      positivity
    linarith
  have hSdk : ∑ k ∈ Finset.range n,
        1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2
      ≤ 2 * (1/R^2 + 1/((1/40)*R)) := by
    have hterm : ∀ k ∈ Finset.range n,
        1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2
        ≤ 1 / ((modelOrbit aa h k u0).re)^2
          + 1 / (Real.pi/lam - (modelOrbit aa h k u0).re)^2 := by
      intro k hk
      have hk' : k < n := Finset.mem_range.mp hk
      have hk1 : k ≤ n := Nat.le_of_lt hk'
      have ha1 := (hstrip k hk1).1
      have ha2 := (hstrip k hk1).2
      exact one_div_min_sq_le _ _ (lt_of_lt_of_le hRpos ha1) (by linarith)
    have hh := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib] at hh
    linarith
  have hSz : ∑ k ∈ Finset.range n, ‖ecalPt aa (modelOrbit aa h k u0)‖^2
      ≤ ∑ k ∈ Finset.range n,
          (10 * (lam + 1/min ((modelOrbit aa h k u0).re)
            (Real.pi/lam - (modelOrbit aa h k u0).re)))^2 := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hk1 : k ≤ n := Nat.le_of_lt hk'
    have ha1 := (hstrip k hk1).1
    have ha2 := (hstrip k hk1).2
    have hb := ecalPt_norm_le_of_re lam (modelOrbit aa h k u0) hlam
      (lt_of_lt_of_le hRpos ha1) (by linarith)
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hSz2 : ∑ k ∈ Finset.range n,
          (10 * (lam + 1/min ((modelOrbit aa h k u0).re)
            (Real.pi/lam - (modelOrbit aa h k u0).re)))^2
      ≤ 10^2 * ∑ k ∈ Finset.range n,
          2 * (lam^2 + 1/(min ((modelOrbit aa h k u0).re)
            (Real.pi/lam - (modelOrbit aa h k u0).re))^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hk1 : k ≤ n := Nat.le_of_lt hk'
    have ha1 := (hstrip k hk1).1
    have ha2 := (hstrip k hk1).2
    have hx : 0 < (modelOrbit aa h k u0).re := lt_of_lt_of_le hRpos ha1
    have hy : 0 < Real.pi/lam - (modelOrbit aa h k u0).re := by linarith
    have h2 : 0 ≤ 1/min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re) :=
      div_nonneg zero_le_one (le_of_lt (lt_min hx hy))
    have hpow : (1/min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2
        = 1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2 := by
      rw [div_pow, one_pow]
    have key : (lam + 1/min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2
        ≤ 2 * (lam^2 + 1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2) := by
      nlinarith [sq_nonneg (lam - 1/min ((modelOrbit aa h k u0).re)
        (Real.pi/lam - (modelOrbit aa h k u0).re)), hpow]
    calc (10 * (lam + 1/min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re)))^2
        = 10^2 * (lam + 1/min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2 := by ring
      _ ≤ 10^2 * (2 * (lam^2 + 1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2)) :=
          mul_le_mul_of_nonneg_left key (by norm_num)
  have hSz3 : ∑ k ∈ Finset.range n,
          2 * (lam^2 + 1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2)
      ≤ 2 * ((n:ℝ) * lam^2 + ∑ k ∈ Finset.range n,
          1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2) := by
    have hsum : ∑ k ∈ Finset.range n,
          2 * (lam^2 + 1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2)
        = 2 * ((n:ℝ) * lam^2 + ∑ k ∈ Finset.range n,
          1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_range_const_real n (lam^2)]
    rw [hsum]
  have hSζ : ∑ k ∈ Finset.range n, ‖ecalPt aa (modelOrbit aa h k u0)‖^2
      ≤ 200 * ((n:ℝ) * lam^2 + 2 * (1/R^2 + 1/((1/40)*R))) := by
    have h1 : ∑ k ∈ Finset.range n,
          2 * (lam^2 + 1/(min ((modelOrbit aa h k u0).re) (Real.pi/lam - (modelOrbit aa h k u0).re))^2)
        ≤ 2 * ((n:ℝ) * lam^2 + 2 * (1/R^2 + 1/((1/40)*R))) := by
      linarith [hSz3, hSdk]
    linarith [hSz, hSz2, h1]
  -- put everything together
  have hmain : ‖∑ k ∈ Finset.range n,
        (approxEcal aa (τ - h1/τ) (modelOrbit aa h (k+1) u0)
          - approxEcal aa (τ - h1/τ) (modelOrbit aa h k u0) + τ)‖
      ≤ Cst * ((∑ k ∈ Finset.range n, ‖ecalPt aa (modelOrbit aa h k u0)‖^2)
          + (n:ℝ) * lam^2) := by
    refine le_trans (norm_sum_le _ _) ?_
    have h1 : ∑ k ∈ Finset.range n,
          ‖approxEcal aa (τ - h1/τ) (modelOrbit aa h (k+1) u0)
            - approxEcal aa (τ - h1/τ) (modelOrbit aa h k u0) + τ‖
        ≤ ∑ k ∈ Finset.range n, Cst * (‖ecalPt aa (modelOrbit aa h k u0)‖^2 + lam^2) :=
      Finset.sum_le_sum (fun k hk => herr k (Finset.mem_range.mp hk))
    have h2 : ∑ k ∈ Finset.range n, Cst * (‖ecalPt aa (modelOrbit aa h k u0)‖^2 + lam^2)
        = Cst * ((∑ k ∈ Finset.range n, ‖ecalPt aa (modelOrbit aa h k u0)‖^2)
          + (n:ℝ) * lam^2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, sum_range_const_real n (lam^2)]
    linarith [h1, h2.le, h2.ge]
  refine le_trans hmain ?_
  -- final arithmetic
  have hbnd : (∑ k ∈ Finset.range n, ‖ecalPt aa (modelOrbit aa h k u0)‖^2) + (n:ℝ) * lam^2
      ≤ 32200 * (1/R + lam) := by
    have hD : 1/R^2 + 1/((1/40)*R) ≤ 41 * (1/R) := by
      have h2 : 1/((1/40)*R) = 40*(1/R) := by field_simp
      have h3 : (1:ℝ)/R^2 ≤ 1/R := by
        have h4 : 1/R ≤ 1 := by
          rw [div_le_one hRpos]
          linarith
        have h5 : 0 ≤ 1/R := by positivity
        calc 1/R^2 = (1/R) * (1/R) := by ring
          _ ≤ 1 * (1/R) := mul_le_mul_of_nonneg_right h4 h5
          _ = 1/R := by ring
      rw [h2]
      linarith
    have h5 : 201 * ((n:ℝ) * lam^2) + 400 * (41 * (1/R))
        ≤ 32200 * (1/R + lam) := by
      have hpi : Real.pi ≤ 4 := Real.pi_le_four
      have h6 : 0 ≤ lam := le_of_lt hlam
      have h7 : 0 ≤ 1/R := by positivity
      have h8 : (n:ℝ) * lam^2 ≤ 40 * Real.pi * lam := hnlam
      nlinarith [hpi, h6, h7, h8]
    linarith [hSζ, hD, h5]
  calc Cst * ((∑ k ∈ Finset.range n, ‖ecalPt aa (modelOrbit aa h k u0)‖^2) + (n:ℝ) * lam^2)
      ≤ Cst * (32200 * (1/R + lam)) := mul_le_mul_of_nonneg_left hbnd hCst0
    _ = (Cst * 32200) * (1/R + lam) := by ring
    _ ≤ (Cst * 32200 + 1) * (1/R + lam) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith

end

end Work.PARIMPL2.Lavaurs
