import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.Gate
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.close_rho_sq_le` — the `(ρ − μ)²` slot of FS's `𝒞`-sum

FS `eq:Close` confines the condensed density to `|ρ − μ| ≤ μK_ℓ⁻²/(2¹⁴π)` (the corrected
threshold `closeThresholdFS`, `F9`).  The `𝒞`-sum of `thm:BogHamDiag` then contributes
`(ρ − μ)²·(ĝ(0)/2)ℓ³·δ` with `ĝ(0) = 8πa` and `δ` the (small) relative slack of the
`κ`-estimate, `δ ≤ C₀·(μa³)(R/a)²`.  This module proves that this contribution lands on
the `(R/a)²√(μa³)` slot of the §11 error bracket `errBracket`:

  `(ρ − μ)²·(ĝ(0)/2)·ℓ³·δ ≤ (C₀/(2²⁶π) + 1)·errBracket v R μ`.

The whole content is the arithmetic identity
`4π/(2²⁸π²)·(2¹⁴π)² = 1/(2²⁶π)` (which is exactly why the constant `1/(2¹⁴π)` of
`closeThresholdFS` is the right one) together with `K_ℓ ≥ 1` at FS's parameters
(`K_ℓ = (μa³)^{-3/646}` and `μa³ ≤ 1`), which supplies `K_ℓ⁻⁴ ≤ 1`; the residual factor
`(R/a)²√(μa³)·√(μa³) = (R/a)²√(μa³)²` is the bracket's second term.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The arithmetic core of `close_rho_sq_le`, in the shape of the estimates supplied by
`eq:Close` (`r := (ρ−μ)²`, `Kp := K_ℓ⁻²`), the `κ`-slack (`hδ`) and the §11 bracket
(`s := √(μa³)`, `Q := (R/a)²`, `X2`, `Ex` the two remaining nonnegative bracket slots).

* `hsq` is `eq:Close` after multiplication by `(2¹⁴π)²` and squaring:
  `(ρ−μ)²(2¹⁴π)² = |ρ−μ|²(2¹⁴π)² ≤ μ²Kp²`;
* `hKp1` is `Kp² = K_ℓ⁻⁴ ≤ 1`;
* the key cancellation is `hid`. -/
private lemma arith_core (A μ Kp t s C₀ Q δ e r X2 Ex : ℝ)
    (hA : 0 ≤ A) (hμ : 0 ≤ μ) (he : 0 ≤ e) (hKp0 : 0 ≤ Kp) (hKp1 : Kp ^ 2 ≤ 1)
    (ht0 : 0 ≤ t) (hs : s * s = t) (hs0 : 0 ≤ s) (hC₀ : 0 ≤ C₀) (hQ : 0 ≤ Q)
    (hX2 : 0 ≤ X2) (hEx : 0 ≤ Ex) (hr0 : 0 ≤ r)
    (hsq : r * ((2 : ℝ) ^ 14 * π) ^ 2 ≤ μ ^ 2 * Kp ^ 2)
    (hδ : δ ≤ C₀ * t * Q) :
    r * (4 * π * A) * e * δ
      ≤ (C₀ / ((2 : ℝ) ^ 26 * π) + 1) * (μ ^ 2 * A * e * s * (X2 + Q * s + Ex)) := by
  have hD : 0 < ((2 : ℝ) ^ 14 * π) ^ 2 := by positivity
  have h4 : 0 ≤ 4 * π * A * e := by positivity
  have hCn : 0 ≤ C₀ * t * Q := by positivity
  have hW : 0 ≤ μ ^ 2 * A * e * t * Q := by positivity
  have hCs : 0 ≤ C₀ / ((2 : ℝ) ^ 26 * π) + 1 := by positivity
  have hr : r ≤ μ ^ 2 * Kp ^ 2 / ((2 : ℝ) ^ 14 * π) ^ 2 := (le_div_iff₀ hD).mpr hsq
  have hkey : Kp ^ 2 * C₀ / ((2 : ℝ) ^ 26 * π) ≤ C₀ / ((2 : ℝ) ^ 26 * π) + 1 := by
    have h2 : 0 < (2 : ℝ) ^ 26 * π := by positivity
    have h1 : Kp ^ 2 * C₀ ≤ C₀ := by nlinarith [hKp1, hKp0, hC₀]
    calc Kp ^ 2 * C₀ / ((2 : ℝ) ^ 26 * π) ≤ C₀ / ((2 : ℝ) ^ 26 * π) :=
          div_le_div_of_nonneg_right h1 h2.le
      _ ≤ C₀ / ((2 : ℝ) ^ 26 * π) + 1 := le_add_of_nonneg_right (by norm_num)
  have hid : μ ^ 2 * Kp ^ 2 / ((2 : ℝ) ^ 14 * π) ^ 2 * (4 * π * A * e)
      = μ ^ 2 * A * e * (Kp ^ 2 / ((2 : ℝ) ^ 26 * π)) := by
    field_simp
    ring
  have hstep4 : Q * t ≤ s * (X2 + Q * s + Ex) := by
    have h1 : Q * s ≤ X2 + Q * s + Ex := by linarith
    calc Q * t = Q * (s * s) := by rw [hs]
      _ = (Q * s) * s := by ring
      _ ≤ (X2 + Q * s + Ex) * s := mul_le_mul_of_nonneg_right h1 hs0
      _ = s * (X2 + Q * s + Ex) := by ring
  have hfin : μ ^ 2 * A * e * t * Q ≤ μ ^ 2 * A * e * s * (X2 + Q * s + Ex) := by
    have h := mul_le_mul_of_nonneg_left hstep4 (by positivity : (0 : ℝ) ≤ μ ^ 2 * A * e)
    nlinarith [h]
  calc r * (4 * π * A) * e * δ
      ≤ r * (4 * π * A) * e * (C₀ * t * Q) := mul_le_mul_of_nonneg_left hδ (by positivity)
    _ = r * (4 * π * A * e) * (C₀ * t * Q) := by ring
    _ ≤ (μ ^ 2 * Kp ^ 2 / ((2 : ℝ) ^ 14 * π) ^ 2) * (4 * π * A * e) * (C₀ * t * Q) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr h4) hCn
    _ = μ ^ 2 * A * e * (Kp ^ 2 / ((2 : ℝ) ^ 26 * π)) * (C₀ * t * Q) := by rw [hid]
    _ = (Kp ^ 2 * C₀ / ((2 : ℝ) ^ 26 * π)) * (μ ^ 2 * A * e * t * Q) := by ring
    _ ≤ (C₀ / ((2 : ℝ) ^ 26 * π) + 1) * (μ ^ 2 * A * e * t * Q) :=
        mul_le_mul_of_nonneg_right hkey hW
    _ ≤ (C₀ / ((2 : ℝ) ^ 26 * π) + 1) * (μ ^ 2 * A * e * s * (X2 + Q * s + Ex)) :=
        mul_le_mul_of_nonneg_left hfin hCs

/-- **A3** (FS `eq:Close` + `eq:Combined1`'s `𝒞`-slot): at the corrected close threshold
`μK_ℓ⁻²/(2¹⁴π)`, the `(ρ − μ)²` contribution of the `𝒞`-sum, with the `κ`-slack
`δ ≤ C₀(μa³)(R/a)²`, is absorbed by the `(R/a)²√(μa³)` slot of the §11 bracket:
`(ρ − μ)²·(ĝ(0)/2)ℓ³·δ ≤ (C₀/(2²⁶π) + 1)·errBracket v R μ`. -/
theorem close_rho_sq_le (v : ℝ³ → ℝ) (R μ ρ δ C₀ gHat0 : ℝ)
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ) (ht : Work.BoseFixR.dil v μ ≤ 1)
    (hg : gHat0 = 8 * π * _root_.BoseGases.a v)
    (hclose : |ρ - μ| ≤ Work.BoseBogFS.closeThresholdFS v μ)
    (hδ : δ ≤ C₀ * Work.BoseFixR.dil v μ * (R / _root_.BoseGases.a v) ^ 2)
    (hC₀ : 0 ≤ C₀) :
    (ρ - μ) ^ 2 * (gHat0 / 2) * Work.BoseFixR.ell3 v μ * δ
      ≤ (C₀ / ((2 : ℝ) ^ 26 * π) + 1) * Work.BoseBogFS.errBracket v R μ := by
  have ht0 : 0 < Work.BoseFixR.dil v μ := by rw [Work.BoseFixR.dil]; positivity
  -- `K_ℓ = (μa³)^{-3/646} > 0` and `1 ≤ K_ℓ` (since `μa³ ≤ 1`)
  have hKl0 : 0 < (Work.BoseBox.paramsAt μ (a v)).Kl := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos (by positivity)
  have hKl1 : 1 ≤ (Work.BoseBox.paramsAt μ (a v)).Kl := by
    have h := Work.BoseBox.fsXp_le_fsXp (t := Work.BoseFixR.dil v μ) (a := (0 : ℝ))
      (b := -(3 / 2)) ht0 ht (by norm_num)
    simpa [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp, Work.BoseFixR.dil,
      Real.rpow_zero] using h
  -- hence `Kp := K_ℓ^{-2}` satisfies `0 ≤ Kp` and `Kp² = K_ℓ^{-4} ≤ 1`
  have hKlp0 : 0 ≤ (Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) :=
    Real.rpow_nonneg hKl0.le _
  have hKlp1 : (Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) ≤ 1 := by
    have h := Real.rpow_le_rpow_of_exponent_le hKl1 (show (-(2 : ℝ)) ≤ 0 by norm_num)
    simpa [Real.rpow_zero] using h
  have hKlp2 : ((Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ))) ^ 2 ≤ 1 := by
    nlinarith [hKlp0, hKlp1]
  -- `eq:Close` multiplied by `2¹⁴π`
  have h2π : 0 < (2 : ℝ) ^ 14 * π := by positivity
  have hmul : |ρ - μ| * ((2 : ℝ) ^ 14 * π)
      ≤ μ * (Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hclose h2π.le
    have he : Work.BoseBogFS.closeThresholdFS v μ * ((2 : ℝ) ^ 14 * π)
        = μ * (Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) := by
      simp only [Work.BoseBogFS.closeThresholdFS]
      rw [div_mul_cancel₀ _ (ne_of_gt h2π)]
    rwa [he] at h
  -- and squared: `(ρ−μ)²(2¹⁴π)² ≤ μ²Kp²`
  have hsq : (ρ - μ) ^ 2 * ((2 : ℝ) ^ 14 * π) ^ 2
      ≤ μ ^ 2 * ((Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ))) ^ 2 := by
    have h1 : (|ρ - μ| * ((2 : ℝ) ^ 14 * π)) ^ 2
        ≤ (μ * (Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (abs_nonneg (ρ - μ)) h2π.le) hmul 2
    simpa only [mul_pow, sq_abs] using h1
  -- `ℓ³ ≥ 0` (`ℓ = K_ℓ(μa)^{-1/2} > 0`)
  have hell3 : 0 ≤ Work.BoseFixR.ell3 v μ := by
    have hℓ : 0 < Work.BoseFixR.ell v μ := by
      simp only [Work.BoseFixR.ell, Work.BoseBox.sideAt, Work.BoseBox.boxSide]
      exact mul_pos hKl0 (Real.rpow_pos_of_pos (by positivity) _)
    simpa only [Work.BoseFixR.ell3] using pow_nonneg hℓ.le 3
  have hs : Real.sqrt (Work.BoseFixR.dil v μ) * Real.sqrt (Work.BoseFixR.dil v μ)
      = Work.BoseFixR.dil v μ := Real.mul_self_sqrt ht0.le
  have hfsX : 0 ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
  have herrExp : 0 ≤ Work.BoseFixR.errExp v μ := by
    simp only [Work.BoseFixR.errExp]
    exact Real.rpow_nonneg ht0.le _
  have hcore := arith_core (a v) μ ((Work.BoseBox.paramsAt μ (a v)).Kl ^ (-(2 : ℝ)))
    (Work.BoseFixR.dil v μ) (Real.sqrt (Work.BoseFixR.dil v μ)) C₀ ((R / a v) ^ 2)
    δ (Work.BoseFixR.ell3 v μ) ((ρ - μ) ^ 2) (Work.BoseFixR.fsX v μ ^ 2)
    (Work.BoseFixR.errExp v μ)
    hav.le hμ.le hell3 hKlp0 hKlp2 ht0.le hs (Real.sqrt_nonneg _) hC₀ (sq_nonneg _)
    hfsX herrExp (sq_nonneg _) hsq hδ
  rw [Work.BoseBogFS.errBracket_eq, show gHat0 / 2 = 4 * π * a v by rw [hg]; ring]
  exact hcore

end Work.BoseBogFS
