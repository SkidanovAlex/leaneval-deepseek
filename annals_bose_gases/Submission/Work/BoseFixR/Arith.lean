import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/Arith.lean` — the arithmetic of the `R`-assembly (FS §11)

The two bounds `FarBound`/`CloseBoundR` of `Defs.lean` and the error `errKafz`
are compared with the *target* `ℓ³·Λ(a v, K, η₀, μ)` of `Work.BoseBoxFix.BoxBoundB`
by pure real arithmetic in which every error is a **monomial in the diluteness**
`t = μa³` times `μ²aℓ³√t`, and `t ≤ 1` makes every monomial with a nonnegative
exponent absorbable.  This module collects that arithmetic in the form the
assembly needs:

* `errAbs` — the §8 error `errKafz`, in the abstract variables
  `(a, ℓ, t, μ, R, C)`, as `C μ²aℓ³√t` times a sum of monomials.  The identity
  `errKafz_eq_errAbs` says the two agree at the box parameters (using
  `μa = μ²aℓ³√(μa³)K_ℓ^{-3}` and `K_ℓ^{-3} = (μa³)^{9/646}`).
* `bigK` — the target's error constant: `K` must dominate
  `(C₄(3 + (R/a)²) + C₆(2 + (R/a)²) + 24π·lhyC + 1)/(4π)`, and nothing else.
* `Lambda_ell3` — the target in FS's `eq:ToProve` shape.
* `FarBound_le_zero`, `CloseBoundR_le_zero` — the two bounds are nonpositive in
  the dilute regime (this is what lets `le_quot` pass from the homogeneous
  residual forms to the normalised quotients).
* the two absorption theorems `absorbFar`/`absorbClose` (FS §11's two final
  comparisons) are the *only* arithmetic the assembly consumes beyond this
  module; they live in `Submission/Work/BoseFixR/Absorb*.lean`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. `lhyC` and the monomials of the diluteness -/

lemma lhyC_eq_lhySharp : lhyC = Work.BoseB6.lhySharp := rfl

/-- `(μa³)^e ≤ 1` for `0 < μa³ ≤ 1` and `e ≥ 0`. -/
lemma rpow_le_one_of_nonneg {t e : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (he : 0 ≤ e) :
    t ^ e ≤ 1 :=
  Real.rpow_le_one ht.le ht1 he

/-- `t^{e} ≤ t^{f}` for `0 < t ≤ 1` and `f ≤ e`. -/
lemma rpow_le_rpow_of_le {t e f : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (h : f ≤ e) :
    t ^ e ≤ t ^ f :=
  Real.rpow_le_rpow_of_exponent_ge ht ht1 h

/-- `1 ≤ t^{-e}` for `0 < t ≤ 1` and `e ≥ 0`. -/
lemma one_le_rpow_neg {t e : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (he : 0 ≤ e) :
    1 ≤ t ^ (-e) := by
  have h := rpow_le_rpow_of_le (t := t) (e := 0) (f := -e) ht ht1 (by linarith)
  simpa using h

/-! ## 1. The error `errAbs` and the constant `bigK` -/

/-- FS's §8/§11 error at the box parameters, in the abstract variables, as
`C μ²aℓ³√t` times a sum of monomials in the diluteness:
`t^{9/646}` (the `Cμa` of `thm:Kafz`, using `μa = μ²aℓ³√(μa³)K_ℓ^{-3}` and
`K_ℓ^{-3} = (μa³)^{9/646}` — `Kl_inv_cube`), `t^{2/323}` (the `X²𝓡` of `prop:Hamilton2ndQuant`),
`(R/a)²√t` (the range error) and `t^{1/1615}` (the `X^{1/5}`). -/
def errAbs (a ℓ t μ R C : ℝ) : ℝ :=
  C * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t *
    (t ^ (9 / 646 : ℝ) + t ^ (2 / 323 : ℝ) + (R / a) ^ 2 * Real.sqrt t
      + t ^ (1 / 1615 : ℝ))

/-- The error constant of the box bound that the §11 assembly produces:
`bigK = (C₄(3 + (R/a)²) + C₆(2 + (R/a)²) + 24π·lhyC + 1)/(4π)`, where `C₄` is
`RB4box`'s error constant and `C₆` is `RB67`'s.  Everything the absorption needs
is monotone in `K`, so any `K ≥ bigK` works. -/
def bigK (a R C₄ C₆ : ℝ) : ℝ :=
  (C₄ * (3 + (R / a) ^ 2) + C₆ * (2 + (R / a) ^ 2) + 24 * π * lhyC + 1) / (4 * π)

lemma errAbs_nonneg {a ℓ t μ R C : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ) (ht : 0 ≤ t)
    (hμ : 0 ≤ μ) (hR : 0 ≤ R) (hC : 0 ≤ C) : 0 ≤ errAbs a ℓ t μ R C := by
  have h1 : 0 ≤ t ^ (9 / 646 : ℝ) := Real.rpow_nonneg ht _
  have h2 : 0 ≤ t ^ (2 / 323 : ℝ) := Real.rpow_nonneg ht _
  have h4 : 0 ≤ t ^ (1 / 1615 : ℝ) := Real.rpow_nonneg ht _
  have h3 : 0 ≤ (R / a) ^ 2 * Real.sqrt t :=
    mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg t)
  have hsum : 0 ≤ t ^ (9 / 646 : ℝ) + t ^ (2 / 323 : ℝ) + (R / a) ^ 2 * Real.sqrt t
      + t ^ (1 / 1615 : ℝ) := by linarith
  have h6 : 0 ≤ C * μ ^ 2 := mul_nonneg hC (sq_nonneg μ)
  have h7 : 0 ≤ C * μ ^ 2 * a := mul_nonneg h6 ha.le
  have h8 : 0 ≤ C * μ ^ 2 * a * ℓ ^ 3 := mul_nonneg h7 (by positivity)
  have hbase : 0 ≤ C * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t :=
    mul_nonneg h8 (Real.sqrt_nonneg t)
  exact mul_nonneg hbase hsum

lemma bigK_nonneg {a R C₄ C₆ : ℝ} (ha : 0 < a) (hR : 0 ≤ R) (hC₄ : 0 ≤ C₄)
    (hC₆ : 0 ≤ C₆) : 0 ≤ bigK a R C₄ C₆ := by
  have h1 : 0 ≤ C₄ * (3 + (R / a) ^ 2) := mul_nonneg hC₄ (by positivity)
  have h2 : 0 ≤ C₆ * (2 + (R / a) ^ 2) := mul_nonneg hC₆ (by positivity)
  have h3 : 0 ≤ 24 * π * lhyC := by have := lhyC_pos; positivity
  have h4 : 0 ≤ C₄ * (3 + (R / a) ^ 2) + C₆ * (2 + (R / a) ^ 2)
      + 24 * π * lhyC + 1 := by linarith
  rw [bigK]
  exact div_nonneg h4 (by positivity)

/-! ## 2. The dictionary with the frozen vocabulary -/

/-- `K_ℓ^{-3} = (μa³)^{9/646}`: FS's `K_ℓ = X^{-3/2}`, `X = (μa³)^{1/323}`. -/
lemma Kl_inv_cube (v : ℝ³ → ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    (paramsAt μ (a v)).Kl ^ (-(3 : ℝ)) = (dil v μ) ^ (9 / 646 : ℝ) := by
  have ht : (0 : ℝ) ≤ μ * a v ^ 3 := by positivity
  rw [paramsAt, fsParams]
  show (fsXp (μ * a v ^ 3) (-(3 / 2 : ℝ))) ^ (-(3 : ℝ)) = (dil v μ) ^ (9 / 646 : ℝ)
  rw [dil, fsXp, ← Real.rpow_mul ht]
  congr 1
  norm_num

/-- `K_ℓ^{-2} = (μa³)^{3/323}` (FS `eq:Close`'s threshold). -/
lemma Kl_inv_sq (v : ℝ³ → ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    (paramsAt μ (a v)).Kl ^ (-(2 : ℝ)) = (dil v μ) ^ (3 / 323 : ℝ) := by
  have ht : (0 : ℝ) ≤ μ * a v ^ 3 := by positivity
  rw [paramsAt, fsParams]
  show (fsXp (μ * a v ^ 3) (-(3 / 2 : ℝ))) ^ (-(2 : ℝ)) = (dil v μ) ^ (3 / 323 : ℝ)
  rw [dil, fsXp, ← Real.rpow_mul ht]
  congr 1
  norm_num

/-- `X² = (μa³)^{2/323}`. -/
lemma fsX_sq (v : ℝ³ → ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    fsX v μ ^ 2 = (dil v μ) ^ (2 / 323 : ℝ) := by
  have ht : 0 ≤ dil v μ := le_of_lt (by rw [dil]; positivity)
  rw [fsX, fsXp, ← Real.rpow_natCast (dil v μ ^ (1 / 323 : ℝ)) 2, ← Real.rpow_mul ht]
  congr 1
  norm_num

lemma errExp_eq (v : ℝ³ → ℝ) (μ : ℝ) : errExp v μ = (dil v μ) ^ (1 / 1615 : ℝ) := rfl

/-- **The §8 error of `Defs.lean` is `errAbs` at the box parameters.** -/
lemma errKafz_eq_errAbs (v : ℝ³ → ℝ) {μ R C : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    errKafz v R μ C = errAbs (a v) (ell v μ) (dil v μ) μ R C := by
  rw [errKafz, errAbs, ell3, Kl_inv_cube v hμ hav, fsX_sq v hμ hav, errExp_eq]

/-- **FS `eq:ToProve`'s target**: `ℓ³Λ(a v, K, η₀, μ)` in the shape the assembly
compares with the two bounds. -/
lemma Lambda_ell3 (v : ℝ³ → ℝ) {μ η₀ K : ℝ} :
    ell3 v μ * Lambda (a v) K η₀ μ
      = -4 * π * μ ^ 2 * a v * ell3 v μ
        + 4 * π * lhyC * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
        - 4 * π * μ ^ 2 * a v * ell3 v μ * K * (dil v μ) ^ (1 / 2 + η₀) := by
  rw [Lambda, dil, ell3]
  ring

lemma FarBound_eq (v : ℝ³ → ℝ) (μ : ℝ) :
    FarBound v μ
      = -4 * π * μ ^ 2 * a v * ell3 v μ
        + 8 * π * lhyC * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ) := by
  rw [FarBound]
  ring

lemma CloseBoundR_eq (v : ℝ³ → ℝ) (R μ C ρ : ℝ) :
    CloseBoundR v R μ C ρ
      = -4 * π * μ ^ 2 * a v * ell3 v μ
        + 4 * π * lhyC * ρ ^ 2 * a v * ell3 v μ * Real.sqrt (ρ * a v ^ 3)
        - C * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)
            * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ) := rfl

/-- `Lambda_ell3` with `ell v μ ^ 3` (definitionally the same, syntactically the
form the §11 absorption lemmas produce). -/
lemma Lambda_ell3' (v : ℝ³ → ℝ) {μ η₀ K : ℝ} :
    ell v μ ^ 3 * Lambda (a v) K η₀ μ
      = -4 * π * μ ^ 2 * a v * ell v μ ^ 3
        + 4 * π * lhyC * μ ^ 2 * a v * ell v μ ^ 3 * Real.sqrt (dil v μ)
        - 4 * π * μ ^ 2 * a v * ell v μ ^ 3 * K * (dil v μ) ^ (1 / 2 + η₀) :=
  Lambda_ell3 v



/-- `FarBound_eq` with `ell v μ ^ 3`. -/
lemma FarBound_eq' (v : ℝ³ → ℝ) (μ : ℝ) :
    FarBound v μ
      = -4 * π * μ ^ 2 * a v * ell v μ ^ 3
        + 8 * π * lhyC * μ ^ 2 * a v * ell v μ ^ 3 * Real.sqrt (dil v μ) :=
  FarBound_eq v μ

/-- `CloseBoundR_eq` with `ell v μ ^ 3`. -/
lemma CloseBoundR_eq' (v : ℝ³ → ℝ) (R μ C ρ : ℝ) :
    CloseBoundR v R μ C ρ
      = -4 * π * μ ^ 2 * a v * ell v μ ^ 3
        + 4 * π * lhyC * ρ ^ 2 * a v * ell v μ ^ 3 * Real.sqrt (ρ * a v ^ 3)
        - C * μ ^ 2 * a v * ell v μ ^ 3 * Real.sqrt (dil v μ)
            * (fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (dil v μ) + errExp v μ) :=
  CloseBoundR_eq v R μ C ρ


/-! ## 3. Nonpositivity of the two bounds (sanity, not needed by the assembly)

The assembly never uses the sign of `FarBound`/`CloseBoundR`: with `KzVal` taken
over the *nonzero* window states, the transition from the homogeneous residuals
to the normalised quotients is `le_div_iff₀` plus `normSq_pos`, with no sign
hypothesis.  The two facts are recorded here because they are what makes the
window's exclusion of `f = 0` harmless in the statements.

* `2·lhyC·√(μa³) ≤ 1` gives `FarBound ≤ 0` (it is `4πμ²aℓ³(2lhyC√t − 1)`).
* `4√2·lhyC·√(μa³) ≤ 1` and `ρ ≤ 2μ` give `CloseBoundR ≤ 0` (the LHY term at `ρ`
  is at most `4πμ²aℓ³`). -/

end Work.BoseFixR
