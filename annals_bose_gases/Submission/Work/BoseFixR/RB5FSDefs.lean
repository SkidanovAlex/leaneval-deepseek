import ChallengeDeps
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/RB5FSDefs.lean` — the far-leg vocabulary

The far leg `Work.BoseBoxFock.RB5FS v h R (HonestBoxFam v h fc fu HM)` (FS §9,
`prop:FarAway`) is routed through three definitions:

* `bigMV v μ` — FS's window parameter `𝓜 = K_𝓜(μa³)^{-1/4}` of the family
  (`Work.BoseBox.bigM (paramsAt μ (a v)) (a v) μ`);
* `ErrRes v μ ρ` — the *crude* error budget for the residual word
  `KzBogFS + linOpT + Q2ex + Q3T` (the terms of `KzOpFS` other than the
  `c`-number, the gap and the `n₊`-slot).  Every one of them carries a factor
  `ρ` (or `|ρ-μ|`, or `√ρ`), so the budget is a sum of the two monomials
  `(ρ+μ)·a·𝓜` and `(ρ+μ)^{3/2}·a·√(ℓ³𝓜)` with an absolute constant;
* `errLHY v μ` — the LHY margin `8π·lhyC·μ²aℓ³√(μa³)` that the far bound
  `FarBound = -4πμ²aℓ³ + 2·(4π·lhyC·μ²aℓ³√(μa³))` carries on top of the
  mean-field term, which the `(ρ-μ)²`-part of the `c`-number must pay out of
  the margin `4πa(ρ-μ)²ℓ³` of the far region.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixR

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-- FS's window parameter `𝓜 = K_𝓜(μa³)^{-1/4}` at the honest parameters. -/
noncomputable def bigMV (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ :=
  Work.BoseBox.bigM (paramsAt μ (a v)) (a v) μ

/-- **The crude far-leg error budget.**  An absolute constant times the sum of the
two monomials carried by every operator of the residual word,
`(ρ+μ)·(a v)·𝓜` (number, pairing, `Q₂^ex` and the `𝒞`-term) and
`(ρ+μ)^{3/2}·(a v)·√((ℓ v μ)³𝓜)` (the linear and cubic words). -/
noncomputable def ErrRes (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ) : ℝ :=
  10 ^ 300 * ((ρ + μ) * a v * bigMV v μ
    + (ρ + μ) ^ (3 / 2 : ℝ) * a v * Real.sqrt (ell v μ ^ 3 * bigMV v μ))

/-- The LHY margin `2·(4π·lhyC·μ²aℓ³√(μa³))` of the far bound `FarBound`. -/
noncomputable def errLHY (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ :=
  8 * Real.pi * Work.UBB.lhyC * μ ^ 2 * a v * ell3 v μ * Real.sqrt (dil v μ)

lemma errLHY_eq_FarBound (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) :
    FarBound v μ
      = -4 * Real.pi * μ ^ 2 * a v * ell3 v μ + errLHY v μ := by
  unfold FarBound errLHY
  ring

lemma bigMV_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    0 ≤ bigMV v μ := by
  unfold bigMV
  exact le_of_lt (Work.BoseBox.bigM_pos_of_params hμ hav)

lemma ErrRes_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ : ℝ} (hμ : 0 < μ) (hav : 0 < a v)
    (hρ : 0 ≤ ρ) (hℓ : 0 ≤ ell v μ) :
    0 ≤ ErrRes v μ ρ := by
  have h1 : 0 ≤ a v := le_of_lt hav
  have h2 : 0 ≤ bigMV v μ := bigMV_nonneg hμ hav
  have h3 : 0 ≤ ρ + μ := by linarith
  have h4 : 0 ≤ (ρ + μ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg h3 _
  have h5 : 0 ≤ ell v μ ^ 3 * bigMV v μ := mul_nonneg (pow_nonneg hℓ 3) h2
  have h6 : 0 ≤ Real.sqrt (ell v μ ^ 3 * bigMV v μ) := Real.sqrt_nonneg _
  have h7 : 0 ≤ 10 ^ 300 * ((ρ + μ) * a v * bigMV v μ
      + (ρ + μ) ^ (3 / 2 : ℝ) * a v * Real.sqrt (ell v μ ^ 3 * bigMV v μ)) := by
    apply mul_nonneg (by norm_num)
    exact add_nonneg (mul_nonneg (mul_nonneg h3 h1) h2)
      (mul_nonneg (mul_nonneg h4 h1) h6)
  rw [ErrRes]
  linarith

end Work.BoseFixR
