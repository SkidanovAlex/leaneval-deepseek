import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB3.CS.Arith` — the parameter arithmetic of the CS step

At FS's parameters `ℓ = sideAt μ a = K_ℓ (μa)^{-1/2}`, so

    μ * a * ℓ² = K_ℓ²        (`mu_a_ell_sq`)

and with the state hypothesis `(n:ℝ) ≤ 2μℓ³` this gives `n·a ≤ 2K_ℓ²ℓ` (`n_mul_a_le`).
Dividing by `ℓ³` yields the two coefficient comparisons of FS `cl:advQ3sch` with
`ε = cK_ℓ⁻²` (in division form; the `zpow` forms of the statement are recovered with
`zpow_neg`):

* `n·a/ℓ³·K_ℓ² ≤ 2K_ℓ²/ℓ²·K_ℓ²` (`coeff_eps_inv_le`, the `ε⁻¹`/`n₊^H`-slot),
* `n·a/ℓ³/K_ℓ² ≤ 2/ℓ²`          (`coeff_eps_le`, the `ε`/`n₊`-slot).

So the final constant `K` in `B3CSRoot` is universal (independent of `μ`).
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Metric Filter

namespace Work.BoseFixB3.CS

set_option autoImplicit false

lemma patAt_Kl_pos (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) : 0 < (patAt μ a).Kl := by
  show 0 < (Work.BoseBox.paramsAt μ a).Kl
  rw [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  exact Work.BoseBox.fsXp_pos (by positivity)

lemma ellAt_pos (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) : 0 < ellAt μ a := by
  show 0 < Work.BoseBox.boxSide (Work.BoseBox.paramsAt μ a) μ a
  exact Work.BoseBox.boxSide_pos hμ ha (patAt_Kl_pos μ a hμ ha)

lemma ellAt_eq (μ a : ℝ) :
    ellAt μ a = (patAt μ a).Kl * (μ * a) ^ (-(1 / 2 : ℝ)) := rfl

/-- `ℓ² = K_ℓ²/(μa)`. -/
lemma ell_sq (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    (ellAt μ a) ^ 2 = ((patAt μ a).Kl) ^ 2 / (μ * a) := by
  have hμa : 0 < μ * a := mul_pos hμ ha
  rw [ellAt_eq, mul_pow]
  have h2 : ((μ * a) ^ (-(1 / 2 : ℝ))) ^ 2 = (μ * a)⁻¹ := by
    rw [← Real.rpow_natCast ((μ * a) ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hμa.le]
    have hexp : (-(1 / 2 : ℝ)) * (2 : ℕ) = -1 := by norm_num
    rw [hexp, Real.rpow_neg_one]
  rw [h2, div_eq_mul_inv]

/-- The single relation behind both coefficient comparisons: `μa·ℓ² = K_ℓ²`. -/
lemma mu_a_ell_sq (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) :
    μ * a * (ellAt μ a) ^ 2 = ((patAt μ a).Kl) ^ 2 := by
  have hμa : μ * a ≠ 0 := ne_of_gt (mul_pos hμ ha)
  rw [ell_sq μ a hμ ha]
  field_simp

/-- With `(n:ℝ) ≤ 2μℓ³`: `n·a ≤ 2K_ℓ²ℓ`. -/
lemma n_mul_a_le (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) {n : ℕ}
    (hn : (n : ℝ) ≤ 2 * μ * (ellAt μ a) ^ 3) :
    (n : ℝ) * a ≤ 2 * ((patAt μ a).Kl) ^ 2 * ellAt μ a := by
  have hℓ := ellAt_pos μ a hμ ha
  have hkey := mu_a_ell_sq μ a hμ ha
  nlinarith [hn, hkey, hℓ, sq_nonneg (ellAt μ a), ha]

/-- `(n:ℝ)·a/ℓ³·K_ℓ² ≤ 2K_ℓ²/ℓ²·K_ℓ²` (the `ε⁻¹`-slot). -/
lemma coeff_eps_inv_le (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) {n : ℕ}
    (hn : (n : ℝ) ≤ 2 * μ * (ellAt μ a) ^ 3) :
    (n : ℝ) * a / (ellAt μ a) ^ 3 * ((patAt μ a).Kl) ^ 2
      ≤ 2 * (((patAt μ a).Kl) ^ 2 / (ellAt μ a) ^ 2) * ((patAt μ a).Kl) ^ 2 := by
  have hℓ := ellAt_pos μ a hμ ha
  have hK := patAt_Kl_pos μ a hμ ha
  have h := n_mul_a_le μ a hμ ha hn
  have h3 : 0 < (ellAt μ a) ^ 3 := by positivity
  have h4 : 0 < (ellAt μ a) ^ 2 := by positivity
  have hdiv : (n : ℝ) * a / (ellAt μ a) ^ 3 ≤ 2 * ((patAt μ a).Kl) ^ 2 / (ellAt μ a) ^ 2 := by
    rw [div_le_div_iff₀ h3 h4]
    nlinarith [h, hℓ, pow_pos hℓ 2]
  calc (n : ℝ) * a / (ellAt μ a) ^ 3 * ((patAt μ a).Kl) ^ 2
      ≤ (2 * ((patAt μ a).Kl) ^ 2 / (ellAt μ a) ^ 2) * ((patAt μ a).Kl) ^ 2 :=
        mul_le_mul_of_nonneg_right hdiv (pow_nonneg hK.le 2)
    _ = 2 * (((patAt μ a).Kl) ^ 2 / (ellAt μ a) ^ 2) * ((patAt μ a).Kl) ^ 2 := by ring

/-- `(n:ℝ)·a/ℓ³/K_ℓ² ≤ 2/ℓ²` (the `ε`-slot). -/
lemma coeff_eps_le (μ a : ℝ) (hμ : 0 < μ) (ha : 0 < a) {n : ℕ}
    (hn : (n : ℝ) ≤ 2 * μ * (ellAt μ a) ^ 3) :
    (n : ℝ) * a / (ellAt μ a) ^ 3 / ((patAt μ a).Kl) ^ 2 ≤ 2 / (ellAt μ a) ^ 2 := by
  have hℓ := ellAt_pos μ a hμ ha
  have hK := patAt_Kl_pos μ a hμ ha
  have h := n_mul_a_le μ a hμ ha hn
  have h3 : 0 < (ellAt μ a) ^ 3 := by positivity
  have h4 : 0 < (ellAt μ a) ^ 2 := by positivity
  have hK2 : 0 < ((patAt μ a).Kl) ^ 2 := by positivity
  have hdiv : (n : ℝ) * a / (ellAt μ a) ^ 3
      ≤ 2 * ((patAt μ a).Kl) ^ 2 * ellAt μ a / (ellAt μ a) ^ 3 :=
    div_le_div_of_nonneg_right h h3.le
  have hsimp : 2 * ((patAt μ a).Kl) ^ 2 * ellAt μ a / (ellAt μ a) ^ 3
      = 2 * ((patAt μ a).Kl) ^ 2 / (ellAt μ a) ^ 2 := by
    field_simp
  rw [hsimp] at hdiv
  calc (n : ℝ) * a / (ellAt μ a) ^ 3 / ((patAt μ a).Kl) ^ 2
      ≤ (2 * ((patAt μ a).Kl) ^ 2 / (ellAt μ a) ^ 2) / ((patAt μ a).Kl) ^ 2 :=
        div_le_div_of_nonneg_right hdiv hK2.le
    _ = 2 / (ellAt μ a) ^ 2 := by
        field_simp

end Work.BoseFixB3.CS
