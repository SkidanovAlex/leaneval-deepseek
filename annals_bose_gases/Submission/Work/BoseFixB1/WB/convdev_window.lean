import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.RegimeAux
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.convdev_window` — the quadratic-deviation window

The last (purely arithmetic) conjunct of the regime bundle `window_regime`:
`convDevC M · (R/ℓ)² ≤ 1/4` at FS's parameters, for small diluteness.

The content is that **`M` is the constant `mValue = 48`** (it does not depend on
`μ` at all: `paramsAt μ a = fsParams (μ a³)` and `fsParams` puts `M := mValue`),
so `convDevC (paramsAt μ (a v)).M = convDevC 48` is a *fixed* nonnegative
constant, while the box side grows without bound,

  `ℓ = sideAt μ (a v) = (a v)·(μ (a v)³)^{-163/323}`   (`sideAt_eq_rpow`).

Hence `(R/ℓ)² = (R/(a v))²·(μ (a v)³)^{326/323}` and the product is
`D·(μa³)^{326/323}` with `D = convDevC 48·(R/(a v))² ≥ 0`; taking
`ε₀ := min 1 (((1/4)/(D+1))^{323/326})` makes `t^{326/323} ≤ (1/4)/(D+1)`
whenever `0 < t := μ(a v)³ ≤ ε₀`, whence `D·t^{326/323} ≤ D/(D+1)·(1/4) ≤ 1/4`.
-/

noncomputable section

open scoped Real

namespace Work.BoseFixB1.WB

/-- **The quadratic-deviation window.**  For every fixed radius `R` there is
`ε₀ > 0` such that for all `μ > 0` with `μ (a v)³ ≤ ε₀` the global
quadratic-deviation constant of the localisation function `χ_M` (`M` FS's
regularity integer, `= mValue = 48` at the parameters `paramsAt μ (a v)`)
satisfies `convDevC M·(R/ℓ)² ≤ 1/4`, `ℓ = sideAt μ (a v)`. -/
theorem convdev_window {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hR : 0 < R) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      Submission.BoseGases.convDevC (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        * (R / Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2 ≤ 1 / 4 := by
  -- the value of `a v` is fixed throughout
  set a : ℝ := _root_.BoseGases.a v with ha
  -- `M = 48` for every `μ`, so the deviation constant is a fixed nonnegative
  -- number; `D` is the whole `μ`-independent prefactor of the product.
  set D : ℝ := Submission.BoseGases.convDevC 48 * (R / a) ^ 2 with hDdef
  have hDnn : 0 ≤ D := by
    rw [hDdef]
    exact mul_nonneg (Submission.BoseGases.convDevC_nonneg 48) (sq_nonneg _)
  have hDp1 : 0 < D + 1 := by linarith
  have hxpos : 0 < (1 : ℝ) / 4 / (D + 1) := div_pos (by norm_num) hDp1
  refine ⟨min 1 (((1 : ℝ) / 4 / (D + 1)) ^ (323 / 326 : ℝ)),
    lt_min one_pos (Real.rpow_pos_of_pos hxpos _), ?_⟩
  intro μ hμ hμa
  have htpos : 0 < μ * a ^ 3 := by positivity
  -- the regularity integer of the parameter block
  have hM : (Work.BoseBox.paramsAt μ a).M = 48 := rfl
  -- the box side in closed form
  have hside : Work.BoseBox.sideAt μ a = a * (μ * a ^ 3) ^ (-(163 / 323 : ℝ)) :=
    Work.BoseBox.sideAt_eq_rpow hav hμ
  have hu : ((μ * a ^ 3) ^ (-(163 / 323 : ℝ)))⁻¹ = (μ * a ^ 3) ^ (163 / 323 : ℝ) := by
    rw [← Real.rpow_neg htpos.le]
    congr 1
    norm_num
  have hdiv : R / Work.BoseBox.sideAt μ a
      = (R / a) * (μ * a ^ 3) ^ (163 / 323 : ℝ) := by
    rw [hside, ← hu]
    field_simp
  rw [hM]
  -- `(R/ℓ)² = (R/a)²·(μa³)^{326/323}`
  have hsq : (R / Work.BoseBox.sideAt μ a) ^ 2
      = (R / a) ^ 2 * (μ * a ^ 3) ^ (326 / 323 : ℝ) := by
    rw [hdiv, mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
    norm_num
  have hx0 : 0 ≤ (1 : ℝ) / 4 / (D + 1) := le_of_lt hxpos
  -- `t := μa³` is below the threshold `((1/4)/(D+1))^{323/326}`
  have htx : μ * a ^ 3 ≤ ((1 : ℝ) / 4 / (D + 1)) ^ (323 / 326 : ℝ) :=
    le_trans hμa (min_le_right _ _)
  -- ... hence `t^{326/323} ≤ (1/4)/(D+1)`
  have hpow : (μ * a ^ 3) ^ (326 / 323 : ℝ) ≤ (1 : ℝ) / 4 / (D + 1) := by
    calc (μ * a ^ 3) ^ (326 / 323 : ℝ)
        ≤ (((1 : ℝ) / 4 / (D + 1)) ^ (323 / 326 : ℝ)) ^ (326 / 323 : ℝ) :=
          Real.rpow_le_rpow htpos.le htx (by norm_num)
      _ = ((1 : ℝ) / 4 / (D + 1)) ^ (((323 : ℝ) / 326) * (326 / 323)) := by
            rw [Real.rpow_mul hx0]
      _ = (1 : ℝ) / 4 / (D + 1) := by
            rw [show ((323 : ℝ) / 326) * (326 / 323) = 1 by norm_num, Real.rpow_one]
  calc Submission.BoseGases.convDevC 48 * (R / Work.BoseBox.sideAt μ a) ^ 2
      = D * (μ * a ^ 3) ^ (326 / 323 : ℝ) := by rw [hsq, hDdef]; ring
    _ ≤ D * ((1 : ℝ) / 4 / (D + 1)) := mul_le_mul_of_nonneg_left hpow hDnn
    _ = (D / (D + 1)) * (1 / 4) := by field_simp
    _ ≤ 1 * (1 / 4) := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        rw [div_le_one hDp1]
        linarith
    _ = 1 / 4 := by norm_num

end Work.BoseFixB1.WB
