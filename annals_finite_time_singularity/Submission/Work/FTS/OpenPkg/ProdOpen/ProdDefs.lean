/-
# `Work.FTS.OpenPkg.ProdOpen.ProdDefs`

Shared vocabulary for the pointwise majorant of the open-quadrant product rule
(`Work.FTS.OpenPkg.ProdOpen.prod_majorant`):

* `Hv` is the angular weight `w z / sin(2θ)^{η/2}` of the pure `D_z`-slots of `HkIntegrand`;
* `SInv` is the `(γ-1)⁻¹`-block of the majorant, i.e. the contribution of the two products
  `HkSq α 4 f · HkIntegrand α 4 g` and `HkSq α 4 g · HkIntegrand α 4 f`;
* `Texc` collects the two *exceptional* terms `(D_z³f·D_θg·W)²` and `(D_θf·D_z³g·W)²`, which are
  the only slots of `HkIntegrand α 4 (f·g)` that are **not** dominated by `PwAny` (the pointwise
  bound of `Work.FTS.OpenPkg.ProdOpen.PwAny` for mixed derivatives of order `≤ 2`) plus the
  single-slot bounds `sq_le_HkIntegrand_z` / `sq_le_HkIntegrand_mixed`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.ProdOpen

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.Spaces

/-- The angular weight `w z / sin(2θ)^{η/2}` carried by the pure `D_z`-slots of
`HkIntegrand`. -/
def Hv (z θ : ℝ) : ℝ := w z / (Real.sin (2 * θ)) ^ (eta / 2)

/-- The `(γ-1)⁻¹`-block of the majorant of the open-quadrant product rule: this is the part
priced by the two `ℋ⁴`-norms of the factors. -/
def SInv (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (gam α - 1)⁻¹
    * (HkSq α 4 f * HkIntegrand α 4 g z θ + HkSq α 4 g * HkIntegrand α 4 f z θ)

/-- The two exceptional terms of the `(3,1)`-slot, both carrying the full weight `W`: the only
summands of `HkIntegrand α 4 (f·g)` that are out of reach of the pointwise bound `PwAny`. -/
def Texc (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ((DzIter 3 f z θ * Dth g z θ) ^ 2 + (Dth f z θ * DzIter 3 g z θ) ^ 2)
    * (Wt α z θ) ^ 2

/-- The target majorant, as a single expression. -/
def Maj (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ := SInv α f g z θ + Texc α f g z θ

theorem gam_sub_one_pos {α : ℝ} (hα : 0 < α) : 0 < gam α - 1 := by
  rw [gam_sub_one]; linarith

theorem gam_sub_one_le_one {α : ℝ} (hα1 : α ≤ 1) : gam α - 1 ≤ 1 := by
  rw [gam_sub_one]; linarith

theorem inv_gam_sub_one_nonneg {α : ℝ} (hα : 0 < α) : 0 ≤ (gam α - 1)⁻¹ :=
  inv_nonneg.mpr (gam_sub_one_pos hα).le

theorem one_le_inv_gam_sub_one {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) ≤ (gam α - 1)⁻¹ := by
  rw [one_le_inv₀ (gam_sub_one_pos hα)]
  exact gam_sub_one_le_one hα1

theorem SInv_nonneg {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ SInv α f g z θ := by
  rw [SInv]
  refine mul_nonneg (inv_gam_sub_one_nonneg hα) ?_
  exact add_nonneg (mul_nonneg (HkSq_nonneg α 4 f) (HkIntegrand_nonneg α 4 g z θ))
    (mul_nonneg (HkSq_nonneg α 4 g) (HkIntegrand_nonneg α 4 f z θ))

theorem Texc_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ Texc α f g z θ := by
  rw [Texc]
  exact mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

theorem Maj_nonneg {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Maj α f g z θ :=
  add_nonneg (SInv_nonneg hα f g z θ) (Texc_nonneg α f g z θ)

/-- The `SInv`-block dominates its first summand. -/
theorem mul_inv_mul_le_SInv_left {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (gam α - 1)⁻¹ * (HkSq α 4 f * HkIntegrand α 4 g z θ) ≤ SInv α f g z θ := by
  rw [SInv]
  refine mul_le_mul_of_nonneg_left ?_ (inv_gam_sub_one_nonneg hα)
  exact le_add_of_nonneg_right (mul_nonneg (HkSq_nonneg α 4 g) (HkIntegrand_nonneg α 4 f z θ))

/-- The `SInv`-block dominates its second summand. -/
theorem mul_inv_mul_le_SInv_right {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (gam α - 1)⁻¹ * (HkSq α 4 g * HkIntegrand α 4 f z θ) ≤ SInv α f g z θ := by
  rw [SInv]
  refine mul_le_mul_of_nonneg_left ?_ (inv_gam_sub_one_nonneg hα)
  exact le_add_of_nonneg_left (mul_nonneg (HkSq_nonneg α 4 f) (HkIntegrand_nonneg α 4 g z θ))

end Work.FTS.OpenPkg.ProdOpen
