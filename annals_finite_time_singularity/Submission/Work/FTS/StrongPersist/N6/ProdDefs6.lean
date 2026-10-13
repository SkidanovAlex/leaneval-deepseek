/-
# `Work.FTS.StrongPersist.N6.ProdDefs6`

Shared vocabulary for the pointwise majorant of the **level-six** product rule (the level-six
shift of `Work.FTS.OpenPkg.ProdOpen.ProdDefs`):

* `SInv6` is the `(γ-1)⁻¹`-block of the majorant, i.e. the contribution of the two products
  `HkSq α 6 f · HkIntegrand α 6 g` and `HkSq α 6 g · HkIntegrand α 6 f`;
* `Texc6` collects the two *exceptional* terms `(D_z⁵f·D_θg·W)²` and `(D_θf·D_z⁵g·W)²`, which are
  the only slots of `HkIntegrand α 6 (f·g)` that are not dominated by `PwAny6` (the pointwise
  bound for mixed derivatives of order `≤ 4`) plus the single-slot bounds `sq_le_HkIntegrand_z` /
  `sq_le_HkIntegrand_mixed`;
* `Maj6` is their sum.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
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

namespace Work.FTS.StrongPersist.N6

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The angular weight `w z / sin(2θ)^{η/2}` carried by the pure `D_z`-slots of `HkIntegrand`. -/
abbrev Hv6 (z θ : ℝ) : ℝ := w z / (Real.sin (2 * θ)) ^ (eta / 2)

/-- The `(γ-1)⁻¹`-block of the level-six majorant: the part priced by the two `ℋ⁶`-norms of the
factors. -/
def SInv6 (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (gam α - 1)⁻¹
    * (HkSq α 6 f * HkIntegrand α 6 g z θ + HkSq α 6 g * HkIntegrand α 6 f z θ)

/-- The two exceptional terms of the `(5,1)`-slot, both carrying the full weight `W`. -/
def Texc6 (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ((DzIter 5 f z θ * Dth g z θ) ^ 2 + (Dth f z θ * DzIter 5 g z θ) ^ 2)
    * (Wt α z θ) ^ 2

/-- The target majorant, as a single expression. -/
def Maj6 (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ := SInv6 α f g z θ + Texc6 α f g z θ

theorem gam_sub_one_pos6 {α : ℝ} (hα : 0 < α) : 0 < gam α - 1 := by
  rw [gam_sub_one]; linarith

theorem gam_sub_one_le_one6 {α : ℝ} (hα1 : α ≤ 1) : gam α - 1 ≤ 1 := by
  rw [gam_sub_one]; linarith

theorem inv_gam_sub_one_nonneg6 {α : ℝ} (hα : 0 < α) : 0 ≤ (gam α - 1)⁻¹ :=
  inv_nonneg.mpr (gam_sub_one_pos6 hα).le

theorem one_le_inv_gam_sub_one6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (1 : ℝ) ≤ (gam α - 1)⁻¹ := by
  rw [one_le_inv₀ (gam_sub_one_pos6 hα)]
  exact gam_sub_one_le_one6 hα1

theorem SInv6_nonneg {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ SInv6 α f g z θ := by
  rw [SInv6]
  refine mul_nonneg (inv_gam_sub_one_nonneg6 hα) ?_
  exact add_nonneg (mul_nonneg (HkSq_nonneg α 6 f) (HkIntegrand_nonneg α 6 g z θ))
    (mul_nonneg (HkSq_nonneg α 6 g) (HkIntegrand_nonneg α 6 f z θ))

theorem Texc6_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) : 0 ≤ Texc6 α f g z θ := by
  rw [Texc6]
  exact mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _)

theorem Maj6_nonneg {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ Maj6 α f g z θ :=
  add_nonneg (SInv6_nonneg hα f g z θ) (Texc6_nonneg α f g z θ)

/-- The `SInv6`-block dominates its first summand. -/
theorem mul_inv_mul_le_SInv6_left {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (gam α - 1)⁻¹ * (HkSq α 6 f * HkIntegrand α 6 g z θ) ≤ SInv6 α f g z θ := by
  rw [SInv6]
  refine mul_le_mul_of_nonneg_left ?_ (inv_gam_sub_one_nonneg6 hα)
  exact le_add_of_nonneg_right (mul_nonneg (HkSq_nonneg α 6 g) (HkIntegrand_nonneg α 6 f z θ))

/-- The `SInv6`-block dominates its second summand. -/
theorem mul_inv_mul_le_SInv6_right {α : ℝ} (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    (gam α - 1)⁻¹ * (HkSq α 6 g * HkIntegrand α 6 f z θ) ≤ SInv6 α f g z θ := by
  rw [SInv6]
  refine mul_le_mul_of_nonneg_left ?_ (inv_gam_sub_one_nonneg6 hα)
  exact le_add_of_nonneg_left (mul_nonneg (HkSq_nonneg α 6 f) (HkIntegrand_nonneg α 6 g z θ))

/-- `n.choose k ≤ 2^n ≤ 64` for `n ≤ 6`, hence `(n.choose k : ℝ)² ≤ 4096`. -/
theorem binom_sq_le_4096 (n k : ℕ) (hkn : k ≤ n) (hn : n ≤ 6) :
    (n.choose k : ℝ) ^ 2 ≤ 4096 := by
  have h1 : n.choose k ≤ 2 ^ n := by
    have h := Finset.single_le_sum (f := fun j => n.choose j) (fun j _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hkn))
    rwa [Nat.sum_range_choose] at h
  have h2 : n.choose k ≤ 64 := by
    calc n.choose k ≤ 2 ^ n := h1
      _ ≤ 2 ^ 6 := pow_le_pow_right₀ (by norm_num) hn
      _ = 64 := by norm_num
  have h3 : (n.choose k : ℝ) ≤ 64 := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (n.choose k : ℝ) := by positivity
  nlinarith [h3, h4]

end Work.FTS.StrongPersist.N6
