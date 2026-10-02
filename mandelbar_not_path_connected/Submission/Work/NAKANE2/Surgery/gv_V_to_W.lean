import Mathlib
import Submission.Work.NAKANE2.Defs
import Submission.Work.NAKANE2.Surgery.gv_basic
import Submission.Work.NAKANE2.Surgery.V_basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The deformed map sends the surgery region `V` into the conformal region `W`

Let `D` be a surgery datum at `c₀` and `‖v‖ < rConst D ≤ ρ/2`.  For `z ∈ V c₀ D.ρ` the
deformed value is

`g_v z = T_{c₀} z + χ (T_{c₀} z) · v`,

and since `0 ≤ χ ≤ 1` the perturbation has norm `< ρ/2`.  Now `T_{c₀} z` lies in the ball of
radius `2ρ` about `c₀` (definition of `V`), so

`dist (g_v z) c₀ ≤ dist (g_v z) (T_{c₀} z) + dist (T_{c₀} z) c₀ < ρ/2 + 2ρ < 3ρ`.

Hence `g_v z` lies in the closed ball of radius `3ρ`, which by the band condition of the
surgery datum is contained in `{7 g₀/8 < G < 9 g₀/8}` with `g₀ = Gcrit c₀ > 0`.  Therefore
`G (g_v z) > 7 g₀/8 > 3 g₀/4`, i.e. `g_v z ∈ W c₀`.
-/

namespace Work.NAKANE2.Surgery

open LeanEval.ComplexAnalysis (Tantibar)

/-- The `ℂ`-valued bump `chiC c₀ χ` takes values of norm at most `1`. -/
theorem norm_chiC_le_one {c₀ : ℂ} (χ : ContDiffBump c₀) (z : ℂ) :
    ‖Work.NAKANE2.chiC c₀ χ z‖ ≤ 1 := by
  rw [Work.NAKANE2.chiC]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
  exact χ.le_one

/-- The difference of `g_v z` and the undeformed value `T_{c₀} z` is `χ (T_{c₀} z) · v`, hence
of norm at most `‖v‖`. -/
theorem dist_gv_Tantibar_le {c₀ : ℂ} (D : Work.NAKANE2.SurgeryData c₀) (v z : ℂ) :
    dist (Work.NAKANE2.gv c₀ D.χ v z) (Tantibar c₀ z) ≤ ‖v‖ := by
  rw [Work.NAKANE2.gv_apply, dist_eq_norm, add_sub_cancel_left, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg v) (norm_chiC_le_one D.χ (Tantibar c₀ z))

/-- **The deformed map sends `V` into `W`.**

For `‖v‖ < rConst D` and `z ∈ V c₀ D.ρ`, the perturbation of `T_{c₀} z` stays inside the ball
of radius `3ρ` on which the band condition of `D` holds, so the Green function of `g_v z` is
still above `(3/4) Gcrit c₀`. -/
theorem gv_V_to_W {c₀ : ℂ} (D : Work.NAKANE2.SurgeryData c₀) {v : ℂ}
    (hv : ‖v‖ < Work.NAKANE2.rConst D) {z : ℂ} (hz : z ∈ Work.NAKANE2.V c₀ D.ρ) :
    Work.NAKANE2.gv c₀ D.χ v z ∈ Work.NAKANE2.W c₀ := by
  rw [Work.NAKANE2.mem_V] at hz
  -- `T_{c₀} z` is within `2ρ` of `c₀`
  have hdist₁ : dist (Tantibar c₀ z) c₀ < 2 * D.ρ := by
    rw [← Metric.mem_ball]; exact hz
  -- the perturbation is of size `< ρ/2`
  have hdist₂ : dist (Work.NAKANE2.gv c₀ D.χ v z) (Tantibar c₀ z) < D.ρ / 2 :=
    lt_of_le_of_lt (dist_gv_Tantibar_le D v z) (Work.NAKANE2.norm_lt_half_ρ D hv)
  -- hence `g_v z` lies in the closed ball of radius `3ρ`, where the band condition holds
  have hmem : Work.NAKANE2.gv c₀ D.χ v z ∈ Metric.closedBall c₀ (3 * D.ρ) := by
    rw [Metric.mem_closedBall]
    have htri := dist_triangle (Work.NAKANE2.gv c₀ D.χ v z) (Tantibar c₀ z) c₀
    linarith [D.hρ]
  -- the band condition gives the lower bound on the Green function
  have hband := D.hband hmem
  rw [Work.NAKANE2.mem_W]
  have hpos := D.Gcrit_pos
  linarith [hband.1]

end Work.NAKANE2.Surgery
