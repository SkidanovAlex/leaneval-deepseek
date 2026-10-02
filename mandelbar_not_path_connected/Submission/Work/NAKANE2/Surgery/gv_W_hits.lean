import Mathlib
import Submission.Work.NAKANE2.Defs
import Submission.Work.NAKANE2.Surgery.gv_wirtinger
import Submission.Work.NAKANE2.Surgery.gv_V_to_W
import Submission.Work.NAKANE2.Surgery.V_basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Wirtinger derivative `∂g_v` is supported in the surgery region

Let `D` be a surgery datum at `c₀` and `‖v‖ < rConst D`.  The deformed map
`g_v = σ_v ∘ T_{c₀}` has

`∂g_v z = v · ∂̄χ (T_{c₀} z) · 2z`   (`gv_wirtinger`),

so its `∂`-derivative can only be nonzero where the bump `χ` is not locally constant at
`T_{c₀} z`, i.e. only near the ball of radius `ρ` about `c₀`.  The two halves of
`gv_W_hits` are exactly the two consequences of this:

* if `z ∈ W c₀` then `G (T_{c₀} z) = 2 G z > 3 g₀ / 2`, while the band condition gives
  `G < 9 g₀ / 8` on `closedBall c₀ (3ρ) ⊇ supp χ`; hence `T_{c₀} z` lies strictly outside
  the support of `χ`, so `∂̄χ (T_{c₀} z) = 0` and `∂g_v z = 0`;
* if `∂g_v z ≠ 0` then `∂̄χ (T_{c₀} z) ≠ 0`, so `dist (T_{c₀} z) c₀ ≤ ρ`, and since
  `g_v z` differs from `T_{c₀} z` by at most `‖v‖ < ρ/2` we get
  `dist (g_v z) c₀ < 3ρ/2 < 3ρ`; the band condition then gives `G (g_v z) > 7 g₀/8 > 3 g₀/4`,
  i.e. `g_v z ∈ W c₀`.

In other words: the Beltrami coefficient `∂̄g_v / ∂g_v` of the surgery lives where `g_v`
sends its points into the conformal region `W`.
-/

namespace Work.NAKANE2.Surgery

open Filter
open scoped Topology

open LeanEval.ComplexAnalysis (Tantibar)

/-- The Green function doubles under `T_{c₀}`: `G (T_{c₀} z) = 2 G z`. -/
theorem gvW_G_Tantibar (c₀ z : ℂ) :
    Work.NAKANE2.G c₀ (Tantibar c₀ z) = 2 * Work.NAKANE2.G c₀ z := by
  have h := Work.ParamRays.greenFun_orbit c₀ z 1
  rw [Work.ParamRays.orbit_succ, Work.ParamRays.orbit_zero, pow_one] at h
  simpa [Work.NAKANE2.G] using h

/-- The Wirtinger derivative `∂̄` of the bump vanishes strictly outside the outer ball:
if `χ.rOut < dist w c₀` then `χ` is identically `0` on a neighbourhood of `w`. -/
theorem gvW_dzbar_chiC_eq_zero {c₀ : ℂ} (χ : ContDiffBump c₀) {w : ℂ}
    (h : χ.rOut < dist w c₀) : Work.MRMT.dzbar (Work.NAKANE2.chiC c₀ χ) w = 0 := by
  have hcont : ContinuousAt (fun y : ℂ => dist y c₀) w := by fun_prop
  have hev : ∀ᶠ y in nhds w, χ.rOut ≤ dist y c₀ :=
    hcont.eventually (eventually_ge_nhds h)
  have hev0 : Work.NAKANE2.chiC c₀ χ =ᶠ[nhds w] (0 : ℂ → ℂ) := by
    filter_upwards [hev] with y hy
    have hy0 : χ y = 0 := ContDiffBump.zero_of_le_dist χ hy
    change ((χ y : ℝ) : ℂ) = (0 : ℂ)
    rw [hy0, Complex.ofReal_zero]
  have hfd : fderiv ℝ (Work.NAKANE2.chiC c₀ χ) w = 0 := by
    rw [hev0.fderiv_eq]; simp
  simp only [Work.MRMT.dzbar, hfd]
  simp

theorem gv_W_hits {c₀ : ℂ} (D : Work.NAKANE2.SurgeryData c₀) {v : ℂ} (hv : ‖v‖ < Work.NAKANE2.rConst D) :
    (∀ z ∈ Work.NAKANE2.W c₀, Work.MRMT.dz (Work.NAKANE2.gv c₀ D.χ v) z = 0) ∧
      (∀ z : ℂ, Work.MRMT.dz (Work.NAKANE2.gv c₀ D.χ v) z ≠ 0 →
        Work.NAKANE2.gv c₀ D.χ v z ∈ Work.NAKANE2.W c₀) := by
  -- points of `W` keep `T_{c₀} z` strictly outside the support of the bump
  have key : ∀ z ∈ Work.NAKANE2.W c₀, D.ρ < dist (Tantibar c₀ z) c₀ := by
    intro z hz
    by_contra hcon
    have hcon' : dist (Tantibar c₀ z) c₀ ≤ D.ρ := not_lt.mp hcon
    have hmem : Tantibar c₀ z ∈ Metric.closedBall c₀ (3 * D.ρ) := by
      rw [Metric.mem_closedBall]
      linarith [D.hρ]
    have hband := (D.hband hmem).2
    have hG : Work.NAKANE2.G c₀ (Tantibar c₀ z) = 2 * Work.NAKANE2.G c₀ z :=
      gvW_G_Tantibar c₀ z
    rw [Work.NAKANE2.mem_W] at hz
    linarith [D.Gcrit_pos]
  constructor
  · -- `z ∈ W` forces `T_{c₀} z` out of the support, so `∂̄χ (T_{c₀} z) = 0`
    intro z hz
    have h1 := (gv_wirtinger D v z).1
    have h2 : Work.MRMT.dzbar (Work.NAKANE2.chiC c₀ D.χ) (Tantibar c₀ z) = 0 :=
      gvW_dzbar_chiC_eq_zero D.χ (by rw [D.hrOut]; exact key z hz)
    rw [h1, h2]; ring
  · -- conversely `∂g_v z ≠ 0` keeps `T_{c₀} z` near `c₀`, hence `g_v z` in the band
    intro z hdz
    have h1 := (gv_wirtinger D v z).1
    have h2 : Work.MRMT.dzbar (Work.NAKANE2.chiC c₀ D.χ) (Tantibar c₀ z) ≠ 0 := by
      intro hzero
      exact hdz (by rw [h1, hzero]; ring)
    have hdist : dist (Tantibar c₀ z) c₀ ≤ D.ρ := by
      by_contra hcon
      exact h2 (gvW_dzbar_chiC_eq_zero D.χ (by rw [D.hrOut]; exact not_le.mp hcon))
    have hmem : Work.NAKANE2.gv c₀ D.χ v z ∈ Metric.closedBall c₀ (3 * D.ρ) := by
      rw [Metric.mem_closedBall]
      have h3 := dist_gv_Tantibar_le D v z
      have h4 := Work.NAKANE2.norm_lt_half_ρ D hv
      have h5 := dist_triangle (Work.NAKANE2.gv c₀ D.χ v z) (Tantibar c₀ z) c₀
      linarith [D.hρ]
    have hband := (D.hband hmem).1
    rw [Work.NAKANE2.mem_W]
    linarith [D.Gcrit_pos]

end Work.NAKANE2.Surgery
