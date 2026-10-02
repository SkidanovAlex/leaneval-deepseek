import Mathlib
import Submission.Work.NAKANE2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open LeanEval.ComplexAnalysis

namespace Work.NAKANE2.Surgery

/-!
# `V_basic` : the elementary properties of the surgery region `V`

For a surgery datum `D` at a parameter `c₀`, the region
`V c₀ D.ρ = {z | T_{c₀} z ∈ ball c₀ (2 ρ)}` is open, contains `0`, is disjoint from the
forward-invariant conformal region `W c₀`, and is mapped into `W c₀` by `T_{c₀}`.

The two non-formal inputs are

* `T_{c₀} z = (conj z)^2 + c₀` is continuous, so `V` is open;
* the Green function scales by `2` under `T_{c₀}` (`Work.ParamRays.greenFun_orbit` in the
  case `n = 1`), together with the band condition of `SurgeryData`: the ball of radius `3ρ`
  lies between the levels `7 g₀/8` and `9 g₀/8` of `G`, where `g₀ = Gcrit c₀ > 0`.
-/

/-- `T_{c₀}` is continuous (it is `z ↦ (conj z)^2 + c₀`). -/
private theorem vb_continuous_Tantibar (c : ℂ) : Continuous (Tantibar c) := by
  unfold Tantibar
  fun_prop

/-- The Green function scales by `2` under `T_{c₀}`: `G(T_{c₀} z) = 2 G z`. -/
private theorem vb_G_Tantibar (c z : ℂ) :
    Work.NAKANE2.G c (Tantibar c z) = 2 * Work.NAKANE2.G c z := by
  show Work.ParamRays.greenFun c (Tantibar c z) = 2 * Work.ParamRays.greenFun c z
  have h1 : Work.ParamRays.orbit c z 1 = Tantibar c z := by
    have h := Work.ParamRays.orbit_succ c z 0
    simpa using h
  rw [← h1, Work.ParamRays.greenFun_orbit, pow_one]

/-- The region `V` of the surgery: it is open, contains the critical point `0`, is disjoint
from the conformal region `W` (the band condition keeps two steps of the orbit apart), and
`T_{c₀}` maps it into `W`. -/
theorem V_basic {c₀ : ℂ} (D : Work.NAKANE2.SurgeryData c₀) :
    IsOpen (Work.NAKANE2.V c₀ D.ρ) ∧ (0 : ℂ) ∈ Work.NAKANE2.V c₀ D.ρ ∧
      Disjoint (Work.NAKANE2.W c₀) (Work.NAKANE2.V c₀ D.ρ) ∧
      (∀ z ∈ Work.NAKANE2.V c₀ D.ρ, LeanEval.ComplexAnalysis.Tantibar c₀ z ∈ Work.NAKANE2.W c₀) := by
  -- the ball of radius `2ρ` on which `V` is modelled sits inside the band of radius `3ρ`
  have hmem_band : ∀ z : ℂ, Tantibar c₀ z ∈ Metric.ball c₀ (2 * D.ρ) →
      Tantibar c₀ z ∈ Metric.closedBall c₀ (3 * D.ρ) := by
    intro z hz
    exact Metric.closedBall_subset_closedBall (by linarith [D.hρ])
      (Metric.ball_subset_closedBall hz)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `V` is the preimage of an open ball under the continuous map `T_{c₀}`
    rw [Work.NAKANE2.V]
    exact Metric.isOpen_ball.preimage (vb_continuous_Tantibar c₀)
  · -- `T_{c₀} 0 = c₀` lies in the ball of radius `2ρ > 0` about itself
    rw [Work.NAKANE2.mem_V, Tantibar, map_zero, zero_pow (by norm_num),
      zero_add, Metric.mem_ball, dist_self]
    linarith [D.hρ]
  · -- a point of `W` has `G(T z) = 2 G z > 3 g₀/2`, but `T z` lies in the band, where
    -- `G < 9 g₀/8`
    rw [Set.disjoint_left]
    intro z hzW hzV
    have hzW' : 3 / 4 * Work.NAKANE2.Gcrit c₀ < Work.NAKANE2.G c₀ z := hzW
    have hzV' : Tantibar c₀ z ∈ Metric.ball c₀ (2 * D.ρ) := hzV
    have hband := D.hband (hmem_band z hzV')
    have h2 := vb_G_Tantibar c₀ z
    have h3 : Work.NAKANE2.G c₀ (Tantibar c₀ z) < 9 / 8 * Work.NAKANE2.Gcrit c₀ := hband.2
    linarith [D.Gcrit_pos]
  · -- conversely the band gives `G(T z) > 7 g₀/8 > 3 g₀/4`
    intro z hz
    rw [Work.NAKANE2.mem_W]
    have hzV' : Tantibar c₀ z ∈ Metric.ball c₀ (2 * D.ρ) := hz
    have h1 : 7 / 8 * Work.NAKANE2.Gcrit c₀ < Work.NAKANE2.G c₀ (Tantibar c₀ z) :=
      (D.hband (hmem_band z hzV')).1
    linarith [D.Gcrit_pos]

end Work.NAKANE2.Surgery
