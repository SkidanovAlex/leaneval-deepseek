import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Flower.tangency_of_antiholomorphic_root
import Submission.Work.FatouCoord.Flower.norm_star_sub_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The antiholomorphic square root `gU` of a parabolic germ is tangent to conjugation

Let `f` be a parabolic germ with `ParabolicBounds f h a r A A'` and let `gU` be an
antiholomorphic square root of `f` (`gU ∘ gU = f`, `gU 0 = 0`, and `star ∘ gU` holomorphic).
Writing `U = star ∘ gU` for the holomorphic map, the identity `gU ∘ gU = f` reads
`f u = star (U (star (U u)))`, so `U` is an antiholomorphic-root presentation of the parabolic
germ; `tangency_of_antiholomorphic_root` gives `deriv U 0 = 1`, and `norm_star_sub_le` then
yields `‖gU u - star u‖ = ‖star (U u) - star u‖ = O(‖u‖ ^ 2)`.
-/

open scoped Topology
open Filter Metric

namespace Work.FatouCoord.Flower

noncomputable section

theorem gU_tangent_sq {f gU h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} (hb : Work.FatouCoord.ParabolicBounds f h a r A A') (hgU_anti : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (gU z)) z) (hgg : gU ∘ gU = f) (hgU0 : gU 0 = 0) : ∃ C ρ : ℝ, 0 < ρ ∧ ∀ u : ℂ, ‖u‖ < ρ → ‖gU u - star u‖ ≤ C * ‖u‖ ^ 2 := by
  set U : ℂ → ℂ := fun z => star (gU z) with hU
  have hUdiff : Differentiable ℂ U := fun z => hgU_anti z
  have hUan : AnalyticAt ℂ U 0 := hUdiff.analyticAt 0
  have hU0 : U 0 = 0 := by simp [hU, hgU0]
  have hgg' : ∀ u : ℂ, gU (gU u) = f u := by
    intro u
    have h := congrFun hgg u
    simpa [Function.comp_apply] using h
  have hf : ∀ u : ℂ, ‖u‖ < r → f u = star (U (star (U u))) := by
    intro u _
    rw [← hgg' u]
    simp only [hU, star_star]
  have hfh : ∀ u : ℂ, ‖u‖ < r → f u = u + u ^ 2 * h u :=
    fun u hu => hb.f_eq u (mem_ball_zero_iff.mpr hu)
  have hh : DifferentiableAt ℂ h 0 :=
    hb.h_diff.differentiableAt (ball_mem_nhds 0 hb.hr)
  have hh0 : h 0 = 1 := by
    have h1 : ‖h 0 - 1‖ ≤ 0 := by
      have h2 := hb.h_close 0 (by simpa using hb.hr)
      simpa using h2
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h1)
  have htang := tangency_of_antiholomorphic_root hb.hr hUan hU0 hf hfh hh hh0
    (rfl : deriv h 0 = deriv h 0)
  have hderiv : deriv U 0 = 1 := htang.1
  obtain ⟨C, ρ, hρ, hbound⟩ := norm_star_sub_le hUan hU0 hderiv
  refine ⟨C, ρ, hρ, fun u hu => ?_⟩
  have h1 := hbound u hu
  rwa [show star (U u) = gU u by simp [hU]] at h1

end

end Work.FatouCoord.Flower
