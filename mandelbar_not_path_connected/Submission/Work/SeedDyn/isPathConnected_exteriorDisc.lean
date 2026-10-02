/-
# `Work.Top.exteriorDisc` is path connected

`Work.Top.exteriorDisc = {w : ℂ | 1 < ‖w‖}` is the exterior of the closed unit disc in
Böttcher coordinates, i.e. the image of the complement `Mbᶜ` of the connectedness locus under
Nakane's parameter Böttcher coordinate `Φ` (see `Work.Top.NakaneData`).  The proofs of
path-connectedness statements about `Mbᶜ` (which are transported across the homeomorphism
`e : ↥Mbᶜ ≃ₜ ↥exteriorDisc`) start here, so we record that `exteriorDisc` is path connected.

The argument is polar: `exteriorDisc` is the image of `(1, ∞) × S¹` under the continuous map
`(r, u) ↦ r * u`, where `r` is read in `ℂ`.  Both factors are path connected
(`Set.Ioi (1:ℝ)` is convex; `Metric.sphere (0:ℂ) 1` is a sphere in a real vector space of
dimension `> 1`, here `Module.rank ℝ ℂ = 2`), hence so is their product, hence so is its
continuous image.
-/
import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Metric
open scoped Cardinal

namespace Work.SeedDyn

/-- The exterior `{w : ℂ | 1 < ‖w‖}` of the closed unit disc is path connected. -/
theorem isPathConnected_exteriorDisc : IsPathConnected (Work.Top.exteriorDisc) := by
  rw [Work.Top.exteriorDisc]
  have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have hIoi : IsPathConnected (Set.Ioi (1 : ℝ)) :=
    (convex_Ioi 1).isPathConnected ⟨2, by norm_num⟩
  have hsph : IsPathConnected (Metric.sphere (0 : ℂ) 1) :=
    isPathConnected_sphere hrank 0 (by norm_num)
  have hprod : IsPathConnected (Set.Ioi (1 : ℝ) ×ˢ Metric.sphere (0 : ℂ) 1) :=
    hIoi.prod hsph
  have hcont : Continuous fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 :=
    (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd
  -- the polar decomposition of the plane identifies `(1,∞) × S¹` with `exteriorDisc`
  have himg : (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) ''
      (Set.Ioi (1 : ℝ) ×ˢ Metric.sphere (0 : ℂ) 1) = {w : ℂ | 1 < ‖w‖} := by
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨hp1, hp2⟩ := hp
      simp only [Set.mem_Ioi] at hp1
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hp2
      show 1 < ‖(p.1 : ℂ) * p.2‖
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < p.1), hp2, mul_one]
      exact hp1
    · intro hw
      have hwne : w ≠ 0 := by intro h; rw [h] at hw; norm_num at hw
      refine ⟨(‖w‖, w / (‖w‖ : ℂ)), ⟨hw, ?_⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_div, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hwne)]
        exact div_self (by positivity)
      · exact mul_div_cancel₀ w (Complex.ofReal_ne_zero.mpr (norm_pos_iff.mpr hwne).ne')
  rw [← himg]
  exact hprod.image hcont

end Work.SeedDyn
