import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

namespace NakaneData

/-- Unfolding of `rayPt` above level `1`, in the form used for continuity: the point of the
parameter ray is obtained by pulling back `rayPoint θ t` through the Böttcher homeomorphism. -/
theorem rayPt_eq_symm {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : NakaneData Mb Φ) {θ t : ℝ} (ht : 1 < t) :
    rayPt hN θ t = ((hN.e.symm ⟨rayPoint θ t, rayPoint_mem_exteriorDisc ht⟩ : ↥Mbᶜ) : ℂ) := by
  rw [rayPt, dite_eq_left ht]

end NakaneData

/-- The point of a parameter ray depends continuously on the level, on the levels `t > 1`:
`t ↦ rayPoint θ t` is continuous into the exterior disc, and `Φ` has a continuous inverse
there which is continuous as a map to `ℂ`. -/
theorem continuousOn_rayPt {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) (θ : ℝ) :
    ContinuousOn (fun t : ℝ => Work.Top.NakaneData.rayPt hN θ t) (Set.Ioi 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  -- `t ↦ rayPoint θ t` is continuous on the line.
  have hray : Continuous fun t : ℝ => Work.Top.NakaneData.rayPoint θ t := by
    unfold Work.Top.NakaneData.rayPoint
    exact Complex.continuous_ofReal.mul continuous_const
  -- restricted to `Ioi 1` it takes values in the exterior disc, continuously.
  have hp : Continuous fun t : Set.Ioi (1 : ℝ) =>
      (⟨Work.Top.NakaneData.rayPoint θ t.1,
        Work.Top.NakaneData.rayPoint_mem_exteriorDisc t.2⟩ : ↥Work.Top.exteriorDisc) :=
    Continuous.subtype_mk (hray.comp continuous_subtype_val) _
  -- applying the inverse Böttcher homeomorphism and coercing back to `ℂ` is continuous.
  have hg : Continuous fun t : Set.Ioi (1 : ℝ) =>
      ((hN.e.symm (⟨Work.Top.NakaneData.rayPoint θ t.1,
        Work.Top.NakaneData.rayPoint_mem_exteriorDisc t.2⟩ : ↥Work.Top.exteriorDisc) : ↥Mbᶜ) : ℂ) :=
    continuous_subtype_val.comp (hN.e.symm.continuous.comp hp)
  refine hg.congr fun t => ?_
  rw [Set.domRestrict_apply]
  exact (Work.Top.NakaneData.rayPt_eq_symm hN t.2).symm

end Work.Top
