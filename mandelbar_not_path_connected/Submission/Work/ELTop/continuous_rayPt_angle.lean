import Mathlib
import Submission.Work.ELTop.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELTop

/-- The point of a parameter ray depends continuously on the angle, at a fixed level `R > 1`:
`θ ↦ rayPoint θ R` is continuous into the exterior disc, and the Böttcher homeomorphism pulls
it back continuously to the plane. -/
theorem continuous_rayPt_angle {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {R : ℝ} (hR : 1 < R) :
    Continuous fun θ : ℝ => Work.EL.rayPt hN θ R := by
  -- `θ ↦ rayPoint θ R` is continuous on the line.
  have hray : Continuous fun θ : ℝ => Work.Top.NakaneData.rayPoint θ R := by
    unfold Work.Top.NakaneData.rayPoint
    fun_prop
  -- it takes values in the exterior disc.
  have hp : Continuous fun θ : ℝ =>
      (⟨Work.Top.NakaneData.rayPoint θ R,
        Work.Top.NakaneData.rayPoint_mem_exteriorDisc hR⟩ : ↥Work.Top.exteriorDisc) :=
    Continuous.subtype_mk hray _
  -- applying the inverse Böttcher homeomorphism and coercing back to `ℂ` is continuous.
  have hg : Continuous fun θ : ℝ =>
      ((hN.e.symm (⟨Work.Top.NakaneData.rayPoint θ R,
        Work.Top.NakaneData.rayPoint_mem_exteriorDisc hR⟩ : ↥Work.Top.exteriorDisc) :
        ↥(Work.EL.K c)ᶜ) : ℂ) :=
    continuous_subtype_val.comp (hN.e.symm.continuous.comp hp)
  refine hg.congr fun θ => ?_
  rw [Work.EL.rayPt, Work.Top.NakaneData.rayPt, dite_eq_left hR]

end Work.ELTop
