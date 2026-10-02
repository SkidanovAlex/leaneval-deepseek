import Mathlib
import Submission.Work.Top.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Top

/-- The point of a parameter ray depends continuously on the angle, at a fixed level `R > 1`:
`θ ↦ rayPoint θ R` is a continuous map into the exterior disc, and the Böttcher homeomorphism
`e` (with `e.symm` continuous) pulls it back continuously to the plane. -/
theorem rayPt_angle_continuous {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ) {R : ℝ}
    (hR : 1 < R) : Continuous (fun s : ℝ => Work.Top.NakaneData.rayPt hN s R) := by
  -- `s ↦ rayPoint s R` is continuous on the line.
  have hray : Continuous fun s : ℝ => Work.Top.NakaneData.rayPoint s R := by
    unfold Work.Top.NakaneData.rayPoint
    fun_prop
  -- it takes values in the exterior disc, continuously.
  have hp : Continuous fun s : ℝ =>
      (⟨Work.Top.NakaneData.rayPoint s R,
        Work.Top.NakaneData.rayPoint_mem_exteriorDisc hR⟩ : ↥Work.Top.exteriorDisc) :=
    Continuous.subtype_mk hray _
  -- applying the inverse Böttcher homeomorphism and coercing back to `ℂ` is continuous.
  have hg : Continuous fun s : ℝ =>
      ((hN.e.symm (⟨Work.Top.NakaneData.rayPoint s R,
        Work.Top.NakaneData.rayPoint_mem_exteriorDisc hR⟩ : ↥Work.Top.exteriorDisc) : ↥Mbᶜ) : ℂ) :=
    continuous_subtype_val.comp (hN.e.symm.continuous.comp hp)
  refine hg.congr fun s => ?_
  rw [Work.Top.NakaneData.rayPt, dite_eq_left hR]

end Work.Top
