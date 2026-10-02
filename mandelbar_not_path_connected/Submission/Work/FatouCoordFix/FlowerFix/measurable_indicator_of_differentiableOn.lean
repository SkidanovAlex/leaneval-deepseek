import Mathlib
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoordFix.FlowerFix

/-- If `φ` is differentiable on the open set `Pg`, then the extension of `φ` by zero off `Pg` is
measurable. Indeed on `Pg` the indicator agrees with the restriction of `φ`, which is continuous
(hence measurable) because `φ` is differentiable on `Pg`; and off `Pg` the indicator is
identically zero. Measurability then follows by pasting over the measurable set `Pg` and its
complement. -/
theorem measurable_indicator_of_differentiableOn {φ : ℂ → ℂ} {Pg : Set ℂ} (hopen : IsOpen Pg)
    (hdiff : DifferentiableOn ℂ φ Pg) : Measurable (Pg.indicator φ) := by
  have hPgm : MeasurableSet Pg := hopen.measurableSet
  refine measurable_of_restrict_of_restrict_compl hPgm ?_ ?_
  · -- On `Pg` the indicator agrees with `φ`, which is continuous there.
    have hcont : Continuous (Pg.domRestrict φ) :=
      continuousOn_iff_continuous_domRestrict.mp hdiff.continuousOn
    have heq : Pg.domRestrict (Pg.indicator φ) = Pg.domRestrict φ := by
      funext x
      rw [Set.domRestrict_apply, Set.indicator_of_mem x.2, Set.domRestrict_apply]
    rw [heq]
    exact hcont.measurable
  · -- Off `Pg` the indicator is identically zero.
    have heq : (Pgᶜ).domRestrict (Pg.indicator φ) = fun _ => (0 : ℂ) := by
      funext x
      rw [Set.domRestrict_apply, Set.indicator_of_notMem x.2]
    rw [heq]
    exact measurable_const

end Work.FatouCoordFix.FlowerFix
