import Mathlib
import Submission.Work.Top.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A periodic injective curve on `[a, a+1)` is a Jordan curve

If `F : ℝ → ℂ` has period `1` at `a` (i.e. `F (a + 1) = F a`), is continuous on the closed
interval `[a, a + 1]` and injective on the half-open interval `[a, a + 1)`, then the image
`F '' [a, a + 1)` is a Jordan curve: the descended map `AddCircle.liftIco 1 a F` on the circle
`AddCircle (1 : ℝ)` is continuous (this uses continuity on `[a, a+1]` and the agreement
`F a = F (a + 1)`), injective (from injectivity of `F` on the fundamental domain `[a, a+1)`),
and has range exactly `F '' [a, a + 1)`.
-/

namespace Work.ELTop

/-- The range of the descended map `AddCircle.liftIco 1 a F` is the image of the fundamental
half-open interval `[a, a + 1)`. -/
theorem range_liftIco_one (F : ℝ → ℂ) (a : ℝ) :
    Set.range (AddCircle.liftIco (1 : ℝ) a F) = F '' Set.Ico a (a + 1) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨((AddCircle.equivIco (1 : ℝ) a x : Set.Ico a (a + 1)) : ℝ),
      (AddCircle.equivIco (1 : ℝ) a x).2, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨(t : AddCircle (1 : ℝ)), AddCircle.liftIco_coe_apply ht⟩

/-- The descended map `AddCircle.liftIco 1 a F` is injective when `F` is injective on
the fundamental domain `[a, a + 1)`. -/
theorem liftIco_one_injective {F : ℝ → ℂ} {a : ℝ}
    (hinj : Set.InjOn F (Set.Ico a (a + 1))) :
    Function.Injective (AddCircle.liftIco (1 : ℝ) a F) := by
  intro x y hxy
  have hx := (AddCircle.equivIco (1 : ℝ) a x).2
  have hy := (AddCircle.equivIco (1 : ℝ) a y).2
  have key : F (((AddCircle.equivIco (1 : ℝ) a x : Set.Ico a (a + 1)) : ℝ))
      = F (((AddCircle.equivIco (1 : ℝ) a y : Set.Ico a (a + 1)) : ℝ)) := hxy
  exact (AddCircle.equivIco (1 : ℝ) a).injective (Subtype.ext (hinj hx hy key))

theorem isJordanCurve_range_liftIco {F : ℝ → ℂ} {a : ℝ}
    (hper : F (a + 1) = F a) (hcont : ContinuousOn F (Set.Icc a (a + 1)))
    (hinj : Set.InjOn F (Set.Ico a (a + 1))) :
    Work.Top.IsJordanCurve (F '' Set.Ico a (a + 1)) := by
  refine ⟨⟨AddCircle.liftIco (1 : ℝ) a F,
    AddCircle.liftIco_continuous hper.symm (by simpa using hcont)⟩, ?_, ?_⟩
  · exact liftIco_one_injective hinj
  · exact range_liftIco_one F a

end Work.ELTop
