import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotC5N3.AK
import Submission.Work.MotC5N3.CensusAux
import Submission.Work.MotV5.ASChart.ASChartIsoL2

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3

open MvPolynomial

/-- `K[X₀,X₁,X₂]` is a ring of characteristic `5` when `K` is. -/
theorem charFive_poly (K : Type) [CommRing K] [CharP K 5] :
    (5 : MvPolynomial (Fin 3) K) = 0 := by
  have h : ((5 : ℕ) : MvPolynomial (Fin 3) K) = 0 := by
    rw [← map_natCast (C : K →+* MvPolynomial (Fin 3) K) 5, CharP.cast_eq_zero K 5, map_zero]
  simpa using h

/-- **The generic polar factor `linAS2L` is a unit**: it is the constant `-2 (a² - ab - b²)` and
`2` is a unit of `K[X₀,X₁,X₂]` in characteristic `5` while `a² - ab - b² ≠ 0`. -/
theorem isUnit_linAS2L {K : Type} [Field K] [CharP K 5] (a b : K)
    (hab : a ^ 2 - a * b - b ^ 2 ≠ 0) : IsUnit (Work.MotV5.ASChart.linAS2L a b) := by
  rw [Work.MotV5.ASChart.linAS2L_eq_const]
  have hfac : (C a ^ 2 - C a * C b - C b ^ 2 : MvPolynomial (Fin 3) K)
      = C (a ^ 2 - a * b - b ^ 2) := by
    rw [map_sub, map_sub, map_mul, map_pow, map_pow]
  rw [hfac]
  exact (isUnit_two_poly K).neg.mul (isUnit_C hab)

/-- **The chart-isomorphism conjunct of the generic AS census** (the conjunct `hΦ`): the
localisation of `K[X0,X1,X2]` away from the source divisor `FdivAS2 (aK K D) (bK K D) g` is
`K`-isomorphic to the localisation away from the target divisor `GdivAS2 (aK K D) (bK K D) g`.

Fork of `Work.MotV5.ASChart.chartIsoAS2` (WP5, LK-5 of `MOTIVIC_CHAR5_N3_LEAD.md` §6, a wrapper of
the generic `Work.MotV5.ASChart.ASChartIsoL*`, `PhiL_*`, `PsiL_*`, `Stereo`, `ASChartLocalDefs`
layer), whose base field is `RatFunc 𝕜`, whose coordinates are `Work.MotAS.aK D`, `Work.MotAS.bK D`
and whose class is `Work.MotV.fAS 𝕜`.  Here `K` is an arbitrary `𝕜`-algebra field of
characteristic `5`, the class is arbitrary, and the coordinates are `Work.MotC5N3.aK K D`,
`Work.MotC5N3.bK K D` (`Submission/Work/MotC5N3/AK.lean`).

Route (confirmed by both reviewers, who note that this needs neither `g ∉ ℘(K)` nor infinitude of
`K`): the generic layer already exists — `Work.MotV5.ASChart.chartIsoL` is stated for an arbitrary
`[Field K]` with `h5 : (5 : MvPolynomial (Fin 3) K) = 0` and concludes
`Nonempty (Localization.Away (FdivAS2L a b g) ≃ₐ[K] Localization.Away (GdivAS2L a b g))`, and
`FdivAS2L a b g = Work.MotAS.FdivAS2 a b g`, `GdivAS2L a b g = Work.MotAS.GdivAS2 a b g` are `rfl`
for every field `K`.  So it suffices to transport along those two `rfl`s and to supply `h5` (from
`[CharP K 5]`) and `hlin : IsUnit (linAS2L (aK K D) (bK K D))`, the latter from
`Work.MotV5.ASChart.linAS2L_eq_const` and `Work.MotC5N3.aK_sq_sub_ne D hD` (the constant
`aK ^ 2 - aK * bK - bK ^ 2 ≠ 0` is a unit in `K[X0,X1,X2]`).  `Submission/Work/MotC5N3/port.py`
performs any textual port still needed.

Deliverable: namespace `Work.MotC5N3`, file `Submission/Work/MotC5N3/chartIsoAS2.lean` (helpers in
sibling files), sorry-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`). -/
theorem chartIsoAS2 (K : Type) [Field K] [CharP K 5] {𝕜 : Type} [Field 𝕜] [Algebra 𝕜 K]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D) (g : K) :
    Nonempty (Localization.Away (Work.MotAS.FdivAS2 (Work.MotC5N3.aK K D)
        (Work.MotC5N3.bK K D) g) ≃ₐ[K]
      Localization.Away (Work.MotAS.GdivAS2 (Work.MotC5N3.aK K D)
        (Work.MotC5N3.bK K D) g)) := by
  have h5 : (5 : MvPolynomial (Fin 3) K) = 0 := charFive_poly K
  have hlin : IsUnit (Work.MotV5.ASChart.linAS2L (Work.MotC5N3.aK K D)
      (Work.MotC5N3.bK K D)) :=
    isUnit_linAS2L _ _ (Work.MotC5N3.aK_sq_sub_ne D hD)
  exact Work.MotV5.ASChart.chartIsoL h5 (Work.MotC5N3.aK K D) (Work.MotC5N3.bK K D) g hlin

end Work.MotC5N3
