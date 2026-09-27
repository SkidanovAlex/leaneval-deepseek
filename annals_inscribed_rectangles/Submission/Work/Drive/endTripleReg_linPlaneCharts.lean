import Mathlib
import Submission.Work.Drive.linPlaneTripleInterior
import Submission.Work.Drive.unrestrictedFromBox
import Submission.Work.Drive.encodedEndData
import Submission.Work.Drive.linCommonPoint

/-!
# The all-linear row `LLL`: `EndTripleReg` of the three linear plane charts

`Work.Drive.EndTripleReg F A B` (`Drive/encodedEndData.lean`) asks, at every common-value triple
`F y₀ = A y₁ = B y₂` of the three class maps, for

* the **injectivity** of the three class derivatives `mfderiv (𝓡 2) (𝓡 3) F y₀`, `… A y₁`, `… B y₂`, and
* the **triviality** of the triple intersection of their ranges.

This file proves it for the three *linear* plane charts
`B k = planeClassMap (diskPlane (linPlaneChart (Φ k) c hc))` — the row `LLL` of the ends-clause table,
i.e. the `hendLLL` hypothesis of `Work.Drive.hasClassLinearization_of_endData` — with the range clause
as an **input** (`hV`, the ends lane's general-position hypothesis, whose content for these charts is the
range computation of `Drive/linPlaneTripleRange.lean`) and the injectivity clauses **derived from
`hgen` alone**.

## The two halves

* **The common value is pinned** (`Work.Drive.class_linPlaneCharts_eq_linCommonPt`).  Each class map
  `B k` lands on the projective plane `projLine (linSub (Φ k))`, so a common value lies on all three;
  the associated subspaces have a one-dimensional triple intersection (`hrank`), and a one-dimensional
  subspace carries a single point of `ℝP³` (`Work.Drive.eq_of_mem_projLine_of_finrank_eq_one`).  Hence
  every common value *is* the class of `Work.Drive.linCommonPt` — this is where `hrank` is used.
* **The injectivity at a box parameter** is then
  `Work.Drive.injective_mfderiv_of_class_eq_linCommonPt` (`Drive/linPlaneTripleInterior.lean`): the
  only way the class derivative of a *folded* disk presentation can degenerate is a *fold*, i.e. a
  disk parameter on the unit circle, and there `hgen` forbids the value; so the class value being the
  class of `linCommonPt` forces the parameter to be in the open square, where the class map is an
  immersion.  This gives the **box-restricted** statement
  `Work.Drive.boxEndTripleReg_linPlaneCharts`.

## The step from the box to all of `ℝ²`

`Work.Drive.EndTripleReg` is quantified over **all** of `ℝ²` while the box argument above needs its
parameters in the closed unit square.  The passage is
`Work.Drive.endTripleReg_diskPlane_of_box` (`Drive/unrestrictedFromBox.lean`), which uses the affine
symmetries `y ↦ (e i * y i + 2 m i)` of the parameter plane (`e i = ±1`) under which the `foldBox`-based
presentations are invariant (`Work.Drive.diskPlane_affRep`): every parameter is carried into the square
by such a symmetry, and `Work.Drive.transfer_mfderiv_class_of_affRep` shows that the injectivity and the
range of the class derivative are unchanged.

**Formalisation warning (why the proof is written in this order).**  Instantiating the transfer at a
*concrete* presentation is pathologically slow in this workspace — `TangentSpace (𝓡 3) x` is an opaque
`def`, so the instance search for the structures on it runs through it (the phenomenon recorded in
`Submission/Work/Drive/HC_ROTATION_STATUS.md`, §2 and §4, and in the `HVClause` comment of
`Drive/chartGenericity.lean`).  The proof below therefore never applies the transfer itself: it proves
the box-restricted statement at the concrete charts (cheap, since `EndTripleReg`-shaped goals at
concrete presentations *are* fine — only the transfer is not) and hands it to
`endTripleReg_diskPlane_of_box` **once**, with the presentation passed as the explicit vector of the
three charts.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjChartELin :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

noncomputable section

/-! ## 1. The common value of three linear plane charts -/

/-- **The common value of the three linear plane charts is the class of `linCommonPt`.**  If the
classes of the `2`-nd, the `0`-th and the `1`-st linear plane chart agree at a triple of parameters,
then that common class is the class of `Work.Drive.linCommonPt`: it lies on all three projective planes
`projLine (linSub (Φ k))`, whose associated subspaces have a one-dimensional triple intersection
(`hrank`), and a one-dimensional subspace carries a single point of `ℝP³`
(`Work.Drive.eq_of_mem_projLine_of_finrank_eq_one`). -/
theorem class_linPlaneCharts_eq_linCommonPt
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (Φ k)) = 1)
    {y₀ y₁ y₂ : EuclideanSpace ℝ (Fin 2)}
    (h01 : planeClassMap (diskPlane (linPlaneChart (Φ 2) c hc)) y₀
      = planeClassMap (diskPlane (linPlaneChart (Φ 0) c hc)) y₁)
    (h02 : planeClassMap (diskPlane (linPlaneChart (Φ 2) c hc)) y₀
      = planeClassMap (diskPlane (linPlaneChart (Φ 1) c hc)) y₂) :
    planeClassMap (diskPlane (linPlaneChart (Φ 2) c hc)) y₀
      = (cappingSpaceHomeoProj (linCommonPt Φ c hc hrank)).2 := by
  have hmem : ∀ k : Fin 3, planeClassMap (diskPlane (linPlaneChart (Φ 2) c hc)) y₀
      ∈ projLine (linSub (Φ k)) := by
    intro k
    fin_cases k
    · rw [h01]
      exact linPlaneChart_mem_projLine (Φ 0) c hc (sqDisk (foldBox y₁))
    · rw [h02]
      exact linPlaneChart_mem_projLine (Φ 1) c hc (sqDisk (foldBox y₂))
    · exact linPlaneChart_mem_projLine (Φ 2) c hc (sqDisk (foldBox y₀))
  have hU : planeClassMap (diskPlane (linPlaneChart (Φ 2) c hc)) y₀
      ∈ projLine (⨅ k : Fin 3, linSub (Φ k)) :=
    mem_projLine_of_submodule_le (le_iInf fun k => submodule_le_of_mem_projLine (hmem k))
  have hP : (cappingSpaceHomeoProj (linCommonPt Φ c hc hrank)).2
      ∈ projLine (⨅ k : Fin 3, linSub (Φ k)) :=
    mem_projLine_of_submodule_le
      (le_iInf fun k => submodule_le_of_mem_projLine (mem_projLine_linCommonPt Φ c hc hrank k))
  exact eq_of_mem_projLine_of_finrank_eq_one hrank hU hP

/-! ## 2. The box-restricted end-triple data of the three linear plane charts -/

/-- **The end-triple data of the linear plane charts, on the closed unit square.**  At box parameters
the common value is pinned by `Work.Drive.class_linPlaneCharts_eq_linCommonPt`, so the class derivative
of each of the three charts is injective by `Work.Drive.injective_mfderiv_of_class_eq_linCommonPt`
(which is where `hgen` rules out the folds); the range clause is the hypothesis `hV`. -/
theorem boxEndTripleReg_linPlaneCharts
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (Φ k)) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart (Φ k) c hc z ≠ linCommonPt Φ c hc hrank)
    (hV : ∀ (y : Fin 3 → EuclideanSpace ℝ (Fin 2)),
      (∀ k : Fin 3,
        planeClassMap (diskPlane (linPlaneChart (Φ 2) c hc)) (y 2)
          = planeClassMap (diskPlane (linPlaneChart (Φ k) c hc)) (y k)) →
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) :=
        Work.Drive.projCharted 3
      letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) (Work.Drive.Ctop)
        (Projectivization ℝ (Eucl 3)) := Work.Drive.isManifold_projCharted 3
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (planeClassMap (diskPlane (linPlaneChart (Φ 2) c hc)))
        (y 2)).range ⊓
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (planeClassMap (diskPlane (linPlaneChart (Φ 0) c hc)))
        (y 0)).range ⊓
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (planeClassMap (diskPlane (linPlaneChart (Φ 1) c hc)))
        (y 1)).range = ⊥) :
    BoxEndTripleReg (planeClassMap (diskPlane (linPlaneChart (Φ 2) c hc)))
      (planeClassMap (diskPlane (linPlaneChart (Φ 0) c hc)))
      (planeClassMap (diskPlane (linPlaneChart (Φ 1) c hc))) := by
  intro y₀ y₁ y₂ hbox h01 h02
  have hy₀ : y₀ ∈ Submission.Drive.unitBox 1 := by simpa using hbox 0
  have hy₁ : y₁ ∈ Submission.Drive.unitBox 1 := by simpa using hbox 1
  have hy₂ : y₂ ∈ Submission.Drive.unitBox 1 := by simpa using hbox 2
  have hcls₀ : planeClassMap (diskPlane (linPlaneChart (Φ 2) c hc)) y₀
      = (cappingSpaceHomeoProj (linCommonPt Φ c hc hrank)).2 :=
    class_linPlaneCharts_eq_linCommonPt Φ c hc hrank h01 h02
  have hcls₁ : planeClassMap (diskPlane (linPlaneChart (Φ 0) c hc)) y₁
      = (cappingSpaceHomeoProj (linCommonPt Φ c hc hrank)).2 := h01.symm.trans hcls₀
  have hcls₂ : planeClassMap (diskPlane (linPlaneChart (Φ 1) c hc)) y₂
      = (cappingSpaceHomeoProj (linCommonPt Φ c hc hrank)).2 := h02.symm.trans hcls₀
  refine ⟨injective_mfderiv_of_class_eq_linCommonPt Φ c hc hrank hgen 2 hy₀ hcls₀,
    injective_mfderiv_of_class_eq_linCommonPt Φ c hc hrank hgen 0 hy₁ hcls₁,
    injective_mfderiv_of_class_eq_linCommonPt Φ c hc hrank hgen 1 hy₂ hcls₂, ?_⟩
  exact hV ![y₁, y₂, y₀] (by
    intro k
    fin_cases k
    · simpa using h01
    · simpa using h02
    · rfl)

/-! ## 3. The end-triple data of the three linear plane charts -/

theorem endTripleReg_linPlaneCharts
    (Φ : Fin 3 → Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3) (c : ℝ) (hc : 0 < c)
    (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, Work.Drive.linSub (Φ k)) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      Work.Drive.linPlaneChart (Φ k) c hc z ≠ Work.Drive.linCommonPt Φ c hc hrank)
    (hV : ∀ (y : Fin 3 → EuclideanSpace ℝ (Fin 2)),
      (∀ k : Fin 3,
        Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 2) c hc)) (y 2)
          = Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ k) c hc)) (y k)) →
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Work.Drive.Eucl 3)) :=
        Work.Drive.projCharted 3
      letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) (Work.Drive.Ctop)
        (Projectivization ℝ (Work.Drive.Eucl 3)) := Work.Drive.isManifold_projCharted 3
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 2) c hc)))
        (y 2)).range ⊓
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 0) c hc)))
        (y 0)).range ⊓
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 1) c hc)))
        (y 1)).range = ⊥) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Work.Drive.Eucl 3)) :=
      Work.Drive.projCharted 3
    letI : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) (Work.Drive.Ctop)
      (Projectivization ℝ (Work.Drive.Eucl 3)) := Work.Drive.isManifold_projCharted 3
    Work.Drive.EndTripleReg
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 2) c hc)))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 0) c hc)))
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (Φ 1) c hc))) := by
  let Q : Fin 3 → ℂ → CappingSpace :=
    ![linPlaneChart (Φ 2) c hc, linPlaneChart (Φ 0) c hc, linPlaneChart (Φ 1) c hc]
  have hQ : ∀ k, ContMDiff (𝓡 2) (𝓡 4) Ctop (diskPlane (Q k)) := by
    intro k
    fin_cases k <;> exact contMDiff_diskPlane (linPlaneChart_contMDiff _ c hc)
  exact endTripleReg_diskPlane_of_box Q hQ
    (boxEndTripleReg_linPlaneCharts Φ c hc hrank hgen hV)

end

end Work.Drive
