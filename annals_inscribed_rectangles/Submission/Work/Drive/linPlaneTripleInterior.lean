import Mathlib
import Submission.Work.Drive.chartGenericity
import Submission.Work.Drive.linCommonPoint
import Submission.Work.Drive.collapseFaceAvoid
import Submission.Work.Drive.squareDisk

/-!
# The all-linear row `LLL` of the ends-clause table: interiority and injectivity

`Work.Drive.EndTripleReg` (the third `Meet3Hyp` clause of `hasClassLinearization_of_endData`) asks, at
every common-value triple of the three class maps, for the **injectivity** of the three class
derivatives and for the triviality of the triple intersection of their ranges.  For the three **linear**
plane charts `y ↦ planeClassMap (diskPlane (linPlaneChart (Φ k) c hc)) y` this file supplies the
injectivity half, together with the interiority input it needs:

* `Work.Drive.normFoldBox_eq_one_iff_not_openSquare` — the fold criterion, in the exact form needed
  (a local copy of the proved `Work.Drive.norm_sqDisk_foldBox_eq_one_iff` of `Drive/pairOneDataT6.lean`,
  reproduced here under a fresh name because that file belongs to the transport's import cone);
* **`Work.Drive.openSquare_of_class_eq_linCommonPt`** — if the class of a *linear plane chart* of the
  triple at a box point equals the class of the common point `linCommonPt Φ c hc hrank`, then the point
  is **strictly interior**: the disk parameter is not on the boundary circle (else `hgen` would be
  violated), and the boundary of the box is exactly the boundary circle of the disk.  This is the
  `openSquare` hypothesis that `injective_mfderiv_cls_diskPlane_linPlaneChart` needs;
* **`Work.Drive.injective_mfderiv_of_class_eq_linCommonPt`** — consequently the class derivative of each
  of the three linear charts is *injective* at the parameters of a common-value triple.

The remaining conjunct (the triviality of the triple intersection of the ranges) is the statement
`Work.Drive.linPlaneTripleRange` (`Drive/linPlaneTripleRange`); both reviewers of its statement
confirmed that it follows from `hrank` alone together with the containment
`range (mfderiv (planeClassMap (diskPlane (linPlaneChart φ c hc)))) y ⊆ T_{[v]} P(linSub φ)`
(`Work.Drive.quotient_generalPosition` is the linear-algebra step).  With this file, the row
`hendLLL` of `hasClassLinearization_of_endData` is the assembly of the two.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjChartLPI :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

noncomputable section

/-! ## 1. The fold criterion -/

/-- **The box point is strictly interior exactly when its disk point is strictly inside the disk.**
(`‖sqDisk (foldBox u)‖ = 1 ↔ ¬ openSquare u` for `u` in the unit square.) -/
lemma normFoldBox_eq_one_iff_not_openSquare {u : EuclideanSpace ℝ (Fin 2)}
    (hu : u ∈ Submission.Drive.unitBox 1) :
    ‖sqDisk (foldBox u)‖ = 1 ↔ ¬ openSquare u := by
  rw [norm_sqDisk_eq_one_iff (foldBox u) (foldBox_mem_unitBox u)]
  constructor
  · intro h ho
    rcases h with h | h | h | h
    · exact foldFun_ne_zero_of_mem_Ioo ho.1 h
    · exact foldFun_ne_one_of_mem_Ioo ho.1 h
    · exact foldFun_ne_zero_of_mem_Ioo ho.2 h
    · exact foldFun_ne_one_of_mem_Ioo ho.2 h
  · intro h
    have hpoint : ∀ i : Fin 2, ¬ (u i ∈ Set.Ioo 0 1) → u i = 0 ∨ u i = 1 := by
      intro i hi
      have hIcc : u i ∈ Set.Icc (0 : ℝ) 1 := hu i
      rw [Set.mem_Icc] at hIcc
      rcases lt_or_ge (u i) 1 with hlt | hge
      · left
        by_contra hne
        exact hi ⟨lt_of_le_of_ne hIcc.1 (Ne.symm hne), hlt⟩
      · right
        exact le_antisymm hIcc.2 hge
    by_cases h0 : u 0 ∈ Set.Ioo 0 1
    · have h1 : ¬ (u 1 ∈ Set.Ioo 0 1) := fun h1 => h ⟨h0, h1⟩
      rcases hpoint 1 h1 with h' | h'
      · exact Or.inr (Or.inr (Or.inl (by rw [foldBox_apply_one, h', foldFun_zero])))
      · exact Or.inr (Or.inr (Or.inr (by rw [foldBox_apply_one, h', foldFun_one])))
    · rcases hpoint 0 h0 with h' | h'
      · exact Or.inl (by rw [foldBox_apply_zero, h', foldFun_zero])
      · exact Or.inr (Or.inl (by rw [foldBox_apply_zero, h', foldFun_one]))

/-! ## 2. The interiority of a common-value parameter -/

open Manifold in
open scoped Manifold ContDiff in
/-- **The interiority.**  If a box point of the `k`-th linear plane chart has the class of the common
point `linCommonPt Φ c hc hrank`, then it lies in the open square. -/
theorem openSquare_of_class_eq_linCommonPt
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (Φ k)) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart (Φ k) c hc z ≠ linCommonPt Φ c hc hrank)
    (k : Fin 3) {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Submission.Drive.unitBox 1)
    (hcls : planeClassMap (diskPlane (linPlaneChart (Φ k) c hc)) y
      = (cappingSpaceHomeoProj (linCommonPt Φ c hc hrank)).2) :
    openSquare y := by
  -- the chart point at the disk parameter has the same transparent coordinates as `linCommonPt`
  have hpt : linPlaneChart (Φ k) c hc (sqDisk (foldBox y)) = linCommonPt Φ c hc hrank := by
    refine eq_linCommonPt Φ c hc hrank ?_ fun j => ?_
    · exact level_linPlaneChart (Φ k) c hc _
    · have h1 : (cappingSpaceHomeoProj (linPlaneChart (Φ k) c hc (sqDisk (foldBox y)))).2
          = (cappingSpaceHomeoProj (linCommonPt Φ c hc hrank)).2 := by
        rw [← hcls]
        rfl
      rw [h1]
      exact mem_projLine_linCommonPt Φ c hc hrank j
  -- the disk parameter is not on the boundary circle (else `hgen` fails)
  have hne : ‖sqDisk (foldBox y)‖ ≠ 1 := fun h1 => hgen k _ h1 hpt
  by_contra hcon
  exact hne ((normFoldBox_eq_one_iff_not_openSquare hy).mpr hcon)

open Manifold in
open scoped Manifold ContDiff in
/-- **The injectivity of the class derivative at the parameters of a common-value triple.** -/
theorem injective_mfderiv_of_class_eq_linCommonPt
    (Φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (hrank : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (Φ k)) = 1)
    (hgen : ∀ (k : Fin 3) (z : ℂ), ‖z‖ = 1 →
      linPlaneChart (Φ k) c hc z ≠ linCommonPt Φ c hc hrank)
    (k : Fin 3) {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Submission.Drive.unitBox 1)
    (hcls : planeClassMap (diskPlane (linPlaneChart (Φ k) c hc)) y
      = (cappingSpaceHomeoProj (linCommonPt Φ c hc hrank)).2) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 3)
      (planeClassMap (diskPlane (linPlaneChart (Φ k) c hc))) y) := by
  have hopen := openSquare_of_class_eq_linCommonPt Φ c hc hrank hgen k hy hcls
  have h := injective_mfderiv_cls_diskPlane_linPlaneChart (Φ k) c hc y hopen
  rwa [show mk2 (y 0) (y 1) = y from mk2_eta y] at h

end

end Work.Drive
