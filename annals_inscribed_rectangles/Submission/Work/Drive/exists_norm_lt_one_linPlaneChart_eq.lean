import Mathlib
import Submission.Work.Drive.linCommonPoint
import Submission.Work.Drive.linVecC_smul_surjective
import Submission.Work.Drive.linPlaneChartNormals

/-!
# The boundary circle of a linear plane chart misses the common point

`Work.Drive.linCommonPt φ c hc h` is the unique point of the capping space on the level `c` whose
projective class lies on all three planes `projLine (linSub (φ k))`
(`Submission/Work/Drive/linCommonPoint.lean`), i.e. the common value of the three plane charts at a
triple parameter.  Each plane chart `linPlaneChart (φ k) c hc` presents its plane by the disk model of
`ℝP²`, and the disk model *covers* its whole projective plane (`Work.Drive.linVecC_smul_surjective`),
so the point `linCommonPt` lies in the image of every one of the three charts.  This file shows that
this point can always be attained in the *open* disk, unless the boundary circle is mapped onto it:
if no `z` with `‖z‖ = 1` is sent to `linCommonPt`, then some `z` with `‖z‖ < 1` is.

Equivalently, the set of boundary parameters `z` with `linPlaneChart (φ k) c hc z = linCommonPt` is
non-empty whenever the interior misses it — the form in which the end-contribution count consumes the
statement (a triple parameter at which the three charts agree and which is not a boundary triple must
be an interior one).

The mathematics is short: the transparent coordinates of `linCommonPt` are `(c, [w])` with
`w ∈ linSub (φ k)`, and `linSub (φ k) = φ k (linStd)` with `linStd = {v : v 3 = 0}`; writing
`v = a • linVecC z` with `a ≠ 0` and `‖z‖ ≤ 1` (`Work.Drive.linVecC_smul_surjective`), the class
`[φ k (linVecC z)] = [w]` is the class of the chart at `z`, and the levels agree because both are
`c`.  A boundary parameter is excluded by hypothesis, leaving `‖z‖ < 1`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

open Manifold in
open scoped Manifold ContDiff in
/-- **The common point of the three linear planes is attained in the open disk of every one of the
three charts, unless the boundary circle is mapped onto it.** -/
theorem exists_norm_lt_one_linPlaneChart_eq (φ : Fin 3 → Work.Drive.Eucl 3 ≃L[ℝ] Work.Drive.Eucl 3)
    (c : ℝ) (hc : 0 < c) (h : Module.finrank ℝ ↥(⨅ k : Fin 3, Work.Drive.linSub (φ k)) = 1)
    (k : Fin 3) (hgen : ∀ z : ℂ, ‖z‖ = 1 →
      Work.Drive.linPlaneChart (φ k) c hc z ≠ Work.Drive.linCommonPt φ c hc h) :
    ∃ z : ℂ, ‖z‖ < 1 ∧ Work.Drive.linPlaneChart (φ k) c hc z = Work.Drive.linCommonPt φ c hc h := by
  -- the transparent coordinates of `linCommonPt` are `(c, [w])` with `w` in the plane of the chart
  obtain ⟨w, hw0, hwU, hwP⟩ := mem_projLine_linCommonPt φ c hc h k
  obtain ⟨v, hvstd, hvw⟩ := hwU
  have hv0 : v ≠ 0 := fun hv => hw0 (by rw [← hvw, hv, map_zero])
  -- `v` lies in the standard plane `linStd`, which is the hyperplane `{v : v 3 = 0}`
  have hv3 : v 3 = 0 := by
    rw [linStd_eq_kerProj] at hvstd
    exact hvstd
  -- hence `v = (w₁, t)` in the complex coordinates, with not both coordinates zero
  have hwne : c₁ v ≠ 0 ∨ v 2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hzero : ofComplex (c₁ v) ((v 2 : ℝ) : ℂ) = 0 := by
      rw [hcon.1, hcon.2]
      simp [ofComplex]
    rw [ofComplex_c₁_c₂_of_apply_three_eq_zero hv3] at hzero
    exact hv0 hzero
  -- so `v = a • linVecC z` for a non-zero real `a` and a point `z` of the closed unit disk
  obtain ⟨z, a, ha0, hz1, haz⟩ := linVecC_smul_surjective (w₁ := c₁ v) (t := v 2) hwne
  have hazv : a • linVecC z = v := by
    rw [haz, ofComplex_c₁_c₂_of_apply_three_eq_zero hv3]
  -- the class of the chart at `z` is that of `w`, and the levels agree
  have hchart : linPlaneChart (φ k) c hc z = linCommonPt φ c hc h := by
    apply cappingSpaceHomeoProj.injective
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      rw [level_linPlaneChart (φ k) c hc z, level_linCommonPt φ c hc h]
    · rw [cappingSpaceHomeoProj_linPlaneChart, hwP]
      refine ((Projectivization.mk_eq_mk_iff ℝ w (φ k (linVecC z)) hw0
        (phi_linVecC_ne_zero (φ k) z)).mpr ⟨Units.mk0 a ha0, ?_⟩).symm
      rw [Units.smul_def, Units.val_mk0, ← (φ k).map_smul, hazv]
      simpa using hvw
  -- and `z` cannot be a boundary point by hypothesis
  have hne : ‖z‖ ≠ 1 := fun hz => hgen z hz hchart
  exact ⟨z, lt_of_le_of_ne hz1 hne, hchart⟩

end

end Work.Drive
