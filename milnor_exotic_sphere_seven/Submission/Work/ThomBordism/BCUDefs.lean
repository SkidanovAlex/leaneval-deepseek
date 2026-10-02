import Mathlib
import Submission.Work.ThomBordism.BCUProfile
import Submission.Work.ThomBordism.bcu_profile_properties
import Submission.Work.ThomBordism.bcu_profile2_properties
import Submission.Work.ThomBordism.exists_eNormChart
import Submission.Work.Surgery.Boundary

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The boundary collapse `Φ` of `boundarySign_boundaryChartAt_univ`: definitions

For a `(n+1)`-manifold with boundary `W`, a boundary point `y`, a scale `τ` and a bump `χ`, the
collapse map of the last mile is

  `Φ z := profile2 0 (χ z) (τ • ((chartAt y z) - (chartAt y y)))`.

The chart value `chartAt y z - chartAt y y` is defined for interior *and* boundary points (the chart
at `y` contains `y` in its source), which is what makes the single formula work on all of `W`: on
the boundary it reduces to the flat-face coordinates `tail (chartAt y z) - tail (chartAt y y)`.

This file contains the definitions and the elementary value lemmas; the continuity, membership and
fibre properties are proved in `boundarySign_boundaryChartAt_univ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

open scoped Manifold Topology

namespace Work.ThomBordism

noncomputable section

/-- The chart at `y`, read in the ambient model space `ℝ^{n+1}`. -/
abbrev bcuCh (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W] (y : W) :
    W → EuclideanSpace ℝ (Fin (n + 1)) :=
  fun z => ((chartAt (EuclideanHalfSpace (n + 1)) y) z).1

/-- The chart value of the collapse, normalised at `y` and scaled by `τ`. -/
def bcuVa (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (τ : ℝ) (z : W) : EuclideanSpace ℝ (Fin (n + 1)) :=
  τ • (bcuCh n W y z - bcuCh n W y y)

/-- **The boundary collapse** attached to the chart at `y`, the scale `τ` and the bump `χ`. -/
def bcuPhi (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (τ : ℝ) (χ : W → ℝ) (z : W) : EuclideanSpace ℝ (Fin (n + 1)) :=
  BCU.profile2 (0 : EuclideanSpace ℝ (Fin (n + 1))) (χ z) (bcuVa n W y τ z)

@[simp] theorem bcuVa_apply (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (τ : ℝ) (z : W) :
    bcuVa n W y τ z = τ • (bcuCh n W y z - bcuCh n W y y) := rfl

@[simp] theorem bcuPhi_apply (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (τ : ℝ) (χ : W → ℝ) (z : W) :
    bcuPhi n W y τ χ z = BCU.profile2 0 (χ z) (bcuVa n W y τ z) := rfl

/-- The collapse at `y` itself is the origin. -/
theorem bcuVa_self (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (τ : ℝ) : bcuVa n W y τ y = 0 := by
  simp [bcuVa]

/-- The collapse vanishes at `y` at time `1`. -/
theorem bcu_profile2_one_zero (m : ℕ) :
    BCU.profile2 (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 0 = 0 := by
  rw [BCU.profile2]
  norm_num
  rw [BCU.shiftPhase2]
  norm_num
  simp [BCU.clampBall]

theorem bcuPhi_self (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (τ : ℝ) (χ : W → ℝ) (h1 : χ y = 1) : bcuPhi n W y τ χ y = 0 := by
  rw [bcuPhi_apply, h1, bcuVa_self, bcu_profile2_one_zero]

/-- At a point where the bump vanishes the collapse is the north pole. -/
theorem bcuPhi_eq_northPole (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (τ : ℝ) (χ : W → ℝ) (z : W) (h : χ z = 0) :
    bcuPhi n W y τ χ z = BCU.northPole n := by
  rw [bcuPhi_apply, h]
  simp [BCU.profile2]

/-! ## The chart whose value is the collapse's normalised coordinate -/

/-- The rescaled and translated chart at `y`: its value at `z` is `τ • (chart y z - chart y y)`.
Built from the (explicit) rescaled interior chart `normChart` and a translation of the model. -/
def bcuChart (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (y : W) (τ : ℝ) (hτ : τ ≠ 0) :
    OpenPartialHomeomorph W (EuclideanSpace ℝ (Fin (n + 1))) :=
  (normChart n W y τ hτ).transHomeomorph
    (Homeomorph.addRight (-(τ • ((chartAt (EuclideanHalfSpace (n + 1)) y) y).1)))

theorem bcuChart_source (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (y : W) (τ : ℝ) (hτ : τ ≠ 0) :
    (bcuChart n W y τ hτ).source = (Work.PTGeometric.icChart n W y).source := by
  rw [bcuChart, OpenPartialHomeomorph.transHomeomorph_source, normChart_source]

/-- The value of `bcuChart` at a point of its source is the normalised chart value `bcuVa`. -/
theorem bcuChart_apply (n : ℕ) (W : TopCat) [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    (y : W) (τ : ℝ) (hτ : τ ≠ 0) {z : W}
    (hz : z ∈ (bcuChart n W y τ hτ).source) :
    bcuChart n W y τ hτ z = bcuVa n W y τ z := by
  have hzs : z ∈ (Work.PTGeometric.icChart n W y).source := by
    rwa [bcuChart_source] at hz
  rw [bcuChart, OpenPartialHomeomorph.transHomeomorph_apply, Function.comp_apply,
    Homeomorph.coe_addRight, normChart_apply]
  rw [Work.PTGeometric.icChart_coe, extChartAt_coe, Function.comp_apply]
  rw [modelWithCornersEuclideanHalfSpace_toFun (n + 1)]
  simp only [Function.comp_apply, bcuVa, bcuCh]
  rw [smul_sub]
  abel

end

end Work.ThomBordism
