import Mathlib
import Submission.Work.Diff.Dim2.Ambient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set Filter

/-!
# Smoothness of the ambient sphere parametrisation

`sphereAmb (r, z) = (sin r • z, cos r)` is the composite of the chart components
`(r, z) ↦ (sin r * z 0, sin r * z 1, cos r) : ℝ × ℝ² → (Fin 3 → ℝ)` with the (continuous,
linear) identification `(Fin 3 → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 3)`.  Each component is
elementary smooth, so `sphereAmb` is `C^∞`.
-/

/-- Value of the `0`-th component of `sphereAmbComp`. -/
private lemma sphereAmbSmooth_comp_zero (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    sphereAmbComp (0 : Fin 3) p = Real.sin p.1 * p.2.ofLp 0 := by
  rw [sphereAmbComp, Fin.cases_zero]

/-- Value of the `1`-st component of `sphereAmbComp`. -/
private lemma sphereAmbSmooth_comp_one (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    sphereAmbComp (1 : Fin 3) p = Real.sin p.1 * p.2.ofLp 1 := by
  rw [show (1 : Fin 3) = Fin.succ (0 : Fin 2) from rfl, sphereAmbComp, Fin.cases_succ,
    Fin.cases_zero]

/-- Value of the `2`-nd component of `sphereAmbComp`. -/
private lemma sphereAmbSmooth_comp_two (p : ℝ × EuclideanSpace ℝ (Fin 2)) :
    sphereAmbComp (2 : Fin 3) p = Real.cos p.1 := by
  rw [show (2 : Fin 3) = Fin.succ (1 : Fin 2) from rfl, sphereAmbComp, Fin.cases_succ,
    show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl, Fin.cases_succ]

/-- Each component of the ambient parametrisation is smooth. -/
private lemma contDiff_sphereAmbComp (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp i p) := by
  fin_cases i
  · show ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (0 : Fin 3) p)
    rw [show (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (0 : Fin 3) p)
        = (fun p => Real.sin p.1 * p.2.ofLp 0) from funext fun p => sphereAmbSmooth_comp_zero p]
    fun_prop
  · show ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (1 : Fin 3) p)
    rw [show (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (1 : Fin 3) p)
        = (fun p => Real.sin p.1 * p.2.ofLp 1) from funext fun p => sphereAmbSmooth_comp_one p]
    fun_prop
  · show ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (2 : Fin 3) p)
    rw [show (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => sphereAmbComp (2 : Fin 3) p)
        = (fun p => Real.cos p.1) from funext fun p => sphereAmbSmooth_comp_two p]
    fun_prop

theorem sphereAmbSmooth : ContDiff ℝ (⊤ : ℕ∞) Work.Diff.Dim2.sphereAmb := by
  have hfun : sphereAmb = (fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
      (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => sphereAmbComp i p)) := rfl
  rw [hfun]
  have hpi : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => fun i : Fin 3 => sphereAmbComp i p) := by
    rw [contDiff_pi]
    exact fun i => contDiff_sphereAmbComp i
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp hpi

end Work.Diff.Dim2
