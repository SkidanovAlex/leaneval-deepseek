import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Calculus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open scoped Topology

/-- `y ↦ g y · (‖x - y‖ ^ 6)⁻¹` is smooth when `x` is outside the (topological) support of `g`:
on a neighbourhood of `x` the function `g` vanishes, and off `x` both factors are smooth.
Useful auxiliary: from `x ∉ tsupport g` one gets `g =ᶠ[𝓝 x] 0` (via `isClosed_tsupport`,
`Metric.isOpen_iff` and `image_eq_zero_of_notMem_tsupport`). -/
theorem contDiff_symH {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∉ tsupport g) :
    ContDiff ℝ (⊤ : ENat) (fun y => g y * ((‖x - y‖ ^ 6 : ℝ) : ℂ)⁻¹) := by
  -- smoothness is a local (pointwise) property
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = x
  · -- at `x` the factor `g` vanishes on a whole neighbourhood, so the product is eventually `0`
    rw [hy]
    have hg0 : g =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hg0] with z hz
    simp [hz]
  · -- away from `x` both factors are smooth and the second one is invertible
    have hne : ((‖x - y‖ ^ 6 : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact pow_ne_zero 6 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm hy)))
    refine hg.contDiffAt.mul ?_
    have h1 : ContDiffAt ℝ (⊤ : ENat) (fun z : EuclideanSpace ℝ (Fin 3) => ‖x - z‖) y :=
      ((contDiffAt_const (c := x)).sub contDiffAt_id).norm ℝ (sub_ne_zero.mpr (Ne.symm hy))
    have h2 : ContDiffAt ℝ (⊤ : ENat) (fun z : EuclideanSpace ℝ (Fin 3) => ‖x - z‖ ^ 6) y :=
      h1.pow 6
    have h3 : ContDiffAt ℝ (⊤ : ENat)
        (fun z : EuclideanSpace ℝ (Fin 3) => ((‖x - z‖ ^ 6 : ℝ) : ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y h2
    exact h3.inv hne

end Work.BoseBoxFock
