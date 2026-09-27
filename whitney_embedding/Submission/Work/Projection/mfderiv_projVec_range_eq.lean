import Mathlib
import Submission.Work.Projection.TransverseDefs
import Submission.Work.Projection.mfderiv_chartAt_decomp
import Submission.Work.Projection.range_sup_eq_top_of_det_ne_zero_smooth

/-!
# The range of `mfderiv` of a projected chart representation

The range form of the chart decomposition of `mfderiv` (`Work.Projection.mfderiv_chartAt_decomp`):
the chart at `p` has surjective manifold derivative, so composing with it does not change the
range, and the range of the manifold derivative of `z ↦ projVec u (e z)` at a point `x` of that
chart is the range of `projVec u ∘ fderiv (chartRep e p) (chartAt p x)`.
-/

open scoped Manifold ContDiff
open Topology

namespace Work.Projection

/-- **The range of the manifold derivative of a projected map, in chart coordinates.** -/
theorem mfderiv_projVec_range_eq {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (e : M → EuclideanSpace ℝ (Fin (2 * n + 1)))
    (he : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) e)
    (p : M) (x : M) (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (u : EuclideanSpace ℝ (Fin (2 * n))) :
    (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
        (fun z => projVec u (e z)) x).range =
      (projVec u ∘L fderiv ℝ (chartRep e p) ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)).range := by
  haveI : IsManifold (𝓡 n) 1 M := IsManifold.of_le (m := 1) (n := ∞) (by simp)
  have he' : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e := he
  have hg : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ (fun z => projVec u (e z)) :=
    (projVec u).contMDiff.comp he'
  have ha : (chartAt (EuclideanSpace ℝ (Fin n)) p) x ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) p).target := (chartAt _ p).map_source hx
  let Mx : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) x
  have hMx : Mx.range = ⊤ := (mdifferentiable_chart (I := 𝓡 n) p).range_mfderiv_eq_top hx
  rw [mfderiv_chartAt_decomp (N := 2 * n) (fun z => projVec u (e z)) hg p x hx]
  have h1 : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        projVec u (e ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)))
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)
      = (projVec u) ∘L fderiv ℝ (chartRep e p)
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) x) := by
    have hcomp' : (fun y : EuclideanSpace ℝ (Fin n) =>
          projVec u (e ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)))
        = ⇑(projVec u) ∘ chartRep e p := rfl
    rw [hcomp', fderiv_comp ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)
      (projVec u).differentiableAt (differentiableAt_chartRep e he' p ha)]
    rw [ContinuousLinearMap.fderiv (projVec u)]
  rw [h1]
  change (((projVec u) ∘L fderiv ℝ (chartRep e p)
    ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)) ∘L Mx).range
      = (projVec u ∘L fderiv ℝ (chartRep e p)
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)).range
  rw [clm_range_comp_smooth, hMx, Submodule.map_top]

end Work.Projection
