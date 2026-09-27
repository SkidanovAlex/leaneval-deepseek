import Mathlib
import Submission.Work.Projection.Defs

/-!
# The sharp (projective) parametrisation of the immersion-bad directions

The immersion-bad set of a chart is the image of the smooth map
`(y, w) ↦ extract ((fderiv ℝ (chartRep f p) y) w)` (`immParam`), whose domain is `2n`-dimensional.
The map `extract` is invariant under non-zero scaling of its argument, so `immParam (y, w)` depends
only on the *direction* of `w`.  Directions in `ℝ^n` are parametrised by the `n` affine charts
`{w | w j = 1}`, each of dimension `n - 1`; the `(n-1)`-dimensional parameter for the chart at
`j : Fin (n+1)` is `dirVec j`, which inserts `1` into the `j`-th coordinate.

Here `n` is written as `m + 1`, so that the `(n-1)`-dimensional parameter space is `Fin m → ℝ`.
-/

open scoped Manifold ContDiff
open Topology MeasureTheory

namespace Work.Projection

variable {m k : ℕ}

/-- The vector `ℝ^{m+1}` with `1` in coordinate `j` and the coordinates given by `t` elsewhere. -/
noncomputable def dirVec (j : Fin (m + 1)) (t : Fin m → ℝ) : EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.insertNth j (1 : ℝ) t)

@[simp] lemma dirVec_apply_same (j : Fin (m + 1)) (t : Fin m → ℝ) : (dirVec j t) j = 1 := by
  simp [dirVec]

@[simp] lemma dirVec_apply_succAbove (j : Fin (m + 1)) (t : Fin m → ℝ) (i : Fin m) :
    (dirVec j t) (j.succAbove i) = t i := by
  simp [dirVec]

/-- Every vector whose `j`-th coordinate is `1` is `dirVec j t` for some `t`. -/
lemma dirVec_eq_of_apply (j : Fin (m + 1)) (v : EuclideanSpace ℝ (Fin (m + 1))) (hv : v j = 1) :
    dirVec j (fun i : Fin m => v (j.succAbove i)) = v := by
  ext i
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨q, rfl⟩
  · simpa using hv.symm
  · simp

/-- `dirVec j` is smooth. -/
lemma contDiff_dirVec (j : Fin (m + 1)) : ContDiff ℝ 1 (dirVec (m := m) j) := by
  have hF : ContDiff ℝ 1 (fun t : Fin m → ℝ => (Fin.insertNth j (1 : ℝ) t : Fin (m + 1) → ℝ)) := by
    rw [contDiff_pi]
    intro i
    rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨q, hq⟩
    · simp only [Fin.insertNth_apply_same]
      exact contDiff_const
    · subst hq
      simp only [Fin.insertNth_apply_succAbove]
      exact contDiff_apply ℝ ℝ q
  exact ((ContinuousLinearEquiv.contDiff ((EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm)).comp hF)

/-- `extract` is invariant under non-zero scaling. -/
@[simp] lemma extract_smul (c : ℝ) (hc : c ≠ 0) (z : EuclideanSpace ℝ (Fin (k + 1))) :
    extract (c • z) = extract z := by
  ext i
  simp only [extract_apply]
  exact mul_div_mul_left _ _ hc

/-- The open set on which the sharp parametrisation of the chart at `p` in the direction chart
`j` is smooth: the point lies in the chart's target and the derivative does not land in the
hyperplane `z (Fin.last k) = 0` (the locus where `extract` is defined). -/
noncomputable def sharpDom {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k + 1))) (p : M) (j : Fin (m + 1)) :
    Set (EuclideanSpace ℝ (Fin (m + 1)) × (Fin m → ℝ)) :=
  {yt | yt.1 ∈ (chartAt (EuclideanSpace ℝ (Fin (m + 1))) p).target ∧
        ((fderiv ℝ (chartRep (n := m + 1) f p) yt.1) (dirVec j yt.2)) (Fin.last k) ≠ 0}

/-- The sharp parametrisation of the immersion-bad directions of the chart at `p`, using the
direction chart `j`: `(y, t) ↦ extract (D_y (dirVec j t))`. -/
noncomputable def sharpParam {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin (k + 1))) (p : M) (j : Fin (m + 1)) :
    EuclideanSpace ℝ (Fin (m + 1)) × (Fin m → ℝ) → EuclideanSpace ℝ (Fin k) :=
  fun yt => extract ((fderiv ℝ (chartRep (n := m + 1) f p) yt.1) (dirVec j yt.2))

end Work.Projection
