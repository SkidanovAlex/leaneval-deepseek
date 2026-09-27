import Mathlib

namespace Work.Projection

open scoped Manifold ContDiff
open Topology

/-- The derivative of a smooth map `f` from an `n`-manifold to `ℝ^N` at a point `x` of the source
of a chart at `p` factors through the derivative of the chart, with the remaining factor being
the ordinary Fréchet derivative of the chart representation of `f`. -/
theorem mfderiv_chartAt_decomp {n N : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → EuclideanSpace ℝ (Fin N)) (hf : ContMDiff (𝓡 n) (𝓡 N) ∞ f) (p x : M)
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    mfderiv (𝓡 n) (𝓡 N) f x =
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        f ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y))
        ((chartAt (EuclideanSpace ℝ (Fin n)) p) x)) ∘L
      mfderiv (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) x := by
  -- the chart, and the chart representation of `f`
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p) x :=
    mdifferentiableAt_atlas (chart_mem_atlas _ _) hx
  have hcs : MDifferentiableAt (𝓡 n) (𝓡 n) (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) x) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas _ _)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).map_source hx)
  have hfmd : MDifferentiableAt (𝓡 n) (𝓡 N) f x := (hf x).mdifferentiableAt (by simp)
  have hg : MDifferentiableAt (𝓡 n) (𝓡 N)
      (fun y : EuclideanSpace ℝ (Fin n) => f ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y))
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) x) :=
    MDifferentiableAt.comp_of_eq ((chartAt (EuclideanSpace ℝ (Fin n)) p) x) hfmd hcs
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv hx)
  -- chain rule
  have hcomp := mfderiv_comp x hg hc
  -- `f` agrees with the chart representation composed with the chart, near `x`
  have heq : mfderiv (𝓡 n) (𝓡 N)
      ((fun y : EuclideanSpace ℝ (Fin n) => f ((chartAt (EuclideanSpace ℝ (Fin n)) p).symm y)) ∘
        (chartAt (EuclideanSpace ℝ (Fin n)) p)) x = mfderiv (𝓡 n) (𝓡 N) f x := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards [(chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds hx] with y hy
    simp only [Function.comp_apply]
    rw [OpenPartialHomeomorph.left_inv _ hy]
  -- on the model space the manifold derivative is the Fréchet derivative
  rw [← heq, hcomp, mfderiv_eq_fderiv]
  rfl

end Work.Projection
