import Mathlib
import Submission.Work.Tubular.exists_euclidean_normalBundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Continuity of the Gram–Schmidt orthonormalisation

The Gram–Schmidt orthonormalisation `InnerProductSpace.gramSchmidtNormed` of a family of vectors
that is everywhere linearly independent depends continuously on the parameter.

Mathlib has the algebraic API for `gramSchmidt` / `gramSchmidtNormed` but not its continuity; the
`ContinuousOn` form is proved in `Submission/Work/Tubular/exists_euclidean_normalBundle.lean`
(`Work.Tubular.continuousOn_gramSchmidtNormed`), and the present file records the global
(`Continuous`) specialisation needed by the Grassmannian chart machinery.
-/

namespace Work.ThomBordism.Grassmann.Smooth

/-- **Gram–Schmidt depends continuously on the parameter.**  If `f : X → ι → E` is a family of
vectors that is pointwise linearly independent and depends continuously on `x`, then for each `i`
the orthonormalised vector `gramSchmidtNormed ℝ (f x) i` depends continuously on `x`. -/
theorem gramSchmidtContinuous {X ι E : Type*} [TopologicalSpace X] [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [WellFoundedLT ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : X → ι → E) (hf : ∀ i, Continuous fun x => f x i)
    (hli : ∀ x, LinearIndependent ℝ (f x)) (i : ι) :
    Continuous fun x => InnerProductSpace.gramSchmidtNormed ℝ (f x) i := by
  rw [← continuousOn_univ]
  exact Work.Tubular.continuousOn_gramSchmidtNormed (𝕜 := ℝ)
    (fun j => (hf j).continuousOn) (fun x _ => hli x) i

end Work.ThomBordism.Grassmann.Smooth
