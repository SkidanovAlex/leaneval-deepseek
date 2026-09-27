import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Dim2.loop_GL_nullhomotopic_of_det_log
import Submission.Work.HSpace.Basic

namespace Work.KT.D2

open scoped unitInterval
open ContinuousMap

noncomputable section

/-- Transport of `Work.KT.Dim2.loop_GL_nullhomotopic_of_det_log` from the unit circle
`Metric.sphere (0 : ℂ) 1` to the model circle `Work.KT.Sph (EuclideanSpace ℝ (Fin 2))`
(= `Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1`), along a linear isometry equivalence
`ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)` (e.g. `x + y * I ↦ ![x, y]`); the induced homeomorphism of
unit spheres (`Submission.sphereCongrLIE` in `Submission/Work/HSpace/Basic.lean` may help) pulls
the homotopy back. -/
theorem loop_GL_sphere2 (N : ℕ)
    (f : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), Matrix (Fin N) (Fin N) ℂ))
    (hf : ∀ x, IsUnit (f x))
    (h : ∃ F : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)), ℂ),
      ∀ x, Complex.exp (F x) = (f x).det) :
    ∃ H : C(Work.KT.Sph (EuclideanSpace ℝ (Fin 2)) × unitInterval, Matrix (Fin N) (Fin N) ℂ),
      (∀ p, IsUnit (H p)) ∧ (∀ x, H (x, 0) = f x) ∧ (∀ x, H (x, 1) = 1) := by
  -- The linear isometry `ℂ ≅ ℝ²` restricts to a homeomorphism of unit circles.
  let φ : Metric.sphere (0 : ℂ) 1 ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    Submission.sphereCongrLIE Complex.orthonormalBasisOneI.repr
  -- Pull `f` back to a loop on the complex unit circle.
  let f' : C(Metric.sphere (0 : ℂ) 1, Matrix (Fin N) (Fin N) ℂ) := f.comp ⟨φ, φ.continuous⟩
  obtain ⟨F, hF⟩ := h
  obtain ⟨H', hunit', h0', h1'⟩ :=
    Work.KT.Dim2.loop_GL_nullhomotopic_of_det_log N f' (fun z => hf (φ z))
      ⟨F.comp ⟨φ, φ.continuous⟩, fun z => hF (φ z)⟩
  refine ⟨H'.comp (ContinuousMap.prodMap ⟨φ.symm, φ.symm.continuous⟩
    (ContinuousMap.id unitInterval)), ?_, ?_, ?_⟩
  · intro p
    exact hunit' (φ.symm p.1, p.2)
  · intro x
    show H' (φ.symm x, 0) = f x
    rw [h0' (φ.symm x)]
    show f (φ (φ.symm x)) = f x
    rw [φ.apply_symm_apply]
  · intro x
    show H' (φ.symm x, 1) = 1
    rw [h1' (φ.symm x)]

end

end Work.KT.D2
