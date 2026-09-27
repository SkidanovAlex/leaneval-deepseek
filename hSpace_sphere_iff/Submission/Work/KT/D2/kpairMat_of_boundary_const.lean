import Mathlib
import Submission.Work.KT.D2.Winding

namespace Work.KT.D2

/-- A continuous matrix-valued function on the disc `D²` whose value on the boundary circle is
constant is the disc family `toCM N M` of a matrix `M` over `Kpair ℝ²`. -/
theorem kpairMat_of_boundary_const (N : ℕ)
    (G : C(Work.KT.Ball (EuclideanSpace ℝ (Fin 2)), Matrix (Fin N) (Fin N) ℂ))
    (h : ∀ x ∈ Work.KT.bdry (EuclideanSpace ℝ (Fin 2)), G x = 1) :
    ∃ M : Matrix (Fin N) (Fin N) (Work.KT.Kpair (EuclideanSpace ℝ (Fin 2))),
      ∀ x, Work.KT.D2.toCM N M x = G x := by
  refine ⟨fun i j => ⟨⟨fun x => G x i j, ?_⟩, ?_⟩, ?_⟩
  · exact (continuous_apply j).comp ((continuous_apply i).comp G.continuous)
  · intro a ha a' ha'
    simp only [ContinuousMap.coe_mk]
    rw [h a ha, h a' ha']
  · intro x
    ext i j
    rfl

end Work.KT.D2
