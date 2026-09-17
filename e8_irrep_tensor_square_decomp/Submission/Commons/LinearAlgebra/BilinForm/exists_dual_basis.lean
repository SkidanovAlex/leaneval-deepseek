import Mathlib.LinearAlgebra.BilinearForm.Properties

namespace Commons.LinearAlgebra.BilinForm

/-- Given a basis `b` of a finite-dimensional vector space `V` over a field `K` and a
non-degenerate bilinear form `B` on `V`, there is a family `b'` with `B (b i) (b' j) = δᵢⱼ`. -/
theorem exists_dual_basis {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (b : Module.Basis ι K V) :
    ∃ b' : ι → V, ∀ i j, B (b i) (b' j) = if i = j then (1 : K) else 0 := by
  -- The `B.dualBasis` of Mathlib is *left*-dual: `B (B.dualBasis hB b i) (b j) = δᵢⱼ`.
  -- Applying it to the flipped form `B.flip` produces a family that is *right*-dual for `B`.
  refine ⟨fun j => B.flip.dualBasis hB.flip b j, fun i j => ?_⟩
  rw [← B.flip_apply]
  exact B.flip.apply_dualBasis_left hB.flip b j i

end Commons.LinearAlgebra.BilinForm