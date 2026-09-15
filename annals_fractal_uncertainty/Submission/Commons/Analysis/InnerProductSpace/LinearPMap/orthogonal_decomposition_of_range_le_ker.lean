import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.LinearPMap.exists_orthogonal_decomposition
import Submission.Commons.Analysis.InnerProductSpace.LinearPMap.orthogonal_range_eq_ker_adjoint

namespace Commons.Analysis.InnerProductSpace.LinearPMap

open scoped _root_.InnerProductSpace

/-- **The abstract `hdec` decomposition.** Let `S : F →ₗ.[K] G` be a closed, densely defined
operator and `T : H →ₗ.[K] F` a densely defined operator whose range is contained in the kernel of
`S`. Then every `x : F` splits as `x = x' + (x - x')` with `x' ∈ ker S` and `x - x'` orthogonal to
`ker S`; in particular `x - x'` is orthogonal to the range of `T`, hence lies in `Dom T†` with
`T† (x - x') = 0`. -/
theorem orthogonal_decomposition_of_range_le_ker {K F G H : Type*} [RCLike K]
    [NormedAddCommGroup F] [InnerProductSpace K F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace K G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace K H] [CompleteSpace H]
    (S : LinearPMap (RingHom.id K) F G) (T : LinearPMap (RingHom.id K) H F)
    (hS : Dense (S.domain : Set F)) (hvnS : LinearPMap.adjoint (LinearPMap.adjoint S) = S)
    (hT : Dense (T.domain : Set H))
    (hran : ∀ y : T.domain, ∃ hy : (T y) ∈ S.domain, S ⟨T y, hy⟩ = 0) :
    ∀ x : F, ∃ (x' : F) (h1 : x' ∈ S.domain), S ⟨x', h1⟩ = 0 ∧
      (∀ (y : F) (hy : y ∈ S.domain), S ⟨y, hy⟩ = 0 → inner K y (x - x') = 0) ∧
      (∃ (h5 : x - x' ∈ (LinearPMap.adjoint T).domain),
        LinearPMap.adjoint T ⟨x - x', h5⟩ = 0) := by
  intro x
  obtain ⟨x', h1, hx'0, hperp⟩ :=
    exists_orthogonal_decomposition S hS hvnS x
  refine ⟨x', h1, hx'0, hperp, ?_⟩
  refine (orthogonal_range_eq_ker_adjoint T hT (x - x')).1 ?_
  intro y
  obtain ⟨hy, hSy⟩ := hran y
  rw [inner_eq_zero_symm]
  exact hperp (T y) hy hSy

end Commons.Analysis.InnerProductSpace.LinearPMap
