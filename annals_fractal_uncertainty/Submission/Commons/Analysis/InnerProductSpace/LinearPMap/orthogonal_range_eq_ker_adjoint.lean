import Mathlib.Analysis.InnerProductSpace.LinearPMap

namespace Commons.Analysis.InnerProductSpace.LinearPMap

open scoped _root_.InnerProductSpace

/-- `x` is orthogonal to the range of a densely defined operator `T` iff `x` lies in the kernel of
the adjoint `T†`.  (This is the `range`-side counterpart of `orthogonal_range_adjoint_eq_ker`.) -/
theorem orthogonal_range_eq_ker_adjoint {K E F : Type*} [RCLike K] [NormedAddCommGroup E]
    [InnerProductSpace K E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace K F]
    [CompleteSpace F] (T : LinearPMap (RingHom.id K) E F) (hT : Dense (T.domain : Set E))
    (x : F) :
    (∀ y : T.domain, inner K x (T y) = 0) ↔
      (∃ hx : x ∈ (LinearPMap.adjoint T).domain, (LinearPMap.adjoint T) ⟨x, hx⟩ = 0) := by
  constructor
  · intro h
    have hzero : ∀ y : T.domain, inner K (0 : E) (y : E) = inner K x (T y) := by
      intro y
      rw [inner_zero_left, h y]
    refine ⟨LinearPMap.mem_adjoint_domain_of_exists (T := T) x ⟨0, hzero⟩, ?_⟩
    exact LinearPMap.adjoint_apply_eq (T := T) hT _ hzero
  · rintro ⟨hx, hx0⟩ y
    have hfa := LinearPMap.adjoint_isFormalAdjoint (T := T) hT
    have h1 := hfa ⟨x, hx⟩ y
    rw [hx0, inner_zero_left] at h1
    exact h1.symm

end Commons.Analysis.InnerProductSpace.LinearPMap
