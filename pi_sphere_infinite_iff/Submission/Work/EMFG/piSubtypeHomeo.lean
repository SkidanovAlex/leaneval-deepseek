import Mathlib

namespace Work.EMFG

/-- The set `Set.pi Set.univ W` (with the subspace topology inherited from the
product `∀ i, X i`) is homeomorphic to the product `∀ i, ↥(W i)` of the subtypes
`W i` (with the product topology). The homeomorphism is the evident one sending
`f` to `fun i => ⟨f i, _⟩`. -/
theorem piSubtypeHomeo {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (W : ∀ i, Set (X i)) :
    Nonempty (↥(Set.pi Set.univ W) ≃ₜ ((i : ι) → ↥(W i))) := by
  have h1 : Continuous (fun f : ↥(Set.pi Set.univ W) => fun i =>
      (⟨(f : ∀ i, X i) i, f.2 i trivial⟩ : ↥(W i))) :=
    continuous_pi fun i =>
      ((continuous_apply i).comp
        (continuous_subtype_val : Continuous
          (Subtype.val : ↥(Set.pi Set.univ W) → (i : ι) → X i))).subtype_mk
        (fun f => f.2 i trivial)
  have h2 : Continuous (fun g : ((i : ι) → ↥(W i)) =>
      (⟨fun i => (g i : X i), fun i _ => (g i).2⟩ : ↥(Set.pi Set.univ W))) :=
    (continuous_pi fun i => (continuous_apply i).subtype_val).subtype_mk (fun g i _ => (g i).2)
  exact ⟨{ toEquiv := Equiv.Set.univPi W, continuous_toFun := h1, continuous_invFun := h2 }⟩

end Work.EMFG
