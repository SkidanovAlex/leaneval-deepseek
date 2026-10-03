import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.hasIndicableLabelling_of_indicable
import Submission.Work.ORLocInd.Howie.indicable_of_labelling

namespace Work.ORLocInd.Howie

/-- **L3 of `N4_LOCIND_LEAD.md`: indicability transfers along vertex-wise isomorphisms of the
presented groupoids.**

If `e : W ≃ V` matches the vertices of a presentation `P₂` on `W` with those of a presentation `P`
on `V`, if `ι x : π₁(⟨Γ₂ | R₂⟩, x) →* π₁(⟨Γ | R⟩, e x)` are bijective for all `x`, and if `P₂`
admits an indicable labelling, then so does `P`.

The proof is the one described in the lead note: a labelling of `P₂` with a closed path of non-zero
level exhibits a vertex `x` whose presented vertex group `π₁(⟨Γ₂ | R₂⟩, x)` is *indicable*
(`indicable_of_labelling`); a bijective homomorphism is an isomorphism, so the same surjection onto
`Multiplicative ℤ` exists on `π₁(⟨Γ | R⟩, e x)`; and indicability of a single vertex group produces
a labelling with a closed path of non-zero level (`hasIndicableLabelling_of_indicable`). -/
theorem hasIndicableLabelling_of_bijective {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) {W : Type*} [Quiver W] [Quiver.HasInvolutiveReverse W]
    (P₂ : Work.ORLocInd.Howie.Presentation W) (e : W ≃ V)
    (ι : ∀ x : W, P₂.vertexGroup x →* P.vertexGroup (e x)) (hb : ∀ x, Function.Bijective (ι x)) :
    P₂.HasIndicableLabelling → P.HasIndicableLabelling := by
  intro h
  -- a labelling of `P₂` with a closed path of non-zero level makes a vertex group indicable
  obtain ⟨L₂, hL₂, x, p, hp⟩ := h
  obtain ⟨φ₂, hφ₂⟩ := indicable_of_labelling P₂ L₂ hL₂ p hp
  -- a bijective homomorphism of groups is an isomorphism
  let ee : P₂.vertexGroup x ≃* P.vertexGroup (e x) := MulEquiv.ofBijective (ι x) (hb x)
  -- so the vertex group of `P` at `e x` is indicable as well
  refine hasIndicableLabelling_of_indicable P (e x) (φ₂.comp ee.symm.toMonoidHom) ?_
  exact hφ₂.comp ee.symm.surjective

end Work.ORLocInd.Howie
