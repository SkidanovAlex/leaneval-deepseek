import Mathlib

namespace Work.OROneRel

/-- If a homomorphism `f : FreeGroup β →* FreeGroup β` sends each free generator either to `1`
or to itself, then every element `y` agrees with `f y` modulo the normal closure of the generators
that `f` kills.  Equivalently, `f` is the identity after quotienting by
`N = normalClosure (of '' {b | f (of b) = 1})`.

This is used in the proof that `f` behaves like the projection onto the free factor spanned by the
generators fixed by `f`. -/
theorem mul_tau_inv_mem {β : Type*} (f : FreeGroup β →* FreeGroup β)
    (hf : ∀ b : β, f (FreeGroup.of b) = 1 ∨ f (FreeGroup.of b) = FreeGroup.of b) (y : FreeGroup β) :
    y * (f y)⁻¹ ∈ Subgroup.normalClosure (FreeGroup.of '' {b : β | f (FreeGroup.of b) = 1}) := by
  set S : Set (FreeGroup β) := FreeGroup.of '' {b : β | f (FreeGroup.of b) = 1} with hS
  -- The quotient map to the group modulo `N = normalClosure S` agrees with its composite with `f`;
  -- this is checked on generators.
  have hqf : (QuotientGroup.mk' (Subgroup.normalClosure S)).comp f
      = QuotientGroup.mk' (Subgroup.normalClosure S) := by
    apply FreeGroup.ext_hom
    intro b
    rcases hf b with h | h
    · -- `f` kills `of b`, and `of b` lies in `S`, hence in the kernel of the quotient map.
      simp only [MonoidHom.comp_apply, h, map_one]
      rw [QuotientGroup.mk'_apply]
      exact ((QuotientGroup.eq_one_iff (FreeGroup.of b)).mpr
        (Subgroup.subset_normalClosure (show FreeGroup.of b ∈ S from ⟨b, h, rfl⟩))).symm
    · -- `f` fixes `of b`.
      simp only [MonoidHom.comp_apply, h]
  -- Hence `y * (f y)⁻¹` maps to `1` in the quotient, i.e. it lies in `N`.
  have hker : y * (f y)⁻¹ ∈ (QuotientGroup.mk' (Subgroup.normalClosure S)).ker := by
    rw [MonoidHom.mem_ker]
    rw [map_mul, map_inv, ← MonoidHom.comp_apply, DFunLike.congr_fun hqf y, mul_inv_cancel]
  rw [QuotientGroup.ker_mk'] at hker
  exact hker

end Work.OROneRel
