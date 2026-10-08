import Mathlib
import Submission.Work.Hering.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step5

/-- The automorphism `normalizerMonoidHom U g` of `U` acts by conjugating (in `G`) with the
underlying element of `g`. -/
private theorem normalizerMonoidHom_apply_coe {G : Type*} [Group G] {H : Subgroup G}
    (g : Subgroup.normalizer (H : Set G)) (h : H) :
    ((Subgroup.normalizerMonoidHom H g) h : G) = (g : G) * (h : G) * (g : G)⁻¹ := by
  simp only [Subgroup.normalizerMonoidHom, MulDistribMulAction.toMulAut_apply,
    MulDistribMulAction.toMulEquiv_apply]
  rfl

/-- If conjugation by `g0` realizes a group automorphism `φ` of a subgroup `U` of `G`, then `g0`
lies in the normalizer of `U` and the action of `g0` on `U` (given by `normalizerMonoidHom`) is
exactly `φ`. -/
theorem exists_normalizerMonoidHom_eq_of_conj {G : Type*} [Group G] {U : Subgroup G} {g0 : G}
    {φ : MulAut U} (h : ∀ u : U, g0 * (u : G) * g0⁻¹ = (φ u : G)) :
    ∃ g : Subgroup.normalizer (U : Set G), Subgroup.normalizerMonoidHom U g = φ := by
  -- `g0` normalizes `U`: conjugation by `g0` maps `U` onto `U` since it agrees with the
  -- automorphism `φ` of `U`.
  have hg0 : g0 ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [h ⟨n, hn⟩]
      exact (φ ⟨n, hn⟩).2
    · intro hn
      -- surjectivity of `φ` provides a preimage `u ∈ U` of `g0 * n * g0⁻¹`
      obtain ⟨u, hu⟩ := φ.surjective ⟨g0 * n * g0⁻¹, hn⟩
      have h2 : g0 * (u : G) * g0⁻¹ = g0 * n * g0⁻¹ := by
        rw [h u]
        exact congrArg Subtype.val hu
      have h3 : (u : G) = n := mul_left_cancel (mul_right_cancel h2)
      rw [← h3]
      exact u.2
  refine ⟨⟨g0, hg0⟩, ?_⟩
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  rw [normalizerMonoidHom_apply_coe]
  exact h u

end Work.Hering.Step5
