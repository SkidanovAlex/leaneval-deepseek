import Mathlib
import Submission.Work.SSGRoute.PT.AlphaPairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exactness of the invariants functor at the middle term

For a complex `N →φ N₂ →ψ N₁` of `G`-modules with `φ` injective and `ker ψ ≤ range φ`
(the exactness of `0 → N →φ N₂ →ψ N₁`), the induced sequence on invariants is exact at the
middle: `range (invariantsHom φ hφ) = ker (invariantsHom ψ hψ)`.

This is the exactness input that `PT/AlphaTwoInputs.lean` needs to discharge `hbot`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.SSGRoute.PT

theorem range_invariantsHom_eq_ker {G : Type*} [Group G]
    {N : Type*} [AddCommGroup N] [DistribMulAction G N]
    {N₂ : Type*} [AddCommGroup N₂] [DistribMulAction G N₂]
    {N₁ : Type*} [AddCommGroup N₁] [DistribMulAction G N₁]
    (φ : N →+ N₂) (ψ : N₂ →+ N₁)
    (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ)
    (hφ_inj : Function.Injective φ) (hφψ : ∀ x : N, ψ (φ x) = 0)
    (hψk : ψ.ker ≤ φ.range) :
    (invariantsHom φ hφ).range = (invariantsHom ψ hψ).ker := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    rw [AddMonoidHom.mem_ker]
    apply Subtype.ext
    show ψ (φ (x : N)) = 0
    exact hφψ (x : N)
  · intro y hy
    rw [AddMonoidHom.mem_ker] at hy
    have hy' : (y : N₂) ∈ ψ.ker := AddMonoidHom.mem_ker.mpr (congrArg Subtype.val hy)
    obtain ⟨n, hn⟩ := hψk hy'
    refine ⟨⟨n, ?_⟩, Subtype.ext ?_⟩
    · intro g
      apply hφ_inj
      rw [hφ g n, hn]
      exact y.2 g
    · show φ n = (y : N₂)
      exact hn

end Work.SSGRoute.PT
