import Mathlib
import Submission.NK.CFTLib.normClassSubgroup_smul_mem
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.NUV2.ArtinBridge.action_trivial_of_coprime_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib

open NK.GlobalCFT

/-- **The `Gal(M/K)`-action on the norm quotient `C_M ⧸ N_{L/M} C_L` is trivial.**

For a tower `K ⊆ M ⊆ L` of number fields with `M/K`, `L/M`, `L/K` Galois of prime degree `p`, the
norm subgroup `N_{L/M} C_L` has index `p` in `C_M` (the field axiom for the *cyclic* extension
`L/M` of prime degree, `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`), and the group
`Gal(M/K)` has order `p`.  Since `N_{L/M} C_L` is `Gal(M/K)`-stable
(`NK.CFTLib.normClassSubgroup_smul_mem`), the action descends to the quotient of order `p`, whose
automorphism group has order `p - 1`; an element of order dividing `p` therefore acts trivially.
This is exactly `NK.NUV2.ArtinBridge.action_trivial_of_coprime_card`. -/
theorem smul_mul_inv_mem_normClassSubgroup {K M L : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L] [IsGalois K M] [IsGalois M L] [IsGalois K L] (p : ℕ) (hp : p.Prime) (hKM : Module.finrank K M = p) (hML : Module.finrank M L = p) : ∀ (σ : Gal(M/K)) (a : NK.GlobalCFT.IdeleClassGroup M), σ • a * a⁻¹ ∈ NK.GlobalCFT.Idele.normClassSubgroup M L := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- `L/M` is cyclic of prime degree, so the norm quotient has order `p`
  haveI hcycL : IsCyclic (L ≃ₐ[M] L) :=
    isCyclic_of_prime_card (α := L ≃ₐ[M] L)
      (by rw [IsGalois.card_aut_eq_finrank M L, hML])
  have hindex : (NK.GlobalCFT.Idele.normClassSubgroup M L).index = p := by
    rw [NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic (K := M) (L := L), hML]
  have hcardQuot : Nat.card (NK.GlobalCFT.IdeleClassGroup M ⧸
      NK.GlobalCFT.Idele.normClassSubgroup M L) = p := by
    rw [← Subgroup.index_eq_card (NK.GlobalCFT.Idele.normClassSubgroup M L), hindex]
  -- `Gal(M/K)` has order `p`, hence order coprime to `p - 1`
  have hcardGal : Nat.card (M ≃ₐ[K] M) = p := by
    rw [IsGalois.card_aut_eq_finrank K M, hKM]
  have hcop : (Nat.card (M ≃ₐ[K] M)).Coprime (p - 1) := by
    rw [hcardGal]
    exact (Nat.coprime_self_sub_right hp.one_le).mpr (Nat.coprime_one_right p)
  -- the norm subgroup is `Gal(M/K)`-stable
  have hstab : ∀ (σ : M ≃ₐ[K] M) {b : NK.GlobalCFT.IdeleClassGroup M},
      b ∈ NK.GlobalCFT.Idele.normClassSubgroup M L →
        σ • b ∈ NK.GlobalCFT.Idele.normClassSubgroup M L :=
    fun σ b hb => NK.CFTLib.normClassSubgroup_smul_mem (K := K) (M := M) (L := L) σ b hb
  exact NK.NUV2.ArtinBridge.action_trivial_of_coprime_card
    (NK.GlobalCFT.Idele.normClassSubgroup M L) hstab p hp hcardQuot hcop

end NK.CFTLib
