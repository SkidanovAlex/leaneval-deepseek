import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup
import Submission.NK.CFTLib.normClassSubgroup_closure_normClassHom_eq_one
import Submission.NK.CFTLib.mem_sup_fixedPoints_of_prime_card
import Submission.NK.CFTLib.smul_mul_inv_mem_normClassSubgroup
import Submission.NK.CFTLib.exists_addOrderOf_eq_card_of_cyclic_normClassQuotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib

open NK.GlobalCFT

theorem normClassSubgroup_sup_range_eq_top
    {K L M : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
    [NumberField M] [Algebra K L] [Algebra K M] [Algebra M L] [IsScalarTower K M L]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional M L]
    [IsGalois K L] [IsGalois K M] [IsGalois M L] [IsCyclic (L ≃ₐ[K] L)]
    (p : ℕ) (hp : p.Prime) (hcard : Nat.card (L ≃ₐ[K] L) = p ^ 2)
    (hM : Module.finrank K M = p)
    (ψ : NK.GlobalCFT.IdeleClassGroup K →* NK.GlobalCFT.IdeleClassGroup M)
    (hψ : ∀ q : NK.GlobalCFT.IdeleClassGroup M,
      (∀ σ : M ≃ₐ[K] M, σ • q = q) ↔ q ∈ ψ.range) :
    ψ.range ⊔ NK.GlobalCFT.Idele.normClassSubgroup M L = ⊤ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  -- ### numerical facts about the tower
  have hKM : Module.finrank K M = p := hM
  have hLK : Module.finrank K L = p ^ 2 := by
    rw [← IsGalois.card_aut_eq_finrank K L, hcard]
  have hML : Module.finrank M L = p := by
    have h := Module.finrank_mul_finrank K M L
    rw [hKM, hLK, pow_two] at h
    exact Nat.mul_left_cancel hp.pos h
  have hQcard : Nat.card (M ≃ₐ[K] M) = p := by
    rw [IsGalois.card_aut_eq_finrank K M, hKM]
  haveI hcycML : IsCyclic (L ≃ₐ[M] L) :=
    isCyclic_of_prime_card (α := L ≃ₐ[M] L)
      (by rw [IsGalois.card_aut_eq_finrank M L, hML])
  -- ### the index formula and the cardinality of the norm class quotient
  have hindex : (NK.GlobalCFT.Idele.normClassSubgroup M L).index = p := by
    rw [NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic (K := M) (L := L), hML]
  have hBcard :
      Nat.card (NK.GlobalCFT.IdeleClassGroup M ⧸
        NK.GlobalCFT.Idele.normClassSubgroup M L) = p := by
    rw [← Subgroup.index_eq_card, hindex]
  -- ### the two hypotheses of the group-theoretic step
  have hact : ∀ (σ : M ≃ₐ[K] M) (a : NK.GlobalCFT.IdeleClassGroup M),
      σ • a * a⁻¹ ∈ NK.GlobalCFT.Idele.normClassSubgroup M L :=
    NK.CFTLib.smul_mul_inv_mem_normClassSubgroup (K := K) (M := M) (L := L) p hp hKM hML
  -- the norm-one elements of the norm subgroup are coboundaries
  obtain ⟨ι, hιinj, -, hιnorm⟩ := NK.CFTLib.exists_inclusion_normClassHom_prod K M
  have hker : ∀ n : ↥(NK.GlobalCFT.Idele.normClassSubgroup M L),
      (∏ σ : M ≃ₐ[K] M, σ • (n : NK.GlobalCFT.IdeleClassGroup M)) = 1 →
      ((n : NK.GlobalCFT.IdeleClassGroup M) ∈ Subgroup.closure {x : NK.GlobalCFT.IdeleClassGroup M |
        ∃ σ : M ≃ₐ[K] M, ∃ m : ↥(NK.GlobalCFT.Idele.normClassSubgroup M L),
          x = σ • (m : NK.GlobalCFT.IdeleClassGroup M) *
            (m : NK.GlobalCFT.IdeleClassGroup M)⁻¹}) := by
    intro n hn
    have hn' : NK.GlobalCFT.IdeleClassGroup.normClassHom K M
        (n : NK.GlobalCFT.IdeleClassGroup M) = 1 := by
      apply hιinj
      rw [hιnorm (n : NK.GlobalCFT.IdeleClassGroup M), map_one]
      exact hn
    have hmem := NK.CFTLib.normClassSubgroup_closure_normClassHom_eq_one (K := K) (M := M)
      (L := L) p hp hKM hML (n : NK.GlobalCFT.IdeleClassGroup M) n.2 hn'
    refine Subgroup.closure_mono ?_ hmem
    rintro x ⟨σ, m, hm, rfl⟩
    exact ⟨σ, ⟨m, hm⟩, rfl⟩
  -- ### the group-theoretic conclusion
  have hmain : ∀ a : NK.GlobalCFT.IdeleClassGroup M,
      a ∈ Subgroup.closure {x : NK.GlobalCFT.IdeleClassGroup M |
            ∀ σ : M ≃ₐ[K] M, σ • x = x} ⊔
        NK.GlobalCFT.Idele.normClassSubgroup M L :=
    fun a => NK.CFTLib.mem_sup_fixedPoints_of_prime_card (p := p) hp
      (Q := M ≃ₐ[K] M) (A := NK.GlobalCFT.IdeleClassGroup M) hQcard
      (NK.GlobalCFT.Idele.normClassSubgroup M L) hact hker a
  -- ### the fixed-point subgroup is the range of `ψ`
  have hfix : Subgroup.closure {x : NK.GlobalCFT.IdeleClassGroup M |
      ∀ σ : M ≃ₐ[K] M, σ • x = x} = ψ.range := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      exact (hψ x).mp hx
    · intro x hx
      exact Subgroup.subset_closure ((hψ x).mpr hx)
  rw [← hfix]
  exact eq_top_iff.mpr fun a _ => hmain a

end NK.CFTLib
