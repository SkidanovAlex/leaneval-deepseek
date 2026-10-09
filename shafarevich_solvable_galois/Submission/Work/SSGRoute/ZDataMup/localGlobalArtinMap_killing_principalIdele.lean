import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.Work.SSGRoute.NKExistenceImport
import Submission.NK.CFTLib.Existence.artinKernel
import Submission.NK.CFTLib.IdeleHasse.localFaithful_onePlace
import Submission.NK.NUV2.ARL.normAdjustment
import Submission.Work.SSGRoute.ZDataMup.nonempty_artinReciprocity_of_abelian
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

open NK.GlobalCFT

/-- Commutativity of the Galois group of a cyclic extension, as a plain hypothesis. -/
theorem comm_of_isCyclic {G : Type*} [Group G] [IsCyclic G] :
    ∀ a b : G, a * b = b * a := by
  intro a b
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  rw [← zpow_add, ← zpow_add, add_comm m n]

theorem localGlobalArtinMap_killing_principalIdele {K : Type} [Field K] [NumberField K]
    {L : Type} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcyc : IsCyclic (L ≃ₐ[K] L)) :
    ∃ Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L), Function.Surjective Φ ∧
      (∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1) ∧
      (∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1) ∧
      (∀ (v : NK.GlobalCFT.Place K) (a : (NK.GlobalCFT.Place.localField K v)ˣ),
        Φ (NK.HassePrinciple.onePlace v a) = 1 ↔
          NK.HassePrinciple.onePlace v a ∈ NK.GlobalCFT.Idele.normImage K L) ∧
      (∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        NK.HeckeL.IsUnramifiedIn (K := K) (L := L) Q →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) := by
  classical
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := comm_of_isCyclic
  haveI : IsMulCommutative (L ≃ₐ[K] L) := IsMulCommutative.of_comm hcomm
  -- the ideal-theoretic reciprocity law
  obtain ⟨m, hm, hramIn, hprincIn⟩ := NK.CFTLib.artinReciprocityIdeal_proved K L hcomm
  -- the congruence subgroup of modulus `m`, with an adjustment
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  -- the idèlic Artin map
  obtain ⟨art, hagree, hprincipal, hgood, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm m hm hramIn hprincIn
      U hU hadj
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  -- the norm clause
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hagree]
    refine NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm m hm hramIn
      hprincIn U hU hadj ?_ y
    intro z
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L m hm z
    exact ⟨d, hUeq ▸ hd⟩
  -- the kernel of `art` is the join of the norm image and the principal idèles
  have hPle : Idele.principalSubgroup K ≤ art.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := Idele.mem_principalSubgroup.mp hx
    exact MonoidHom.mem_ker.mpr (hprincipal a)
  have hker : art.ker = Idele.normImage K L ⊔ Idele.principalSubgroup K := by
    have hFC := NK.CFTLib.fundamentalClassElement
    have h1 := NK.CFTLib.Existence.ker_artinMapCK_eq_normClassSubgroup (K := K) (L := L)
      hFC art hPle hnorm hsurj
    refine le_antisymm ?_ ?_
    · intro x hx
      have hmk : IdeleClassGroup.mk K x ∈ (NK.CFTLib.Existence.artinMapCK art hPle).ker := by
        rw [MonoidHom.mem_ker, NK.CFTLib.Existence.artinMapCK_mk]
        exact MonoidHom.mem_ker.mp hx
      rw [h1] at hmk
      obtain ⟨n, hn, hmn⟩ := Subgroup.mem_map.mp hmk
      have h2 : n⁻¹ * x ∈ Idele.principalSubgroup K :=
        (IdeleClassGroup.mk_eq_mk_iff).mp hmn
      have h3 : n * (n⁻¹ * x) ∈ Idele.normImage K L ⊔ Idele.principalSubgroup K :=
        Subgroup.mul_mem_sup hn h2
      rwa [mul_inv_cancel_left] at h3
    · refine sup_le ?_ hPle
      intro x hx
      obtain ⟨y, hy⟩ := Idele.mem_normImage.mp hx
      rw [MonoidHom.mem_ker,
        show x = Idele.normIdeleHom K L y from
          Idele.ext (fun v => by rw [Idele.normIdeleHom_apply]; exact hy v)]
      exact hnorm y
  refine ⟨art, hsurj, hnorm, hprincipal, ?_, ?_⟩
  · intro v a
    rw [← MonoidHom.mem_ker, hker]
    exact ⟨NK.CFTLib.IdeleHasse.localFaithful_onePlace (K := K) (L := L) hcyc,
      fun h => Subgroup.mem_sup_left h⟩
  · intro Q hunr
    rw [hagree]
    exact ideleArtin_ideleOfPrime_of_unramified (K := K) (L := L) hcomm m hm hramIn hprincIn
      U hU hadj hunr

end Work.SSGRoute.ZDataMup
