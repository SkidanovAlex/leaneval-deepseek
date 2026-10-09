import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
import Submission.NK.CFTLib.Existence.artinKernel
import Submission.NK.CFTLib.fundamentalClassElement
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity

open NK.GlobalCFT

/-- **The idèlic Artin map of a congruence datum has kernel the norms times the principal
idèles.**  Let `L / K` be a finite Galois extension of number fields with commutative Galois
group, `m > 0` a modulus whose support contains the ramified primes, `hprinc` the ideal-theoretic
reciprocity law at modulus `m` (the product condition `NK.CFTLib.artinKillsPrincipal`), and let
`U ≤ 𝕀 K` be a congruence subgroup of modulus `m` such that every idèle can be adjusted by a
principal idèle into `U`.  Then there is an idèlic Artin map
`art : 𝕀 K →* Gal(L/K)` which is surjective and whose kernel is exactly
`N_{L/K} 𝕀 L ⊔ Kˣ`.

The map is the idèlic Artin map `NK.CFTLib.Arl.ideleArtin` built from the reciprocity law
(`NK.CFTLib.Arl.exists_monoidHom_ideleArtin`); it kills the principal idèles by construction and
the idèlic norms by `NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin`.  The reverse inclusion is
the index statement of class field theory: the Artin map on the idèle class group has kernel
`N_{L/K} C_L` (`NK.CFTLib.Existence.ker_artinMapCK_eq_normClassSubgroup`, from the global
fundamental class `NK.CFTLib.fundamentalClassElement`). -/
theorem exists_artinMap_ker_eq_normImage_sup_principal {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (m : ℕ) (hm : 0 < m) (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), (m : NumberField.RingOfIntegers K) ∉ p.asIdeal → Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1) (hprinc : NK.CFTLib.artinKillsPrincipal K L m) (U : Subgroup (NK.GlobalCFT.Idele K)) (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U) (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ, x * NK.GlobalCFT.Idele.principalIdele K b ∈ U) : ∃ art : NK.GlobalCFT.Idele K →* Gal(L/K), MonoidHom.ker art = NK.GlobalCFT.Idele.normImage K L ⊔ NK.GlobalCFT.Idele.principalSubgroup K ∧ Function.Surjective art := by
  classical
  haveI : IsMulCommutative (Gal(L/K)) := IsMulCommutative.of_comm hcomm
  -- the idèlic Artin map attached to the congruence datum
  obtain ⟨art, hagree, hprincipal, _hgood, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin (K := K) (L := L) hcomm m hm hram hprinc
      U hU hadj
  -- `U` really is the concrete congruence subgroup of modulus `m`
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  -- the map kills the idèlic norms
  have hnorm : ∀ y : Idele L, art (Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hagree]
    refine NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm m hm hram
      hprinc U hU hadj ?_ y
    intro z
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L m hm z
    exact ⟨d, hUeq ▸ hd⟩
  -- the map kills the principal idèles
  have hPle : Idele.principalSubgroup K ≤ art.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := Idele.mem_principalSubgroup.mp hx
    exact MonoidHom.mem_ker.mpr (hprincipal a)
  -- the kernel is the join of the norms and the principal idèles
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
  exact ⟨art, hker, hsurj⟩

end Work.SSGRoute.ZDataMup.ArtinReciprocity
