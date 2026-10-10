import Mathlib.Control.Fix
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.CFTLib.Existence.exists_galois_normClassSubgroup_eq_of_cyclotomic_descent_deg
import Submission.NK.CFTLib.Existence.exists_galois_normClassSubgroup_le_of_kummer
import Submission.NK.CFTLib.Existence.index_comap_normClassHom_eq_prime
import Submission.NK.CFTLib.fundamentalClassElement
import Submission.NK.NUV2.ArtinBridge.isOpen_comap_normClassHom
import Submission.NK.NUV2.kernelCondition_all
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.cycloPrincipalId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.exists_idealModulus_of_natModulus
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.indexLeId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.langCyclicRelIndexId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.normKerId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.transfer.fracCoprimeId_relNormUnit
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.transfer.normRayId_map_relNormUnit_le
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.transfer.pow_finrank_mem_normRayId
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.productFormula_cyclotomic
import Submission.Work.SSGRoute.ZDataMup.IdealModulusContainmentProved
import Submission.Work.SSGRoute.ZDataMup.IdealModulusKernel.CycloPrincipalId
import Submission.Work.SSGRoute.ZDataMup.IdealModulusKernel.IndexLeIdId
import Submission.Work.SSGRoute.ZDataMup.MupAux.AuxId
import Submission.Work.SSGRoute.ZDataMup.MupAux.DescentId
import Submission.Work.SSGRoute.ZDataMup.MupAux.LImageId
import Submission.Work.SSGRoute.ZDataMup.MupAux.RestrictArtinId
import Submission.Work.SSGRoute.ZDataMup.MupAux.RestrictId
import Submission.Work.SSGRoute.ZDataMup.MupAux.ThetaKerId
import Submission.Work.SSGRoute.ZDataMup.MupAux.TransportId
import Submission.Work.SSGRoute.ZDataMup.abelian_of_cyclicCase
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom
import Submission.Work.SSGRoute.ZDataMup.mRam_ramifiedSupport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The restricted Artin map kills the norms of a subfield (commutative case, modulus explicit)

This is the global-class-field-theoretic step which converts the **orthogonality**
`x ∈ U' · N_{N/↥K} C_N` of the escape-form Grünwald theorem into the hypothesis
`α|_{M ⊓ N} = 1` required by the Čebotarev step (`EscapeCoreLib.exists_place_frobenius_of_compat`
or `N4Escape.escapePrimeFrobAtPrime`).

The file adapts `Work.SSGRoute.ZDataMup.restrictNormalHom_artinMap_clauses` (which is stated for
`L/K` **cyclic** and Frobenius-normalised at *every* unramified prime) to the two forms the
correction actually needs:

* `L/K` only **commutative** — this is what an abelian class field gives; the modulus input is the
  one supplied by `NK.CFTLib.artinReciprocityIdeal_proved` (which is proved for every commutative
  `L/K`), replacing `artinKillsPrincipal_cyclic`/`exists_admissible`;
* Φ only Frobenius-normalised **outside a given modulus `m`** — this is exactly what
  `exists_artinIso_frobAtPrime` (whose `Bad` is the set of primes containing the conductor) and
  `NK.CFTLib.Existence.exists_ideleArtinMap_of_arl` supply.

The conclusion used by the correction is the last one:
`res_M (Φ (N_{M/K} y)) = 1` for every `y ∈ 𝕀_M`, and its class-group form
`q ∈ N_{M/K}C_M ⟹ res_M (Φ x) = 1` for any idèle representative `x` of `q`.
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute.N4Escape

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

/-- Auxiliary: the restriction of the idèlic Artin map to a normal intermediate field kills the
idèlic norms of that intermediate field (via `ideleArtin_restrictNormalHom` and the norm-killing
of `ideleArtin` for the subextension).  Copy of `Work.SSGRoute.ZDataMup.restrictNormalHom_ideleArtin_kills_norms`. -/
theorem restrictNormalHom_ideleArtin_kills_norms
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (U : Subgroup (NK.GlobalCFT.Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M] [Normal K ↥M]
    (hcommM : ∀ a b : Gal(↥M/K), a * b = b * a) :
    ∀ y : NK.GlobalCFT.Idele ↥M,
      AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
        (NK.CFTLib.Arl.ideleArtin hcomm U hadj
          (NK.GlobalCFT.Idele.normIdeleHom K ↥M y)) = 1 := by
  haveI : IsGalois K ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  intro y
  rw [Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom (K := K) (L := L) hcomm m hm hram U hU hadj M hcommM
    (NK.GlobalCFT.Idele.normIdeleHom K ↥M y)]
  have hramM : ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 K), (m : 𝓞 K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 ↥M) = 1 := fun p hp =>
    NK.NUV2.ARL.ramificationIdxIn_eq_one_of_intermediateField (K := K) (L := L) M p (hram p hp)
  have hprincM : NK.CFTLib.artinKillsPrincipal K ↥M m :=
    NK.NUV2.ARL.artinKillsPrincipal_of_intermediateField (K := K) (L := L) M hram hprinc
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  have hadjN : ∀ y : NK.GlobalCFT.Idele ↥M, ∃ d : (↥M)ˣ,
      NK.GlobalCFT.Idele.normIdeleHom K ↥M
        (y * NK.GlobalCFT.Idele.principalIdele ↥M d) ∈ U := by
    intro y
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K ↥M m hm y
    exact ⟨d, by rw [hUeq]; exact hd⟩
  exact NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := ↥M) hcommM m hm
    hramM hprincM U hU hadj hadjN y

/-- **The restricted Artin map kills the norms of the intermediate field** (commutative case,
modulus explicit). -/
theorem restrictNormalHom_artinMap_kills_norms_of_modulus
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M] [Normal K ↥M]
    [IsGalois K ↥M]
    (Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L))
    (hP : ∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1)
    (hN : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (hF : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ Q.asIdeal →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) :
    ∀ y : NK.GlobalCFT.Idele ↥M, AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
        (Φ (NK.GlobalCFT.Idele.normIdeleHom K ↥M y)) = 1 := by
  classical
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  have hcommM : ∀ a b : Gal(↥M/K), a * b = b * a := by
    intro a b
    obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := L) a
    obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := L) b
    rw [← map_mul, ← map_mul, hcomm a' b']
  -- the idèlic Artin map attached to the modulus
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm
  obtain ⟨art, hagree, hprincipal, hgood, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin hcomm m hm hram hprinc U hU hadj
  -- `art` kills the idèlic norms
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  have hadjN : ∀ y : NK.GlobalCFT.Idele L, ∃ d : Lˣ,
      NK.GlobalCFT.Idele.normIdeleHom K L
        (y * NK.GlobalCFT.Idele.principalIdele L d) ∈ U := by
    intro y
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K L m hm y
    exact ⟨d, by rw [hUeq]; exact hd⟩
  have hnorm_art : ∀ y : NK.GlobalCFT.Idele L, art (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1 := by
    intro y
    rw [hagree]
    exact NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin (K := K) (L := L) hcomm m hm
      hram hprinc U hU hadj hadjN y
  -- the Artin reciprocity isomorphism attached to `art`
  have hPle_art : NK.GlobalCFT.Idele.principalSubgroup K ≤ art.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hx
    exact MonoidHom.mem_ker.mpr (hprincipal a)
  obtain ⟨e, he⟩ := NK.CFTLib.Existence.exists_artinIso_of_ideleArtin
    NK.CFTLib.fundamentalClassElement art hPle_art hnorm_art hsurj
  -- factor `Φ` through `C_K ⧸ N_{L/K} C_L`
  have hPle_Φ : NK.GlobalCFT.Idele.principalSubgroup K ≤ Φ.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hx
    exact MonoidHom.mem_ker.mpr (hP a)
  let Φbar : NK.GlobalCFT.IdeleClassGroup K →* (L ≃ₐ[K] L) :=
    QuotientGroup.lift (NK.GlobalCFT.Idele.principalSubgroup K) Φ hPle_Φ
  have hΦbar : ∀ x : NK.GlobalCFT.Idele K,
      Φbar (NK.GlobalCFT.IdeleClassGroup.mk K x) = Φ x :=
    fun x => QuotientGroup.lift_mk' _ _ x
  have hNle : NK.GlobalCFT.Idele.normClassSubgroup K L ≤ Φbar.ker := by
    intro z hz
    obtain ⟨x, hxmem, hmk⟩ := Subgroup.mem_map.mp hz
    have h1 : Φbar z = Φbar (NK.GlobalCFT.IdeleClassGroup.mk K x) := by rw [hmk]
    rw [MonoidHom.mem_ker, h1, hΦbar]
    obtain ⟨y, hy⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hxmem
    have hxy : x = NK.GlobalCFT.Idele.normIdeleHom K L y :=
      NK.GlobalCFT.Idele.ext (fun v => by rw [NK.GlobalCFT.Idele.normIdeleHom_apply]; exact hy v)
    rw [hxy, hN y]
  let χbar : NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L →*
      (L ≃ₐ[K] L) :=
    QuotientGroup.lift (NK.GlobalCFT.Idele.normClassSubgroup K L) Φbar hNle
  have hχbar : ∀ z : NK.GlobalCFT.IdeleClassGroup K,
      χbar (QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup K L) z) = Φbar z :=
    fun z => QuotientGroup.lift_mk' _ _ z
  let χ : (L ≃ₐ[K] L) →* (L ≃ₐ[K] L) := χbar.comp e.symm.toMonoidHom
  have hχ : ∀ x : NK.GlobalCFT.Idele K, χ (art x) = Φ x := by
    intro x
    have h1 : e.symm (art x) =
        QuotientGroup.mk' (NK.GlobalCFT.Idele.normClassSubgroup K L)
          (NK.GlobalCFT.IdeleClassGroup.mk K x) := by
      rw [← he x, MulEquiv.symm_apply_apply]
    change χbar (e.symm (art x)) = Φ x
    rw [h1, hχbar, hΦbar]
  -- `χ` fixes every Frobenius element, hence is the identity
  let Fix : Subgroup (L ≃ₐ[K] L) :=
    { carrier := {g : L ≃ₐ[K] L | χ g = g}
      one_mem' := map_one χ
      mul_mem' := by
        intro a b ha hb
        change χ a = a at ha
        change χ b = b at hb
        change χ (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        change χ a = a at ha
        change χ a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hFixTop : Fix = ⊤ := by
    refine NK.CFTLib.Arl.eq_top_of_forall_isFrobAtPrime_of_notMem (K := K) (L := L)
      (NK.CFTLib.Arl.primesDividing (K := K) m hm) Fix ?_
    intro p hpT σ hσ
    have hpm : (m : 𝓞 K) ∉ p.asIdeal := fun h =>
      hpT ((NK.CFTLib.Arl.mem_primesDividing (K := K) m hm p).mpr h)
    have hunr : NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p :=
      (NK.CFTLib.ArtinReciprocityIdeal.isUnramified_iff_ramificationIdxIn_eq_one (K := K) (L := L) p).mpr
        (hram p hpm)
    have hσeq : σ = NK.Chebotarev.frobAtPrime (K := K) (L := L) p :=
      (NK.Chebotarev.ExistsUniqueIsFrobAtPrime (K := K) (L := L) hcomm p hunr).unique hσ
        (NK.Chebotarev.isFrobAtPrime_frobAtPrime hcomm p hunr)
    have hcalc : χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) p)
        = NK.Chebotarev.frobAtPrime (K := K) (L := L) p := by
      calc χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) p)
          = χ (art (NK.HeckeL.ideleOfPrime K p)) := by rw [hgood p hpm]
        _ = Φ (NK.HeckeL.ideleOfPrime K p) := hχ _
        _ = NK.Chebotarev.frobAtPrime (K := K) (L := L) p := hF p hpm
    rw [hσeq]
    show χ (NK.Chebotarev.frobAtPrime (K := K) (L := L) p) = NK.Chebotarev.frobAtPrime (K := K) (L := L) p
    exact hcalc
  have hχid : χ = MonoidHom.id (L ≃ₐ[K] L) := by
    refine MonoidHom.ext fun g => ?_
    have hg : g ∈ Fix := by rw [hFixTop]; exact Subgroup.mem_top g
    show χ g = g
    exact hg
  have hΦart : Φ = art := by
    refine MonoidHom.ext fun x => ?_
    rw [← hχ x, hχid]
    rfl
  intro y
  rw [hΦart, hagree]
  exact restrictNormalHom_ideleArtin_kills_norms hcomm m hm hram hprinc U hU hadj M hcommM y

/-- **The class-group form.**  An idèle class in the norm subgroup of the intermediate field is
killed by the restricted Artin map. -/
theorem restrictNormalHom_artinMap_kills_normClassSubgroup_of_modulus
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)]
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K L m)
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M] [Normal K ↥M]
    [IsGalois K ↥M]
    (Φ : NK.GlobalCFT.Idele K →* (L ≃ₐ[K] L))
    (hP : ∀ a : Kˣ, Φ (NK.GlobalCFT.Idele.principalIdele K a) = 1)
    (hN : ∀ y : NK.GlobalCFT.Idele L, Φ (NK.GlobalCFT.Idele.normIdeleHom K L y) = 1)
    (hF : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ Q.asIdeal →
        Φ (NK.HeckeL.ideleOfPrime K Q) = NK.Chebotarev.frobAtPrime (K := K) (L := L) Q) :
    ∀ (q : NK.GlobalCFT.IdeleClassGroup K), q ∈ NK.GlobalCFT.Idele.normClassSubgroup K ↥M →
      ∀ x : NK.GlobalCFT.Idele K, NK.GlobalCFT.IdeleClassGroup.mk K x = q →
        AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M (Φ x) = 1 := by
  intro q hq x hx
  -- a norm idèle representative of `q`
  obtain ⟨x₀, hx₀, hx₀q⟩ := Subgroup.mem_map.mp hq
  rw [NK.GlobalCFT.Idele.normImage_eq_map, MonoidHom.mem_range] at hx₀
  obtain ⟨z, rfl⟩ := hx₀
  have hxq : NK.GlobalCFT.IdeleClassGroup.mk K x =
      NK.GlobalCFT.IdeleClassGroup.mk K (NK.GlobalCFT.Idele.normIdeleHom K ↥M z) := by
    rw [hx, hx₀q]
  have hprin : x⁻¹ * NK.GlobalCFT.Idele.normIdeleHom K ↥M z ∈
      NK.GlobalCFT.Idele.principalSubgroup K :=
    NK.GlobalCFT.IdeleClassGroup.mk_eq_mk_iff.mp hxq
  have hΦ1 : Φ (x⁻¹ * NK.GlobalCFT.Idele.normIdeleHom K ↥M z) = 1 := by
    obtain ⟨a, ha⟩ := NK.GlobalCFT.Idele.mem_principalSubgroup.mp hprin
    rw [← ha]
    exact hP a
  rw [map_mul, map_inv] at hΦ1
  have hΦx : Φ x = Φ (NK.GlobalCFT.Idele.normIdeleHom K ↥M z) := inv_mul_eq_one.mp hΦ1
  rw [hΦx]
  exact restrictNormalHom_artinMap_kills_norms_of_modulus m hm hram hprinc M Φ hP hN hF z

end Work.SSGRoute.N4Escape
