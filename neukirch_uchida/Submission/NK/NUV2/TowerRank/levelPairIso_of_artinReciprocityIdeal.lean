import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.fcElement_of_arl
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup
import Submission.NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero
import Submission.NK.NUV2.RouteB.LangX.artinSymbol_restrictNormalHom
import Submission.NK.NUV2.ArtinBridge.levelPairIso
import Submission.NK.NUV2.TowerRank.normClassSubgroup_fixedField_commutator
import Submission.NK.NUV2.TowerRank.normClassSubgroup_fixedField_sup_commutator_of_normal
import Submission.NK.GlobalCFTdeep.Transport.NormGroupTransport

/-!
# `LevelPairIso` from the ideal-theoretic Artin reciprocity law

`NK.NUV2.ArtinBridge.LevelPairIso K Ω ℓ` is the levelwise norm-group/Galois-subgroup
correspondence: for every finite `ℓ`-level `M/K` of `Ω` there is an isomorphism
`C_K ⧸ N_{M/K}C_M ≃* Gal(M/K)^{ab}` carrying, for every `ℓ`-sublevel `L ⊆ M`, the image of
`N_{L/K}C_L` onto the kernel of the restriction `Gal(M/K)^{ab} → Gal(L/K)^{ab}`.

This file proves it from the **ideal-theoretic Artin reciprocity law**
`NK.CFTLib.ArtinReciprocityIdeal` (Lang, *ANT*, Ch. X; the raw integer-modulus form).  The route is
the one recorded in `NOTES.md` §10:

* from the law one builds the idèlic Artin map `𝕀 K →* Gal(F/K)` of an abelian level `F/K`
  (killing the principal idèles and the norms, Frobenius-normalised, with open kernel and
  `ker = Kˣ · N_{F/K}𝕀 F`), using `NK.CFTLib.Arl.exists_monoidHom_ideleArtin` and the norm
  index theorem `NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement`
  derived from the global fundamental class `NK.CFTLib.fcElement_of_arl`;
* the **crux** is the compatibility of these idèlic maps with restriction to an intermediate field,
  `NK.NUV2.TowerRank.ideleArtin_restrictNormalHom`: two idèlic Artin maps built from the *same*
  modulus and the *same* congruence subgroup are intertwined by `AlgEquiv.restrictNormalHom`.  This
  is the "norm functoriality" of the Artin map, and it follows from the functoriality of the
  fractional-ideal Artin symbol `NK.NUV2.TowerRank.artinSym_restrictNormalHom`;
* the level pairing is then obtained from the norm limitation theorem
  (`NK.NUV2.TowerRank.normClassSubgroup_fixedField_commutator` and its normal-subgroup version
  `NK.NUV2.TowerRank.normClassSubgroup_fixedField_sup_commutator_of_normal`), the exactness of the
  level maps (`levelRestrict_ker`) and a cardinality count.

The main theorem is `NK.NUV2.TowerRank.levelPairIso_of_artinReciprocityIdeal`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.NUV2.TowerRank

open NK.GlobalCFT (Idele IdeleClassGroup)
open scoped NumberField

/-- Unramifiedness of primes outside `(m)` is inherited by a multiple modulus. -/
theorem ramificationIdxIn_eq_one_of_dvd {K F : Type*} [Field K] [NumberField K] [Field F]
    [NumberField F] [Algebra K F] {m m' : ℕ} (hdvd : m ∣ m')
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 F) = 1)
    (p : NK.Chebotarev.PrimeIdeal K) (hp : (m' : 𝓞 K) ∉ p.asIdeal) :
    Ideal.ramificationIdxIn p.asIdeal (𝓞 F) = 1 := by
  obtain ⟨k, rfl⟩ := hdvd
  refine hram p (fun hcon => hp ?_)
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right (k : 𝓞 K) p.asIdeal hcon

/-- The product condition of the Artin reciprocity law is inherited by a multiple modulus. -/
theorem artinKillsPrincipal_of_dvd {K F : Type*} [Field K] [NumberField K] [Field F]
    [NumberField F] [Algebra K F] [IsGalois K F] {m m' : ℕ} (hdvd : m ∣ m')
    (h : NK.CFTLib.artinKillsPrincipal K F m) :
    NK.CFTLib.artinKillsPrincipal K F m' := by
  intro a ha hpos s e σ hs hfac hfrob
  obtain ⟨k, rfl⟩ := hdvd
  have hle : Ideal.span {(((m * k : ℕ)) : 𝓞 K)} ≤ Ideal.span {(m : 𝓞 K)} := by
    rw [Ideal.span_singleton_le_iff_mem]
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right (k : 𝓞 K) _ (Ideal.mem_span_singleton_self (m : 𝓞 K))
  refine h a (hle ha) hpos s e σ (fun p hp hcon => ?_) hfac hfrob
  exact hs p hp (by
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right (k : 𝓞 K) p.asIdeal hcon)

/-- **The abelianisation of a commutative group has the same cardinality.** -/
theorem natCard_abelianization_of_comm {G : Type*} [Group G] [IsMulCommutative G] :
    Nat.card (Abelianization G) = Nat.card G := by
  have h : commutator G = ⊥ := (commutator_eq_bot_iff G).mpr inferInstance
  calc Nat.card (Abelianization G) = Nat.card (G ⧸ commutator G) := rfl
    _ = Nat.card (G ⧸ (⊥ : Subgroup G)) := by rw [h]
    _ = Nat.card G := Nat.card_congr QuotientGroup.quotientBot.toEquiv

variable {K : Type*} [Field K] [NumberField K]

/-- **The canonical congruence subgroup of modulus `m`**, chosen once so that two different
constructions use the same subgroup and the same adjustment function. -/
noncomputable def congU (m : ℕ) (hm : 0 < m) : Subgroup (Idele K) :=
  (NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm).choose

theorem isCongruenceSubgroup_congU (m : ℕ) (hm : 0 < m) :
    NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m (congU (K := K) m hm) :=
  (NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm).choose_spec.1

theorem congU_eq_congruenceSubgroup (m : ℕ) (hm : 0 < m) :
    congU (K := K) m hm = NK.CFTLib.Arl.congruenceSubgroup K m :=
  SetLike.ext fun x => ((isCongruenceSubgroup_congU (K := K) m hm).1 x).trans Iff.rfl

/-- **The canonical adjustment** of an idèle into the congruence subgroup of modulus `m`. -/
noncomputable def congAdjust (m : ℕ) (hm : 0 < m) :
    ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ congU (K := K) m hm :=
  (NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K m hm).choose_spec.2

section

variable {F : Type*} [Field F] [NumberField F] [Algebra K F] [FiniteDimensional K F]
  [IsGalois K F]

/-- **The idèlic Artin map attached to a congruence subgroup.** -/
theorem exists_artData_core (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (hcomm : ∀ a b : Gal(F/K), a * b = b * a) (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 F) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K F m)
    (U : Subgroup (Idele K)) (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : Idele K, ∃ b : Kˣ, x * Idele.principalIdele K b ∈ U) :
    ∃ art : Idele K →* Gal(F/K),
      (∀ x : Idele K, art x = NK.CFTLib.Arl.ideleArtin hcomm U hadj x) ∧
      art.ker = Idele.principalSubgroup K ⊔ Idele.normImage K F ∧
      Function.Surjective art ∧
      (∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ 𝔭.asIdeal →
        art (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime 𝔭) := by
  classical
  haveI : IsMulCommutative Gal(F/K) := IsMulCommutative.of_comm hcomm
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup K m :=
    SetLike.ext fun x => (hU.1 x).trans Iff.rfl
  obtain ⟨art, hAgree, hprin, hfrob, hsurj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin hcomm m hm hram hprinc U hU hadj
  have hadjN : ∀ y : Idele F, ∃ d : Fˣ,
      Idele.normIdeleHom K F (y * Idele.principalIdele F d) ∈ U := by
    intro y
    obtain ⟨d, hd⟩ := NK.CFTLib.Arl.exists_norm_mul_mem_congruenceSubgroup K F m hm y
    exact ⟨d, hUeq ▸ hd⟩
  have hnorm : ∀ y : Idele F, art (Idele.normIdeleHom K F y) = 1 := by
    intro y
    rw [hAgree (Idele.normIdeleHom K F y)]
    exact NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin hcomm m hm hram hprinc U hU hadj hadjN y
  have hnormImage : Idele.normImage K F ≤ art.ker := by
    intro y hy
    obtain ⟨y₀, hy₀⟩ := Idele.mem_normImage.mp hy
    have hyeq : y = Idele.normIdeleHom K F y₀ := by ext v; rw [hy₀ v]; rfl
    rw [hyeq]
    exact MonoidHom.mem_ker.mpr (hnorm y₀)
  have hprin' : Idele.principalSubgroup K ≤ art.ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := Idele.mem_principalSubgroup.mp hx
    exact MonoidHom.mem_ker.mpr (hprin a)
  have hle : Idele.principalSubgroup K ⊔ Idele.normImage K F ≤ art.ker := sup_le hprin' hnormImage
  have hcard1 : Nat.card (Idele K ⧸ art.ker) = Nat.card (Gal(F/K)) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange art).toEquiv]
    rw [MonoidHom.range_eq_top.mpr hsurj]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  have hcard3 : Nat.card (IdeleClassGroup K ⧸ Idele.normClassSubgroup K F) = Nat.card (Gal(F/K)) := by
    rw [← Subgroup.index_eq_card, NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement hFC]
    exact natCard_abelianization_of_comm
  have hcard2 : Nat.card (Idele K ⧸ (Idele.principalSubgroup K ⊔ Idele.normImage K F)) =
      Nat.card (IdeleClassGroup K ⧸ Idele.normClassSubgroup K F) := by
    haveI : (Idele.principalSubgroup K).Normal := Subgroup.normal_of_isMulCommutative _
    haveI : (Idele.principalSubgroup K ⊔ Idele.normImage K F).Normal :=
      Subgroup.normal_of_isMulCommutative _
    have h1 := Nat.card_congr (QuotientGroup.quotientQuotientEquivQuotient
      (N := Idele.principalSubgroup K) (M := Idele.principalSubgroup K ⊔ Idele.normImage K F)
      le_sup_left).toEquiv
    rw [← h1]
    congr 1
    rw [Subgroup.map_sup,
      show Subgroup.map (QuotientGroup.mk' (Idele.principalSubgroup K)) (Idele.principalSubgroup K)
        = ⊥ from (Subgroup.map_eq_bot_iff _).mpr (le_of_eq (QuotientGroup.ker_mk' _).symm),
      bot_sup_eq]
    rfl
  have hcard : Nat.card (Idele K ⧸ art.ker) =
      Nat.card (Idele K ⧸ (Idele.principalSubgroup K ⊔ Idele.normImage K F)) := by
    rw [hcard1, ← hcard3, hcard2]
  have hker : art.ker = Idele.principalSubgroup K ⊔ Idele.normImage K F := by
    have hne : (art.ker).index ≠ 0 := by
      rw [Subgroup.index_eq_card, hcard1]
      exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    have hidx : (Idele.principalSubgroup K ⊔ Idele.normImage K F).index = (art.ker).index := by
      rw [Subgroup.index_eq_card, Subgroup.index_eq_card, hcard]
    have h1 : (Idele.principalSubgroup K ⊔ Idele.normImage K F).relIndex art.ker = 1 := by
      have hmul := Subgroup.relIndex_mul_index hle
      rw [hidx] at hmul
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (by rw [one_mul]; exact hmul)
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle
  exact ⟨art, hAgree, hker, hsurj, hfrob⟩

end



/-- The conjugation action of `e : X ≃ₐ[K] Y` as a multiplicative equivalence. -/
noncomputable def algEquivConjMulEquiv {K X Y : Type*} [Field K] [Field X] [Field Y] [Algebra K X]
    [Algebra K Y] (e : X ≃ₐ[K] Y) : (X ≃ₐ[K] X) ≃* (Y ≃ₐ[K] Y) where
  toFun := NK.Reconstruct.algEquivConjHom e
  invFun := NK.Reconstruct.algEquivConjHom e.symm
  left_inv σ := by
    ext x
    simp [NK.Reconstruct.algEquivConjHom, AlgEquiv.trans_apply]
  right_inv τ := by
    ext x
    simp [NK.Reconstruct.algEquivConjHom, AlgEquiv.trans_apply]
  map_mul' σ τ := map_mul (NK.Reconstruct.algEquivConjHom e) σ τ

/-- Commutativity of automorphism groups transports along a `K`-algebra isomorphism. -/
theorem isMulCommutative_of_algEquiv' {K X Y : Type*} [Field K] [Field X] [Field Y] [Algebra K X]
    [Algebra K Y] (e : X ≃ₐ[K] Y) (h : IsMulCommutative (Y ≃ₐ[K] Y)) :
    IsMulCommutative (X ≃ₐ[K] X) := by
  haveI := h
  refine IsMulCommutative.of_comm (M := X ≃ₐ[K] X) fun a b => ?_
  exact (algEquivConjMulEquiv e).injective (by
    rw [map_mul, map_mul]
    exact IsMulCommutative.is_comm.comm _ _)

/-- The idèlic Artin map at a modulus, with the canonical congruence subgroup. -/
theorem exists_artData {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
    (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (hcomm : ∀ a b : Gal(F/K), a * b = b * a) (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 F) = 1)
    (hprinc : NK.CFTLib.artinKillsPrincipal K F m) :
    ∃ art : Idele K →* Gal(F/K),
      (∀ x : Idele K, art x = NK.CFTLib.Arl.ideleArtin hcomm (congU (K := K) m hm)
        (congAdjust (K := K) m hm) x) ∧
      art.ker = Idele.principalSubgroup K ⊔ Idele.normImage K F ∧
      Function.Surjective art ∧
      (∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ 𝔭.asIdeal →
        art (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime 𝔭) :=
  exists_artData_core hFC hcomm m hm hram hprinc (congU (K := K) m hm)
    (isCongruenceSubgroup_congU (K := K) m hm) (congAdjust (K := K) m hm)

theorem artinSym_restrictNormalHom {K A : Type} [Field K] [NumberField K] [Field A]
    [NumberField A] [Algebra K A] [FiniteDimensional K A] [IsGalois K A]
    (B : IntermediateField K A) [FiniteDimensional K ↥B] [NumberField ↥B] [Normal K ↥B]
    (hcommA : ∀ a b : Gal(A/K), a * b = b * a)
    (hcommB : ∀ a b : Gal(↥B/K), a * b = b * a)
    (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (hunr : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      NK.CFTLib.Arl.exps 𝔞 𝔭 ≠ 0 → Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 A) = 1) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := A) B
        (NK.CFTLib.Arl.artinSym hcommA 𝔞)
      = NK.CFTLib.Arl.artinSym hcommB 𝔞 := by
  classical
  haveI : IsMulCommutative Gal(A/K) := IsMulCommutative.of_comm hcommA
  haveI : IsMulCommutative Gal(↥B/K) := IsMulCommutative.of_comm hcommB
  letI galA : CommMonoid Gal(A/K) := NK.CFTLib.Arl.galCommMonoid hcommA
  letI galB : CommMonoid Gal(↥B/K) := NK.CFTLib.Arl.galCommMonoid hcommB
  have hA : NK.CFTLib.Arl.artinSym hcommA 𝔞
      = (NK.CFTLib.Arl.exps 𝔞).prod (fun 𝔭 (e : ℤ) =>
          (NK.Chebotarev.frobAtPrime (K := K) (L := A) 𝔭) ^ e) := rfl
  have hB : NK.CFTLib.Arl.artinSym hcommB 𝔞
      = (NK.CFTLib.Arl.exps 𝔞).prod (fun 𝔭 (e : ℤ) =>
          (NK.Chebotarev.frobAtPrime (K := K) (L := ↥B) 𝔭) ^ e) := rfl
  have hterm : ∀ 𝔭 ∈ (NK.CFTLib.Arl.exps 𝔞).support,
      AlgEquiv.restrictNormalHom (F := K) (K₁ := A) B
        (NK.Chebotarev.frobAtPrime (K := K) (L := A) 𝔭)
      = NK.Chebotarev.frobAtPrime (K := K) (L := ↥B) 𝔭 := by
    intro 𝔭 h𝔭
    exact NK.NUV2.RouteB.LangX.frobAtPrime_restrictNormalHom B 𝔭
      (hunr 𝔭 (Finsupp.mem_support_iff.mp h𝔭))
  rw [hA, hB]
  rw [Finsupp.prod_of_support_subset (NK.CFTLib.Arl.exps 𝔞) (le_refl _)
      (fun 𝔭 (e : ℤ) => (NK.Chebotarev.frobAtPrime (K := K) (L := A) 𝔭) ^ e)
      (fun i _ => zpow_zero _)]
  rw [Finsupp.prod_of_support_subset (NK.CFTLib.Arl.exps 𝔞) (le_refl _)
      (fun 𝔭 (e : ℤ) => (NK.Chebotarev.frobAtPrime (K := K) (L := ↥B) 𝔭) ^ e)
      (fun i _ => zpow_zero _)]
  rw [map_prod]
  exact Finset.prod_congr rfl fun 𝔭 h𝔭 => by rw [map_zpow, hterm 𝔭 h𝔭]


/-- Unramifiedness descends to an intermediate field. -/
theorem ramificationIdxIn_eq_one_of_intermediateField {K A : Type} [Field K] [NumberField K]
    [Field A] [NumberField A] [Algebra K A] [FiniteDimensional K A] [IsGalois K A]
    (B : IntermediateField K A) [FiniteDimensional K ↥B] [NumberField ↥B] [Normal K ↥B]
    (p : NK.Chebotarev.PrimeIdeal K)
    (h : Ideal.ramificationIdxIn p.asIdeal (𝓞 A) = 1) :
    Ideal.ramificationIdxIn p.asIdeal (𝓞 ↥B) = 1 :=
  NK.NUV2.ARL.ramificationIdxIn_eq_one_of_intermediateField (M := B) p h

/-- **The product condition of the reciprocity law descends to an intermediate field.** -/
theorem artinKillsPrincipal_of_intermediateField {K A : Type} [Field K] [NumberField K]
    [Field A] [NumberField A] [Algebra K A] [FiniteDimensional K A] [IsGalois K A]
    (hcommA : ∀ a b : Gal(A/K), a * b = b * a)
    (B : IntermediateField K A) [FiniteDimensional K ↥B] [NumberField ↥B] [Normal K ↥B]
    (hcommB : ∀ a b : Gal(↥B/K), a * b = b * a)
    {m : ℕ}
    (hramA : ∀ p : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 A) = 1)
    (hprincA : NK.CFTLib.artinKillsPrincipal K A m) :
    NK.CFTLib.artinKillsPrincipal K ↥B m := by
  classical
  intro a ha hpos s e σ hs hfac hfrob
  choose τ hτ using fun p : NK.Chebotarev.PrimeIdeal K =>
    NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := A) p
  have hσeq : ∀ p ∈ s, σ p = AlgEquiv.restrictNormalHom (F := K) (K₁ := A) B (τ p) := by
    intro p hp
    have hunrB : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥B) p :=
      NK.NUV2.RouteB.LangX.isUnramified_of_ramificationIdxIn_eq_one p
        (ramificationIdxIn_eq_one_of_intermediateField B p (hramA p (hs p hp)))
    have h1 : NK.Chebotarev.frobAtPrime (K := K) (L := ↥B) p
        = AlgEquiv.restrictNormalHom (F := K) (K₁ := A) B (τ p) :=
      (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommB p hunrB _).mp
        (NK.CFTLib.exists_isFrobAtPrime_restrict B (hτ p))
    have h2 : NK.Chebotarev.frobAtPrime (K := K) (L := ↥B) p = σ p :=
      (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommB p hunrB _).mp (hfrob p hp)
    rw [← h1, h2]
  have h1 : s.toList.map (fun p => σ p ^ e p)
      = s.toList.map (fun p => (AlgEquiv.restrictNormalHom (F := K) (K₁ := A) B (τ p)) ^ e p) :=
    List.map_congr_left (fun p hp => by rw [hσeq p (Finset.mem_toList.mp hp)])
  have h2 : (s.toList.map (fun p => τ p ^ e p)).map
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := A) B)
      = s.toList.map (fun p => (AlgEquiv.restrictNormalHom (F := K) (K₁ := A) B (τ p)) ^ e p) := by
    rw [List.map_map]
    exact List.map_congr_left fun p _ => by
      simp only [Function.comp_apply]
      exact map_zpow (AlgEquiv.restrictNormalHom (F := K) (K₁ := A) B) (τ p) (e p)
  have hmap : (s.toList.map (fun p => σ p ^ e p)).prod
      = AlgEquiv.restrictNormalHom (F := K) (K₁ := A) B
          ((s.toList.map (fun p => τ p ^ e p)).prod) := by
    rw [MonoidHom.map_list_prod, h2, ← h1]
  rw [hmap, hprincA a ha hpos s e τ hs hfac (fun p _ => hτ p), map_one]


/-- **The idèlic Artin map is compatible with restriction to a subfield**, both maps being built
from the same modulus and the same congruence subgroup. -/
theorem ideleArtin_restrictNormalHom {K A : Type} [Field K] [NumberField K] [Field A]
    [NumberField A] [Algebra K A] [FiniteDimensional K A] [IsGalois K A]
    (B : IntermediateField K A) [FiniteDimensional K ↥B] [NumberField ↥B] [Normal K ↥B]
    (hcommA : ∀ a b : Gal(A/K), a * b = b * a)
    (hcommB : ∀ a b : Gal(↥B/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hramA : ∀ p : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 A) = 1)
    (x : Idele K) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := A) B
        (NK.CFTLib.Arl.ideleArtin hcommA (congU (K := K) m hm) (congAdjust (K := K) m hm) x)
      = NK.CFTLib.Arl.ideleArtin hcommB (congU (K := K) m hm) (congAdjust (K := K) m hm) x := by
  have hy : x * Idele.principalIdele K
      (NK.CFTLib.Arl.adjust (congU (K := K) m hm) (congAdjust (K := K) m hm) x)
      ∈ congU (K := K) m hm :=
    NK.CFTLib.Arl.adjust_spec _ _ x
  have hUc := isCongruenceSubgroup_congU (K := K) m hm
  have hunr : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      NK.CFTLib.Arl.exps (Idele.idealOf (x * Idele.principalIdele K
        (NK.CFTLib.Arl.adjust (congU (K := K) m hm) (congAdjust (K := K) m hm) x))) 𝔭 ≠ 0 →
      Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 A) = 1 := by
    intro 𝔭 h𝔭
    refine hramA 𝔭 (fun hcon => h𝔭 ?_)
    rw [NK.CFTLib.Arl.exps_apply, Idele.count_idealOf]
    exact NK.CFTLib.Arl.exp_eq_zero_of_mem_congruence m _ hUc _ hy 𝔭 hcon
  exact artinSym_restrictNormalHom B hcommA hcommB _ hunr

/-- **Uniqueness of the idèlic Artin map**: two homomorphisms with the same kernel and the same
Frobenius normalisation outside a set of unramified primes agree. -/
theorem artData_unique {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F]
    [Algebra K F] [FiniteDimensional K F] [IsGalois K F]
    (hcomm : ∀ a b : Gal(F/K), a * b = b * a)
    (T : Finset (NK.Chebotarev.PrimeIdeal K))
    (hT : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, 𝔭 ∉ T →
      NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := F) 𝔭)
    {art art' : Idele K →* Gal(F/K)}
    (hker : art.ker = Idele.principalSubgroup K ⊔ Idele.normImage K F)
    (hker' : art'.ker = Idele.principalSubgroup K ⊔ Idele.normImage K F)
    (hfrob : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, 𝔭 ∉ T →
      art (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime 𝔭)
    (hfrob' : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, 𝔭 ∉ T →
      art' (NK.HeckeL.ideleOfPrime K 𝔭) = NK.Chebotarev.frobAtPrime 𝔭) :
    art = art' := by
  classical
  haveI : IsMulCommutative Gal(F/K) := IsMulCommutative.of_comm hcomm
  haveI hN : (Idele.normImage K F).Normal := Subgroup.normal_of_isMulCommutative _
  haveI hPN : (Idele.principalSubgroup K ⊔ Idele.normImage K F).Normal :=
    Subgroup.normal_of_isMulCommutative _
  let Φ : Idele K ⧸ (Idele.principalSubgroup K ⊔ Idele.normImage K F) →* Gal(F/K) :=
    QuotientGroup.lift (Idele.principalSubgroup K ⊔ Idele.normImage K F) art (le_of_eq hker.symm)
  let Φ' : Idele K ⧸ (Idele.principalSubgroup K ⊔ Idele.normImage K F) →* Gal(F/K) :=
    QuotientGroup.lift (Idele.principalSubgroup K ⊔ Idele.normImage K F) art' (le_of_eq hker'.symm)
  have hΦ : ∀ x : Idele K,
      Φ (QuotientGroup.mk' (Idele.principalSubgroup K ⊔ Idele.normImage K F) x) = art x :=
    fun x => QuotientGroup.lift_mk' _ _ x
  have hΦ' : ∀ x : Idele K,
      Φ' (QuotientGroup.mk' (Idele.principalSubgroup K ⊔ Idele.normImage K F) x) = art' x :=
    fun x => QuotientGroup.lift_mk' _ _ x
  have hinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, hker]
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientGroup.ker_mk' _).symm
  set S : Set (Idele K ⧸ (Idele.principalSubgroup K ⊔ Idele.normImage K F)) :=
    {y | ∃ 𝔭 : NK.Chebotarev.PrimeIdeal K, 𝔭 ∉ T ∧
      y = QuotientGroup.mk' (Idele.principalSubgroup K ⊔ Idele.normImage K F)
        (NK.HeckeL.ideleOfPrime K 𝔭)} with hS
  have himg : Φ '' S = {σ : Gal(F/K) | ∃ 𝔭 : NK.Chebotarev.PrimeIdeal K, 𝔭 ∉ T ∧
      NK.Chebotarev.IsFrobAtPrime (K := K) (L := F) 𝔭 σ} := by
    ext σ
    constructor
    · rintro ⟨y, ⟨𝔭, h𝔭, rfl⟩, rfl⟩
      exact ⟨𝔭, h𝔭, (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm 𝔭 (hT 𝔭 h𝔭) _).mpr
        (hfrob 𝔭 h𝔭).symm⟩
    · rintro ⟨𝔭, h𝔭, hσ⟩
      exact ⟨_, ⟨𝔭, h𝔭, rfl⟩, by
        rw [hΦ, hfrob 𝔭 h𝔭]
        exact (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcomm 𝔭 (hT 𝔭 h𝔭) _).mp hσ⟩
  have hcl : Subgroup.closure S = ⊤ := by
    have hmap : Subgroup.map Φ (Subgroup.closure S) = ⊤ := by
      rw [MonoidHom.map_closure, himg,
        NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem T]
    rw [eq_top_iff]
    intro y _
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (show Φ y ∈ Subgroup.map Φ (Subgroup.closure S)
      from by rw [hmap]; trivial)
    exact (hinj hzy) ▸ hz
  have heq : Φ = Φ' := by
    refine MonoidHom.ext fun y => ?_
    let D : Subgroup (Idele K ⧸ (Idele.principalSubgroup K ⊔ Idele.normImage K F)) :=
      { carrier := {y | Φ y = Φ' y}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [map_mul, map_mul, ha, hb]
        one_mem' := by
          simp only [Set.mem_setOf_eq]
          rw [map_one, map_one]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          rw [map_inv, map_inv, ha] }
    have hSD : S ⊆ D := by
      rintro y ⟨𝔭, h𝔭, rfl⟩
      change Φ (QuotientGroup.mk' (Idele.principalSubgroup K ⊔ Idele.normImage K F)
          (NK.HeckeL.ideleOfPrime K 𝔭))
        = Φ' (QuotientGroup.mk' (Idele.principalSubgroup K ⊔ Idele.normImage K F)
          (NK.HeckeL.ideleOfPrime K 𝔭))
      rw [hΦ, hΦ', hfrob 𝔭 h𝔭, hfrob' 𝔭 h𝔭]
    exact (Subgroup.closure_le D).mpr hSD (by rw [hcl]; trivial)
  refine MonoidHom.ext fun x => ?_
  rw [← hΦ x, ← hΦ' x, heq]




/-- Membership in `restrictLevelTo`. -/
theorem mem_restrictLevelTo {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    {E M : IntermediateField K K'} (h : E ≤ M)
    (x : ↥(NK.Reconstruct.restrictLevelTo E M h)) : ((x : ↥M) : K') ∈ E :=
  Subfield.mem_comap.mp x.2

/-- The converse membership in `restrictLevelTo`. -/
theorem mem_restrictLevelTo_of_mem {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    {E M : IntermediateField K K'} (h : E ≤ M) (x : ↥M) (hx : (x : K') ∈ E) :
    x ∈ NK.Reconstruct.restrictLevelTo E M h := hx

/-- The identity of `↥(restrictLevelTo E M h)` with `↥E`. -/
noncomputable def restrictLevelToEquiv {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    (E M : IntermediateField K K') (h : E ≤ M) :
    ↥(NK.Reconstruct.restrictLevelTo E M h) ≃ₐ[K] ↥E where
  toFun x := ⟨(x : ↥M), mem_restrictLevelTo h x⟩
  invFun y := ⟨⟨y, h y.2⟩, by
    show ((⟨y, h y.2⟩ : ↥M) : K') ∈ E
    exact y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_mul' x y := by ext; rfl
  map_add' x y := by ext; rfl
  commutes' c := by ext; rfl

/-- The norm class subgroup is invariant under `K`-algebra isomorphisms. -/
theorem normClassSubgroup_eq_of_algEquiv {K F F' : Type*} [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F] [FiniteDimensional K F]
    [Field F'] [NumberField F'] [Algebra K F'] [FiniteDimensional K F'] (e : F ≃ₐ[K] F') :
    NK.GlobalCFT.Idele.normClassSubgroup K F = NK.GlobalCFT.Idele.normClassSubgroup K F' := by
  have h1 := NK.GlobalCFTdeep.Transport.normClassSubgroup_map_ideleClassEquiv
    (K := K) (L := F) (K' := K) (L' := F) (RingEquiv.refl K) (RingEquiv.refl F)
    (fun x => rfl)
  have h2 := NK.GlobalCFTdeep.Transport.normClassSubgroup_map_ideleClassEquiv
    (K := K) (L := F) (K' := K) (L' := F') (RingEquiv.refl K) e.toRingEquiv
    (fun x => e.commutes x)
  rw [h2] at h1
  exact h1.symm


/-- The cardinality of the image of a subgroup in a quotient is its relative index. -/
theorem natCard_map_mk'_eq_relIndex {G : Type*} [Group G] (H K : Subgroup G) [H.Normal]
    (h : H ≤ K) :
    Nat.card ↥(Subgroup.map (QuotientGroup.mk' H) K) = H.relIndex K := by
  have hker : ((QuotientGroup.mk' H).comp K.subtype).ker = H.subgroupOf K := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Iff.rfl
  have hrange : ((QuotientGroup.mk' H).comp K.subtype).range
      = Subgroup.map (QuotientGroup.mk' H) K := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hq : Nat.card (↥K ⧸ ((QuotientGroup.mk' H).comp K.subtype).ker)
      = Nat.card ↥(((QuotientGroup.mk' H).comp K.subtype).range) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
  rw [← hrange, ← hq, hker, ← Subgroup.index_eq_card]
  rfl

section GaloisCorr

open NK.Reconstruct

variable {K : Type} [Field K] [NumberField K] {K' : Type} [Field K'] [Algebra K K']

/-- The conjugation homomorphism is injective. -/
theorem algEquivConjHom_ker {K X Y : Type*} [Field K] [Field X] [Field Y] [Algebra K X]
    [Algebra K Y] (e : X ≃ₐ[K] Y) : (NK.Reconstruct.algEquivConjHom e).ker = ⊥ := by
  rw [MonoidHom.ker_eq_bot_iff]
  intro σ τ hστ
  ext x
  have h2 := congrArg (fun φ : Y ≃ₐ[K] Y => φ (e x)) hστ
  simpa [NK.Reconstruct.algEquivConjHom, AlgEquiv.trans_apply] using h2

/-- The restriction map to a level, as a homomorphism. -/
noncomputable def resLevel {K : Type} [Field K] {K' : Type} [Field K'] [Algebra K K']
    (L M : NK.Reconstruct.FrobLevel K K') (h : L.L ≤ M.L)
    [Normal K ↥(NK.Reconstruct.levelTo L M h)] :
    Gal(↥M.L/K) →* Gal(↥(NK.Reconstruct.levelTo L M h)/K) :=
  AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M.L) ↥(NK.Reconstruct.levelTo L M h)

/-- **The kernel of the level restriction is the fixing subgroup.** -/
theorem levelRestrictHom_ker {K : Type} [Field K] [NumberField K] {K' : Type} [Field K']
    [Algebra K K'] [IsGalois K K'] (L M : NK.Reconstruct.FrobLevel K K') (h : L.L ≤ M.L) :
    (NK.Reconstruct.levelRestrictHom L M h).ker
      = (NK.Reconstruct.levelTo L M h).fixingSubgroup := by
  haveI hnl : Normal K ↥(NK.Reconstruct.levelTo L M h) := NK.Reconstruct.normal_levelTo L M h
  have hker : (NK.Reconstruct.levelRestrictHom L M h).ker = (resLevel L M h).ker :=
    MonoidHom.ker_comp_of_injective (resLevel L M h)
      (NK.Reconstruct.algEquivConjHom (NK.Reconstruct.levelToEquiv L M h))
      (algEquivConjMulEquiv _).injective
  rw [hker]
  exact IntermediateField.restrictNormalHom_ker _

/-- The level restriction homomorphism is surjective. -/
theorem levelRestrictHom_surjective {K : Type} [Field K] [NumberField K] {K' : Type} [Field K']
    [Algebra K K'] [IsGalois K K'] (L M : NK.Reconstruct.FrobLevel K K') (h : L.L ≤ M.L) :
    Function.Surjective (NK.Reconstruct.levelRestrictHom L M h) := by
  haveI hnl : Normal K ↥(NK.Reconstruct.levelTo L M h) := NK.Reconstruct.normal_levelTo L M h
  have h1 : Function.Surjective (resLevel L M h) :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥(NK.Reconstruct.levelTo L M h)) ↥M.L
  have h2 : Function.Surjective ⇑(NK.Reconstruct.algEquivConjHom
      (NK.Reconstruct.levelToEquiv L M h)) := (algEquivConjMulEquiv _).surjective
  exact h2.comp h1

/-- The commutator of the restriction map. -/
theorem map_levelRestrictHom_commutator {K : Type} [Field K] [NumberField K] {K' : Type}
    [Field K'] [Algebra K K'] [IsGalois K K'] (L M : NK.Reconstruct.FrobLevel K K')
    (h : L.L ≤ M.L) :
    Subgroup.map (NK.Reconstruct.levelRestrictHom L M h) (commutator Gal(↥M.L/K))
      = commutator Gal(↥L.L/K) := by
  change Subgroup.map (NK.Reconstruct.levelRestrictHom L M h)
      ⁅(⊤ : Subgroup Gal(↥M.L/K)), (⊤ : Subgroup Gal(↥M.L/K))⁆
    = ⁅(⊤ : Subgroup Gal(↥L.L/K)), (⊤ : Subgroup Gal(↥L.L/K))⁆
  rw [Subgroup.map_commutator,
    Subgroup.map_top_of_surjective (NK.Reconstruct.levelRestrictHom L M h)
      (levelRestrictHom_surjective L M h)]

/-- The preimage of the commutator subgroup is the fixing subgroup joined with the commutator. -/
theorem comap_levelRestrictHom_commutator {K : Type} [Field K] [NumberField K] {K' : Type}
    [Field K'] [Algebra K K'] [IsGalois K K'] (L M : NK.Reconstruct.FrobLevel K K')
    (h : L.L ≤ M.L) :
    Subgroup.comap (NK.Reconstruct.levelRestrictHom L M h) (commutator Gal(↥L.L/K))
      = (NK.Reconstruct.levelTo L M h).fixingSubgroup
        ⊔ commutator Gal(↥M.L/K) := by
  rw [← map_levelRestrictHom_commutator L M h, Subgroup.comap_map_eq, levelRestrictHom_ker]
  exact sup_comm _ _

/-- The image of the fixing subgroup joined with the commutator is the commutator. -/
theorem map_levelRestrictHom_sup_commutator {K : Type} [Field K] [NumberField K] {K' : Type}
    [Field K'] [Algebra K K'] [IsGalois K K'] (L M : NK.Reconstruct.FrobLevel K K')
    (h : L.L ≤ M.L) :
    Subgroup.map (NK.Reconstruct.levelRestrictHom L M h)
        ((NK.Reconstruct.levelTo L M h).fixingSubgroup ⊔ commutator Gal(↥M.L/K))
      = commutator Gal(↥L.L/K) := by
  rw [Subgroup.map_sup, map_levelRestrictHom_commutator L M h,
    show Subgroup.map (NK.Reconstruct.levelRestrictHom L M h)
        (NK.Reconstruct.levelTo L M h).fixingSubgroup = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (le_of_eq (levelRestrictHom_ker L M h).symm),
    bot_sup_eq]

/-- **The kernel of the abelianised level restriction.** -/
theorem levelRestrict_ker {K : Type} [Field K] [NumberField K] {K' : Type} [Field K']
    [Algebra K K'] [IsGalois K K'] (L M : NK.Reconstruct.FrobLevel K K') (h : L.L ≤ M.L) :
    (NK.Reconstruct.levelRestrict L M h).ker
      = Subgroup.map Abelianization.of ((NK.Reconstruct.levelTo L M h).fixingSubgroup
          ⊔ commutator Gal(↥M.L/K)) := by
  apply le_antisymm
  · rintro y hy
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective (commutator Gal(↥M.L/K)) y
    have h1 : NK.Reconstruct.levelRestrict L M h (Abelianization.of σ) = 1 := hy
    rw [NK.Reconstruct.levelRestrict, Abelianization.map_of] at h1
    have h2 : NK.Reconstruct.levelRestrictHom L M h σ ∈ Abelianization.of.ker :=
      MonoidHom.mem_ker.mpr h1
    rw [Abelianization.ker_of] at h2
    have h2' : σ ∈ Subgroup.comap (NK.Reconstruct.levelRestrictHom L M h)
        (commutator Gal(↥L.L/K)) :=
      Subgroup.mem_comap.mpr h2
    rw [comap_levelRestrictHom_commutator L M h] at h2'
    exact Subgroup.mem_map_of_mem _ h2'
  · rintro y ⟨σ, hσ, rfl⟩
    rw [MonoidHom.mem_ker, NK.Reconstruct.levelRestrict, Abelianization.map_of]
    exact MonoidHom.mem_ker.mp (by
      rw [Abelianization.ker_of]
      exact map_levelRestrictHom_sup_commutator L M h ▸ Subgroup.mem_map_of_mem _ hσ)

end GaloisCorr

/-- **The main theorem.** -/
theorem levelPairIso_of_artinReciprocityIdeal (h : NK.CFTLib.ArtinReciprocityIdeal)
    (K : Type) [Field K] [NumberField K]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosure K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] :
    NK.NUV2.ArtinBridge.LevelPairIso K Ω ℓ := by
  classical
  have hFC : NK.GlobalCFTdeep.FundamentalClassElement := NK.CFTLib.fcElement_of_arl h
  intro M hM
  haveI : IsGalois K ↥M.L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hCn : (⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆).Normal :=
    Subgroup.commutator_normal (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)) (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))
  let A : IntermediateField K ↥M.L :=
    IntermediateField.fixedField ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆
  haveI hAgal : IsGalois K ↥A := IsGalois.of_fixedField_normal_subgroup _
  haveI hAcomm : IsMulCommutative (↥A ≃ₐ[K] ↥A) := by
    haveI hq : IsMulCommutative ((↥M.L ≃ₐ[K] ↥M.L) ⧸
        ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆) :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N :=
        ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆)).mpr le_rfl
    refine IsMulCommutative.of_comm (M := ↥A ≃ₐ[K] ↥A) fun a b => ?_
    exact (IsGalois.normalAutEquivQuotient
      (⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆)).symm.injective
      (by rw [map_mul, map_mul]; exact hq.is_comm.comm _ _)
  have hcommA : ∀ a b : Gal(↥A/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  -- the reciprocity law at the abelian level `A` and the idèlic Artin map of `A`
  obtain ⟨m, hm, hramA, hprincA⟩ := h K ↥A hcommA
  obtain ⟨artA, hartA, hkerA, hsurjA, hfrobA⟩ :=
    exists_artData (K := K) (F := ↥A) hFC hcommA m hm hramA hprincA
  -- the norm class subgroup of `A` is that of `M`
  have hNA : Idele.normClassSubgroup K ↥M.L = Idele.normClassSubgroup K ↥A :=
    (NK.NUV2.TowerRank.normClassSubgroup_fixedField_commutator hFC (K := K) (F := ↥M.L)).symm
  -- the isomorphism `Gal(M/K)^ab ≅ Gal(A/K)`
  let Φe : Abelianization (↥M.L ≃ₐ[K] ↥M.L) ≃* Gal(↥A/K) :=
    IsGalois.normalAutEquivQuotient
      ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆
  have hΦe : ∀ σ : ↥M.L ≃ₐ[K] ↥M.L, Φe (Abelianization.of σ)
      = AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M.L) ↥A σ :=
    fun σ => IsGalois.normalAutEquivQuotient_apply _ σ
  let φA : Gal(↥M.L/K) →* Gal(↥A/K) := AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥M.L) ↥A
  have hφAsurj : Function.Surjective φA :=
    AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥A) ↥M.L
  -- the map `C_K →* Gal(A/K)`
  haveI hNnormal : (Idele.normClassSubgroup K ↥M.L).Normal := Subgroup.normal_of_isMulCommutative _
  have hprin_le : Idele.principalSubgroup K ≤ artA.ker := by
    rw [hkerA]; exact le_sup_left
  let fA : IdeleClassGroup K →* Gal(↥A/K) :=
    QuotientGroup.lift (Idele.principalSubgroup K) artA hprin_le
  have hfA : ∀ x : Idele K, fA (IdeleClassGroup.mk K x) = artA x :=
    fun x => QuotientGroup.lift_mk' _ _ x
  have hkill : Idele.normClassSubgroup K ↥M.L ≤ fA.ker := by
    intro x hx
    rw [hNA, show Idele.normClassSubgroup K ↥A = (Idele.normImage K ↥A).map (IdeleClassGroup.mk K)
      from rfl] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [MonoidHom.mem_ker, hfA, ← MonoidHom.mem_ker, hkerA]
    exact Subgroup.mem_sup_right hy
  let eM : IdeleClassGroup K ⧸ Idele.normClassSubgroup K ↥M.L →*
      Abelianization (↥M.L ≃ₐ[K] ↥M.L) :=
    Φe.symm.toMonoidHom.comp (QuotientGroup.lift (Idele.normClassSubgroup K ↥M.L) fA hkill)
  have heM : ∀ x : Idele K, eM (QuotientGroup.mk' (Idele.normClassSubgroup K ↥M.L)
      (IdeleClassGroup.mk K x)) = Φe.symm (artA x) := by
    intro x
    exact congrArg Φe.symm ((QuotientGroup.lift_mk' (Idele.normClassSubgroup K ↥M.L) hkill
      (IdeleClassGroup.mk K x)).trans (hfA x))
  have hsurjE : Function.Surjective eM := by
    intro y
    obtain ⟨x, hx⟩ := hsurjA (Φe y)
    exact ⟨QuotientGroup.mk' (Idele.normClassSubgroup K ↥M.L) (IdeleClassGroup.mk K x), by
      rw [heM, hx, Φe.symm_apply_apply]⟩
  have hcardE : Nat.card (IdeleClassGroup K ⧸ Idele.normClassSubgroup K ↥M.L) =
      Nat.card (Abelianization (↥M.L ≃ₐ[K] ↥M.L)) := by
    rw [← Subgroup.index_eq_card,
      NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement hFC]
  haveI hfinM : (Idele.normClassSubgroup K ↥M.L).FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero (K := K) (L := ↥M.L))
  haveI : Finite (IdeleClassGroup K ⧸ Idele.normClassSubgroup K ↥M.L) := inferInstance
  haveI : Fintype (IdeleClassGroup K ⧸ Idele.normClassSubgroup K ↥M.L) := Fintype.ofFinite _
  haveI : Fintype (Abelianization (↥M.L ≃ₐ[K] ↥M.L)) := Fintype.ofFinite _
  have hbijE : Function.Bijective eM := by
    refine (Fintype.bijective_iff_surjective_and_card eM).mpr ⟨hsurjE, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcardE
  refine ⟨MulEquiv.ofBijective eM hbijE, ?_⟩
  intro L hL hLM
  -- ===== the sublevel, viewed inside `M` =====
  let EL : IntermediateField K ↥M.L := NK.Reconstruct.levelTo L M hLM
  haveI hELnor : Normal K ↥EL := NK.Reconstruct.normal_levelTo L M hLM
  haveI hELfd : FiniteDimensional K ↥EL := IntermediateField.finiteDimensional_left EL
  haveI hELnf : NumberField ↥EL := Commons.NumberTheory.NumberField.numberField_of_intermediateField EL
  haveI hELgal : IsGalois K ↥EL := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- ===== the maximal abelian subextension of `EL` =====
  let B : IntermediateField K ↥M.L := IntermediateField.fixedField
    (EL.fixingSubgroup ⊔ ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆)
  haveI hBJnor : (EL.fixingSubgroup ⊔
      ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆).Normal :=
    Subgroup.sup_normal _ _
  haveI hBgal : IsGalois K ↥B := IsGalois.of_fixedField_normal_subgroup _
  haveI hBfd : FiniteDimensional K ↥B := IntermediateField.finiteDimensional_left B
  haveI hBnf : NumberField ↥B := Commons.NumberTheory.NumberField.numberField_of_intermediateField B
  have hBcomm : IsMulCommutative (↥B ≃ₐ[K] ↥B) := by
    haveI hq : IsMulCommutative ((↥M.L ≃ₐ[K] ↥M.L) ⧸
        (EL.fixingSubgroup ⊔ ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆)) :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := (EL.fixingSubgroup ⊔
        ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆))).mpr le_sup_right
    refine IsMulCommutative.of_comm (M := ↥B ≃ₐ[K] ↥B) fun a b => ?_
    exact (IsGalois.normalAutEquivQuotient (EL.fixingSubgroup ⊔
      ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆)).symm.injective
      (by rw [map_mul, map_mul]; exact hq.is_comm.comm _ _)
  -- ===== `B` as a subfield of `A` =====
  have hBA : B ≤ A := IntermediateField.fixedField_le (H1 :=
    ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆)
    (H2 := EL.fixingSubgroup ⊔
      ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆) le_sup_right
  let BA : IntermediateField K ↥A := NK.Reconstruct.restrictLevelTo B A hBA
  haveI hBAfd : FiniteDimensional K ↥BA := IntermediateField.finiteDimensional_left BA
  haveI hBAnf : NumberField ↥BA := Commons.NumberTheory.NumberField.numberField_of_intermediateField BA
  haveI hBAnor : Normal K ↥BA := NK.Reconstruct.normal_restrictLevelTo hBA
  haveI hBAgal : IsGalois K ↥BA := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  haveI hBAcomm : IsMulCommutative (↥BA ≃ₐ[K] ↥BA) :=
    isMulCommutative_of_algEquiv' (restrictLevelToEquiv B A hBA) hBcomm
  have hcommB : ∀ a b : Gal(↥BA/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  -- ===== the Artin data at the sublevel =====
  have hramB : ∀ p : NK.Chebotarev.PrimeIdeal K, (m : 𝓞 K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 ↥BA) = 1 :=
    fun p hp => ramificationIdxIn_eq_one_of_intermediateField BA p (hramA p hp)
  have hprincB : NK.CFTLib.artinKillsPrincipal K ↥BA m :=
    artinKillsPrincipal_of_intermediateField hcommA BA hcommB hramA hprincA
  obtain ⟨artB, hartB, hkerB, hsurjB, hfrobB⟩ :=
    exists_artData (K := K) (F := ↥BA) hFC hcommB m hm hramB hprincB
  -- ===== the crux: the Artin maps are compatible =====
  have hcompat : ∀ x : Idele K,
      AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥A) ↥BA (artA x) = artB x := by
    intro x
    rw [hartA x, hartB x]
    exact ideleArtin_restrictNormalHom BA hcommA hcommB m hm hramA x
  have hartB_kill : ∀ y : Idele K, y ∈ Idele.normImage K ↥BA → artB y = 1 := by
    intro y hy
    exact MonoidHom.mem_ker.mp ((hkerB ▸ Subgroup.mem_sup_right hy :
      y ∈ artB.ker))
  have hartA_fixes : ∀ y : Idele K, y ∈ Idele.normImage K ↥BA →
      AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥A) ↥BA (artA y) = 1 := by
    intro y hy
    rw [hcompat y]
    exact hartB_kill y hy
  -- ===== the norm class subgroups agree =====
  have hNL_BA : Idele.normClassSubgroup K ↥L.L = Idele.normClassSubgroup K ↥BA := by
    calc Idele.normClassSubgroup K ↥L.L
        = Idele.normClassSubgroup K ↥EL :=
          (NK.NUV2.TowerRank.normClassSubgroup_eq_of_algEquiv
            (NK.Reconstruct.levelToEquiv L M hLM)).symm
      _ = Idele.normClassSubgroup K ↥(IntermediateField.fixedField EL.fixingSubgroup) := by
          rw [IsGalois.fixedField_fixingSubgroup EL]
      _ = Idele.normClassSubgroup K ↥B :=
          NK.NUV2.TowerRank.normClassSubgroup_fixedField_sup_commutator_of_normal hFC EL.fixingSubgroup
      _ = Idele.normClassSubgroup K ↥BA :=
          (NK.NUV2.TowerRank.normClassSubgroup_eq_of_algEquiv
            (restrictLevelToEquiv B A hBA)).symm
  -- ===== the image of `ker (levelRestrict)` under `Φe` =====
  have himage : Φe '' ((NK.Reconstruct.levelRestrict L M hLM).ker)
      = Subgroup.map φA (EL.fixingSubgroup ⊔
          ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆) := by
    rw [levelRestrict_ker L M hLM]
    ext τ
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨σ, hσ, hσy⟩ := Subgroup.mem_map.mp hy
      rw [← hσy, hΦe σ]
      exact Subgroup.mem_map_of_mem _ hσ
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨Abelianization.of σ, Subgroup.mem_map_of_mem _ hσ, hΦe σ⟩
  -- ===== the transfer from the restriction to `BA` to the fixing of `B` =====
  have htransfer : ∀ σ : Gal(↥M.L/K),
      AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥A) ↥BA (φA σ) = 1 →
      σ ∈ EL.fixingSubgroup ⊔ ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆ := by
    intro σ hσ
    have hfixB : σ ∈ B.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      let xA : ↥A := ⟨x, hBA hx⟩
      have hy : xA ∈ BA := mem_restrictLevelTo_of_mem hBA xA hx
      let xBA : ↥BA := ⟨xA, hy⟩
      have h4 : (φA σ) xA = xA := by
        rw [← AlgEquiv.restrictNormalHom_apply (F := K) BA (φA σ) xBA, hσ,
          AlgEquiv.one_apply]
      have h5 := congrArg (fun z : ↥A => (z : ↥M.L)) h4
      rw [show ((φA σ) xA : ↥M.L) = σ (xA : ↥M.L) from
        AlgEquiv.restrictNormalHom_apply (F := K) A σ xA] at h5
      exact h5
    rwa [show B.fixingSubgroup = EL.fixingSubgroup ⊔
      ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆ from
        IntermediateField.fixingSubgroup_fixedField _] at hfixB
  -- ===== the inclusion =====
  have hle : Subgroup.map (MulEquiv.ofBijective eM hbijE).toMonoidHom
      (Subgroup.map (QuotientGroup.mk' (Idele.normClassSubgroup K ↥M.L))
        (Idele.normClassSubgroup K ↥L.L))
      ≤ (NK.Reconstruct.levelRestrict L M hLM).ker := by
    rintro y ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨u, hu, rfl⟩ := (show w ∈ (Idele.normImage K ↥L.L).map (IdeleClassGroup.mk K)
      from hw) |> Subgroup.mem_map.mp
    have huw : IdeleClassGroup.mk K u ∈ Idele.normClassSubgroup K ↥BA := by
      rw [← hNL_BA]
      exact Subgroup.mem_map_of_mem _ hu
    obtain ⟨v, hv, hvu⟩ := (show IdeleClassGroup.mk K u
      ∈ (Idele.normImage K ↥BA).map (IdeleClassGroup.mk K) from huw) |> Subgroup.mem_map.mp
    have hcls : QuotientGroup.mk' (Idele.normClassSubgroup K ↥M.L) (IdeleClassGroup.mk K v)
        = QuotientGroup.mk' (Idele.normClassSubgroup K ↥M.L) (IdeleClassGroup.mk K u) := by
      rw [hvu]
    rw [← hcls]
    change eM (QuotientGroup.mk' (Idele.normClassSubgroup K ↥M.L) (IdeleClassGroup.mk K v))
      ∈ (NK.Reconstruct.levelRestrict L M hLM).ker
    rw [heM v]
    have key : artA v ∈ Φe '' ((NK.Reconstruct.levelRestrict L M hLM).ker) := by
      rw [himage]
      obtain ⟨σ, hσ⟩ := hφAsurj (artA v)
      have hfix : AlgEquiv.restrictNormalHom (F := K) (K₁ := ↥A) ↥BA (φA σ) = 1 :=
        hσ.symm ▸ hartA_fixes v hv
      have hσB : σ ∈ EL.fixingSubgroup ⊔
          ⁅(⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L)), (⊤ : Subgroup (↥M.L ≃ₐ[K] ↥M.L))⁆ :=
        htransfer σ hfix
      exact hσ ▸ Subgroup.mem_map_of_mem (f := φA) hσB
    obtain ⟨γ, hγ, hγeq⟩ := key
    rw [← hγeq, Φe.symm_apply_apply]
    exact hγ
  -- ===== the cardinality comparison =====
  have hcardle : Nat.card (Subgroup.map (MulEquiv.ofBijective eM hbijE).toMonoidHom
      (Subgroup.map (QuotientGroup.mk' (Idele.normClassSubgroup K ↥M.L))
        (Idele.normClassSubgroup K ↥L.L)))
      = Nat.card ((NK.Reconstruct.levelRestrict L M hLM).ker) := by
    haveI hNMle : Idele.normClassSubgroup K ↥M.L ≤ Idele.normClassSubgroup K ↥L.L :=
      NK.NUV2.ArtinBridge.normClassSubgroup_le_of_intermediateField_le L.L M.L hLM
    haveI hfinL : (Idele.normClassSubgroup K ↥L.L).FiniteIndex :=
      Subgroup.finiteIndex_iff.mpr (NK.GlobalCFTdeep.normClassSubgroup_index_ne_zero (K := K) (L := ↥L.L))
    haveI : Finite (IdeleClassGroup K ⧸ Idele.normClassSubgroup K ↥L.L) := inferInstance
    have hM : (Idele.normClassSubgroup K ↥M.L).index
        = Nat.card (Abelianization (↥M.L ≃ₐ[K] ↥M.L)) :=
      NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement hFC
    have hL : (Idele.normClassSubgroup K ↥L.L).index
        = Nat.card (Abelianization (↥L.L ≃ₐ[K] ↥L.L)) :=
      NK.NUV2.ArtinBridge.index_eq_card_abelianization_of_fundamentalClassElement hFC
    have hrel : (Idele.normClassSubgroup K ↥M.L).relIndex (Idele.normClassSubgroup K ↥L.L)
        = Nat.card (Abelianization (↥M.L ≃ₐ[K] ↥M.L))
          / Nat.card (Abelianization (↥L.L ≃ₐ[K] ↥L.L)) := by
      refine (Nat.div_eq_of_eq_mul_right (n := Nat.card (Abelianization (↥L.L ≃ₐ[K] ↥L.L)))
        (by rw [← hL]; exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) ?_).symm
      calc Nat.card (Abelianization (↥M.L ≃ₐ[K] ↥M.L))
          = (Idele.normClassSubgroup K ↥M.L).index := hM.symm
        _ = (Idele.normClassSubgroup K ↥M.L).relIndex (Idele.normClassSubgroup K ↥L.L)
              * (Idele.normClassSubgroup K ↥L.L).index := (Subgroup.relIndex_mul_index hNMle).symm
        _ = (Idele.normClassSubgroup K ↥M.L).relIndex (Idele.normClassSubgroup K ↥L.L)
              * Nat.card (Abelianization (↥L.L ≃ₐ[K] ↥L.L)) := by rw [hL]
        _ = Nat.card (Abelianization (↥L.L ≃ₐ[K] ↥L.L))
              * (Idele.normClassSubgroup K ↥M.L).relIndex (Idele.normClassSubgroup K ↥L.L) :=
            mul_comm _ _
    have hker : Nat.card ((NK.Reconstruct.levelRestrict L M hLM).ker)
        = Nat.card (Abelianization (↥M.L ≃ₐ[K] ↥M.L))
          / Nat.card (Abelianization (↥L.L ≃ₐ[K] ↥L.L)) := by
      have hsurj := NK.Reconstruct.levelRestrict_surjective L M hLM
      have h1 : Nat.card (Abelianization (↥M.L ≃ₐ[K] ↥M.L)
            ⧸ (NK.Reconstruct.levelRestrict L M hLM).ker)
          = Nat.card (Abelianization (↥L.L ≃ₐ[K] ↥L.L)) :=
        (Nat.card_congr (QuotientGroup.quotientKerEquivRange
            (NK.Reconstruct.levelRestrict L M hLM)).toEquiv).trans
          (by rw [MonoidHom.range_eq_top.mpr hsurj]
              exact Nat.card_congr Subgroup.topEquiv.toEquiv)
      have h2 : Nat.card ↥((NK.Reconstruct.levelRestrict L M hLM).ker)
            * ((NK.Reconstruct.levelRestrict L M hLM).ker).index
          = Nat.card (Abelianization (↥M.L ≃ₐ[K] ↥M.L)) :=
        Subgroup.card_mul_index _
      have h3 : ((NK.Reconstruct.levelRestrict L M hLM).ker).index
          = Nat.card (Abelianization (↥L.L ≃ₐ[K] ↥L.L)) :=
        (Subgroup.index_eq_card _).trans h1
      have hpos : 0 < Nat.card (Abelianization (↥L.L ≃ₐ[K] ↥L.L)) := by
        rw [← h3]
        exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      refine (Nat.div_eq_of_eq_mul_right (n := Nat.card (Abelianization (↥L.L ≃ₐ[K] ↥L.L)))
        hpos ?_).symm
      rw [h3, mul_comm] at h2
      exact h2.symm
    rw [Subgroup.card_map_of_injective (MulEquiv.ofBijective eM hbijE).injective,
      natCard_map_mk'_eq_relIndex _ _ hNMle, hrel, hker]

  exact le_antisymm hle (Subgroup.eq_of_le_of_card_ge hle hcardle.ge).ge

end NK.NUV2.TowerRank
