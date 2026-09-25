import Mathlib
import Submission.NK.GlobalCFT.Reciprocity
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFTdeep.Transport.NormGroupTransport
import Submission.NK.Reconstruct.Gamma

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.NUV2.ArtinBridge

open scoped IsMulCommutative

universe u₃ u₄ u₁ u₅

/-- If `A ≤ B` are subgroups of a group with equal finite index, then `A = B`. -/
theorem subgroup_eq_of_le_of_index_eq {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B)
    (hidx : A.index = B.index) (hne : B.index ≠ 0) : A = B := by
  have h1 : A.relIndex B * B.index = B.index := by
    rw [Subgroup.relIndex_mul_index h, hidx]
  have h2 : A.relIndex B * B.index = 1 * B.index := by
    rw [one_mul]; exact h1
  have hrel : A.relIndex B = 1 := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) h2
  exact le_antisymm h (Subgroup.relIndex_eq_one.mp hrel)

/-- Every number field is small in every universe. -/
theorem small_numberField (K : Type u₁) [Field K] [NumberField K] : Small.{u₃} K := by
  haveI : Module.Free ℚ K := Module.Free.of_divisionRing ℚ K
  haveI : Small.{u₃} (Fin (Module.finrank ℚ K) → ℚ) := small_zero _
  exact Small.mk' ((Module.finBasis ℚ K).equivFun.toEquiv.trans
    (equivShrink (Fin (Module.finrank ℚ K) → ℚ)))

/-- **Conjugation by a compatible pair of ring equivalences.**  If `ι : K ≃+* S` and `ρ : L ≃+* T`
are ring equivalences compatible with the algebra structures, then conjugation by `ρ` is an
isomorphism of automorphism groups `(L ≃ₐ[K] L) ≃* (T ≃ₐ[S] T)`. -/
noncomputable def algEquivCongrOfRingEquiv {K S L T : Type*} [Field K] [Field S] [Field L]
    [Field T] [Algebra K L] [Algebra S T] (ι : K ≃+* S) (ρ : L ≃+* T)
    (hcomp : ∀ x : K, ρ (algebraMap K L x) = algebraMap S T (ι x)) :
    (L ≃ₐ[K] L) ≃* (T ≃ₐ[S] T) where
  toFun A := AlgEquiv.ofRingEquiv (f := (ρ.symm.trans A.toRingEquiv).trans ρ) (fun s => by
    show ρ (A (ρ.symm (algebraMap S T s))) = algebraMap S T s
    have h0 : ρ (algebraMap K L (ι.symm s)) = algebraMap S T s := by
      rw [hcomp (ι.symm s), ι.apply_symm_apply]
    have h1 : ρ.symm (algebraMap S T s) = algebraMap K L (ι.symm s) := by
      rw [← h0, RingEquiv.symm_apply_apply]
    rw [h1, A.commutes]
    exact h0)
  invFun B := AlgEquiv.ofRingEquiv (f := (ρ.trans B.toRingEquiv).trans ρ.symm) (fun x => by
    show ρ.symm (B (ρ (algebraMap K L x))) = algebraMap K L x
    have h0 : ρ (algebraMap K L x) = algebraMap S T (ι x) := hcomp x
    have h1 : ρ.symm (algebraMap S T (ι x)) = algebraMap K L x := by
      rw [← h0, RingEquiv.symm_apply_apply]
    rw [h0, B.commutes]
    exact h1)
  left_inv A := by ext x; simp
  right_inv B := by ext x; simp
  map_mul' A C := by ext x; simp

/-- **The index formula is invariant under a change of universes.**  If the norm-index formula
`[C_{K'} : N_{K'/K} C_{L'}] = |Gal(L'/K')ᵃᵇ|` is available for fields in the universes of `K'` and
`L'`, then it is available for fields `K`, `L` in any universes: the fields are replaced by
`Shrink`-copies lying in the universes where `hidx` applies. -/
theorem index_eq_card_abelianization_of_hidx
    (hidx : ∀ {K' : Type u₃} {L' : Type u₄} [Field K'] [NumberField K'] [Field L']
      [NumberField L'] [Algebra K' L'] [FiniteDimensional K' L'] [IsGalois K' L'],
      (NK.GlobalCFT.Idele.normClassSubgroup K' L').index =
        Nat.card (Abelianization (L' ≃ₐ[K'] L')))
    {K : Type u₁} [Field K] [NumberField K] {L : Type u₅} [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index =
      Nat.card (Abelianization (L ≃ₐ[K] L)) := by
  classical
  haveI hKs : Small.{u₃} K := small_numberField K
  haveI hLs : Small.{u₄} L := small_numberField L
  letI : Algebra (Shrink.{u₃} K) (Shrink.{u₄} L) :=
    Algebra.compHom (Shrink.{u₄} L) ((Shrink.ringEquiv K).toRingHom)
  haveI hgal : IsGalois (Shrink.{u₃} K) (Shrink.{u₄} L) := by
    refine IsGalois.of_equiv_equiv (f := (Shrink.ringEquiv K).symm)
      (g := (Shrink.algEquiv K L).symm.toRingEquiv) ?_
    ext x
    rw [RingHom.comp_apply, RingHom.comp_apply]
    refine congrArg (equivShrink L).symm ?_
    change (algebraMap K (Shrink.{u₄} L)) ((Shrink.ringEquiv K) ((Shrink.ringEquiv K).symm x)) =
      (Shrink.algEquiv K L).symm (algebraMap K L x)
    rw [RingEquiv.apply_symm_apply, Shrink.algEquiv_symm_apply, Equiv.algebraMap_def]
    rfl
  haveI hfd : FiniteDimensional (Shrink.{u₃} K) (Shrink.{u₄} L) := by
    haveI : FiniteDimensional K (Shrink.{u₄} L) :=
      LinearEquiv.finiteDimensional (Shrink.algEquiv K L).symm.toLinearEquiv
    have hst : IsScalarTower K (Shrink.{u₃} K) (Shrink.{u₄} L) := by
      refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
      rw [Algebra.compHom_algebraMap_apply]
      have h1 : (algebraMap K (Shrink.{u₃} K)) x = (equivShrink K) x := by
        rw [Equiv.algebraMap_def]; rfl
      rw [h1]
      have h2 : (Shrink.ringEquiv K).toRingHom ((equivShrink K) x) = x := by
        change (Shrink.ringEquiv K) ((Shrink.ringEquiv K).symm x) = x
        exact (Shrink.ringEquiv K).apply_symm_apply x
      rw [h2]
    exact @Module.Finite.of_restrictScalars_finite K (Shrink.{u₃} K) (Shrink.{u₄} L)
      _ _ _ _ _ _ hst _
  haveI hnfK : NumberField (Shrink.{u₃} K) := by
    haveI hcz : CharZero (Shrink.{u₃} K) := by
      refine charZero_of_inj_zero (fun n hn => ?_)
      have h : (n : K) = 0 := by
        have h' := congrArg (Shrink.ringEquiv K) hn
        simpa using h'
      exact CharZero.cast_injective (show (n : K) = ((0 : ℕ) : K) from by simpa using h)
    haveI hfd' : FiniteDimensional ℚ (Shrink.{u₃} K) :=
      LinearEquiv.finiteDimensional (Shrink.algEquiv ℚ K).symm.toLinearEquiv
    exact { to_charZero := hcz, to_finiteDimensional := hfd' }
  haveI hnfL : NumberField (Shrink.{u₄} L) := by
    haveI hcz : CharZero (Shrink.{u₄} L) := by
      refine charZero_of_inj_zero (fun n hn => ?_)
      have h : (n : L) = 0 := by
        have h' := congrArg (Shrink.ringEquiv L) hn
        simpa using h'
      exact CharZero.cast_injective (show (n : L) = ((0 : ℕ) : L) from by simpa using h)
    haveI hfd' : FiniteDimensional ℚ (Shrink.{u₄} L) :=
      LinearEquiv.finiteDimensional (Shrink.algEquiv ℚ L).symm.toLinearEquiv
    exact { to_charZero := hcz, to_finiteDimensional := hfd' }
  let eK : K ≃+* Shrink.{u₃} K := (Shrink.ringEquiv K).symm
  let eL : L ≃+* Shrink.{u₄} L := (Shrink.algEquiv K L).symm.toRingEquiv
  have hcompat : ∀ x : K, eL (algebraMap K L x) =
      algebraMap (Shrink.{u₃} K) (Shrink.{u₄} L) (eK x) := by
    intro x
    show eL (algebraMap K L x) = algebraMap (Shrink.{u₃} K) (Shrink.{u₄} L) (eK x)
    rw [Algebra.compHom_algebraMap_apply]
    change algebraMap K (Shrink.{u₄} L) x =
      algebraMap K (Shrink.{u₄} L) ((Shrink.ringEquiv K) ((Shrink.ringEquiv K).symm x))
    rw [RingEquiv.apply_symm_apply]
  have hindex : (NK.GlobalCFT.Idele.normClassSubgroup K L).index =
      (NK.GlobalCFT.Idele.normClassSubgroup (Shrink.{u₃} K) (Shrink.{u₄} L)).index :=
    NK.GlobalCFTdeep.Transport.normClassSubgroup_index_eq eK eL hcompat
  have hcard : Nat.card (Abelianization (L ≃ₐ[K] L)) =
      Nat.card (Abelianization (Shrink.{u₄} L ≃ₐ[Shrink.{u₃} K] Shrink.{u₄} L)) :=
    Nat.card_congr (MulEquiv.abelianizationCongr
      (algEquivCongrOfRingEquiv eK eL hcompat)).toEquiv
  rw [hindex, hidx (K' := Shrink.{u₃} K) (L' := Shrink.{u₄} L), ← hcard]

theorem exists_ellPowerLevel_normClassSubgroup_le {K : Type*} [Field K] [NumberField K]
    {Ω : Type*} [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosure K Ω] (ℓ : ℕ) [Fact ℓ.Prime]
    (hEx : NK.GlobalCFT.ExistenceTheorem K)
    (hidx : ∀ {K' L' : Type*} [Field K'] [NumberField K'] [Field L'] [NumberField L']
      [Algebra K' L'] [FiniteDimensional K' L'] [IsGalois K' L'],
      (NK.GlobalCFT.Idele.normClassSubgroup K' L').index =
        Nat.card (Abelianization (L' ≃ₐ[K'] L')))
    (V : Subgroup (NK.GlobalCFT.IdeleClassGroup K)) (hfi : V.FiniteIndex)
    (hopen : IsOpen (V : Set (NK.GlobalCFT.IdeleClassGroup K)))
    (hidxV : ∃ n : ℕ, V.index = ℓ ^ n) :
    ∃ (L : NK.Reconstruct.FrobLevel K Ω),
      IsPGroup ℓ (↥L.L ≃ₐ[K] ↥L.L) ∧
      NK.GlobalCFT.Idele.normClassSubgroup K ↥L.L ≤ V := by
  classical
  -- The abstract class field of `V`, given by the existence theorem.
  obtain ⟨L₀, hFldL₀, hNfL₀, hAlgL₀, hFdL₀, hGalL₀, hN⟩ := hEx.exists_normSubgroup V hfi hopen
  letI : Field L₀ := hFldL₀
  letI : NumberField L₀ := hNfL₀
  letI : Algebra K L₀ := hAlgL₀
  letI : FiniteDimensional K L₀ := hFdL₀
  letI : IsGalois K L₀ := hGalL₀
  -- The maximal abelian subextension: the fixed field of the commutator subgroup.
  let H : Subgroup (L₀ ≃ₐ[K] L₀) := commutator (L₀ ≃ₐ[K] L₀)
  haveI : H.Normal := Subgroup.commutator_normal (⊤ : Subgroup (L₀ ≃ₐ[K] L₀)) ⊤
  let M₀ : IntermediateField K L₀ := IntermediateField.fixedField H
  haveI : IsGalois K ↥M₀ := IsGalois.of_fixedField_normal_subgroup H
  haveI : FiniteDimensional K ↥M₀ := IntermediateField.finiteDimensional_left M₀
  haveI : FiniteDimensional ↥M₀ L₀ := IntermediateField.finiteDimensional_right M₀
  haveI : NumberField ↥M₀ := Commons.NumberTheory.NumberField.numberField_of_intermediateField M₀
  obtain ⟨n, hn⟩ := hidxV
  -- The index formula at both fields.
  have hidxL₀ : (NK.GlobalCFT.Idele.normClassSubgroup K L₀).index =
      Nat.card (Abelianization (L₀ ≃ₐ[K] L₀)) := index_eq_card_abelianization_of_hidx hidx
  have hidxM₀ : (NK.GlobalCFT.Idele.normClassSubgroup K ↥M₀).index =
      Nat.card (Abelianization (↥M₀ ≃ₐ[K] ↥M₀)) := index_eq_card_abelianization_of_hidx hidx
  have hcardG : Nat.card (Abelianization (L₀ ≃ₐ[K] L₀)) = ℓ ^ n := by
    rw [← hidxL₀, hN, hn]
  -- `Gal(M₀/K)` is the abelianisation of `Gal(L₀/K)`.
  have eG : (↥M₀ ≃ₐ[K] ↥M₀) ≃* Abelianization (L₀ ≃ₐ[K] L₀) :=
    (IsGalois.normalAutEquivQuotient (K := K) (L := L₀) H).symm
  have hcardX_abG : Nat.card (↥M₀ ≃ₐ[K] ↥M₀) = Nat.card (Abelianization (L₀ ≃ₐ[K] L₀)) :=
    Nat.card_congr eG.toEquiv
  haveI : IsMulCommutative (↥M₀ ≃ₐ[K] ↥M₀) :=
    IsMulCommutative.of_comm fun a b => eG.injective (by rw [map_mul, map_mul, mul_comm])
  have hcardAbX : Nat.card (Abelianization (↥M₀ ≃ₐ[K] ↥M₀)) = Nat.card (↥M₀ ≃ₐ[K] ↥M₀) :=
    (Nat.card_congr (Abelianization.equivOfComm (H := ↥M₀ ≃ₐ[K] ↥M₀)).toEquiv).symm
  have hcardM₀gal : Nat.card (↥M₀ ≃ₐ[K] ↥M₀) = ℓ ^ n := hcardX_abG.trans hcardG
  have hisPM₀ : IsPGroup ℓ (↥M₀ ≃ₐ[K] ↥M₀) := IsPGroup.of_card hcardM₀gal
  -- The norm subgroup of `M₀` equals `V`.
  have htower : NK.GlobalCFT.Idele.normClassSubgroup K L₀ ≤
      NK.GlobalCFT.Idele.normClassSubgroup K ↥M₀ :=
    NK.GlobalCFT.Idele.normClassSubgroup_le_of_tower
  have hidxEq : (NK.GlobalCFT.Idele.normClassSubgroup K L₀).index =
      (NK.GlobalCFT.Idele.normClassSubgroup K ↥M₀).index := by
    rw [hidxL₀, hidxM₀, hcardAbX, hcardX_abG]
  have hneM₀ : (NK.GlobalCFT.Idele.normClassSubgroup K ↥M₀).index ≠ 0 := by
    rw [hidxM₀, hcardAbX, hcardX_abG, hcardG]
    exact pow_ne_zero n (Nat.Prime.ne_zero (Fact.out : ℓ.Prime))
  have hEq : NK.GlobalCFT.Idele.normClassSubgroup K ↥M₀ = V := by
    rw [← subgroup_eq_of_le_of_index_eq htower hidxEq hneM₀, hN]
  -- The realisation of `M₀` inside `Ω`.
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  let φ : ↥M₀ →ₐ[K] Ω := IsSepClosed.lift
  let ψ : IntermediateField K Ω := φ.fieldRange
  let e : ↥M₀ ≃ₐ[K] ↥ψ := AlgEquiv.ofInjectiveField φ
  have hfinψ : FiniteDimensional K ↥ψ := LinearEquiv.finiteDimensional e.toLinearEquiv
  haveI : FiniteDimensional K ↥ψ := hfinψ
  have hnormψ : Normal K ↥ψ := Normal.of_algEquiv e
  haveI : Normal K ↥ψ := hnormψ
  have hnfψ : NumberField ↥ψ := Commons.NumberTheory.NumberField.numberField_of_intermediateField ψ
  haveI : NumberField ↥ψ := hnfψ
  -- The transport of the norm subgroup fixes `V` (because `hEx` exhibits `V` as a norm group).
  have hT : (V).map (NK.GlobalCFTdeep.Transport.ideleClassEquiv (RingEquiv.refl K)).toMonoidHom
      = V := by
    rw [← hN]
    exact NK.GlobalCFTdeep.Transport.normClassSubgroup_map_ideleClassEquiv
      (RingEquiv.refl K) (RingEquiv.refl L₀) (fun _ => rfl)
  have hNψ : NK.GlobalCFT.Idele.normClassSubgroup K ↥ψ = V := by
    have hmap := NK.GlobalCFTdeep.Transport.normClassSubgroup_map_ideleClassEquiv
      (K := K) (L := ↥M₀) (K' := K) (L' := ↥ψ) (RingEquiv.refl K) (e : ↥M₀ ≃+* ↥ψ)
      (fun x => e.commutes x)
    rw [← hmap, hEq, hT]
  refine ⟨{ L := ψ, finite := hfinψ, normal := hnormψ, numberField := hnfψ }, ?_, ?_⟩
  · exact IsPGroup.of_equiv hisPM₀ (AlgEquiv.autCongr e)
  · exact le_of_eq hNψ

end NK.NUV2.ArtinBridge
