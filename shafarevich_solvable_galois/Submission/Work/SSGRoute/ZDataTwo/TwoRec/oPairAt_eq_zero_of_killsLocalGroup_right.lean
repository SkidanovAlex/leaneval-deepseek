import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.oPairAt_eq_zero_of_killsLocalGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZDataTwo.TwoRec

theorem oPairAt_eq_zero_of_killsLocalGroup_right {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (α β : (↥K)ˣ) (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β u = 0) :
    Work.SSGRoute.ZDataMup.OddForm.oPairAt (K := K) (p := 2) (k := k) (Ω := Ω)
        (⟨ζ, hζK⟩ : ↥K) (Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ)
        A hA
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ α)
        (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) = 0 := by
  classical
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) 2 :=
    Work.SSGRoute.ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  -- the Kummer cochain of `β` is a locally constant cocycle on `K.fixingSubgroup`
  have hbcoc : SSGRoute.IsCocycleOn (SSGRoute.res k K) K.fixingSubgroup
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) := by
    intro g hg h' hh
    rw [Work.SSGRoute.ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ β g hg h' hh]
    rfl
  have hb : Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β ∈
      Work.SSGRoute.lcCocycles 2 k Ω K (ZMod 2) K.fixingSubgroup :=
    ⟨hbcoc, Work.SSGRoute.ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ β⟩
  -- it is the Kummer character of `β` on `K.fixingSubgroup`
  have hchar : ∀ (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ K.fixingSubgroup),
      Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β σ =
        Work.SSGRoute.kummerCharZMod (Ω := Ω) (K := ↥K) 2 (ζ := (⟨ζ, hζK⟩ : ↥K)) hζ' β
          ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩) :=
    fun σ hσ => Work.SSGRoute.ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ)
      (hζK := hζK) (hζ := hζ) (β := β) hσ
  -- hence its local model at `A` is the local Kummer character of `β`
  have hmodel := Work.SSGRoute.ZDataMup.OddForm.localModelIso_toClass_eq_kummerCharMonoidHom_of_toClass
      (K := K) (p := 2) (k := k) (Ω := Ω) (A := A) (⟨ζ, hζK⟩ : ↥K) hζ' hA β
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) hb hchar
  -- the local Kummer dictionary: `β` is a local square at `A`
  have hpow : NK.UchidaKummer.localPowClass ↥K 2
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA) β = 1 :=
    (Work.SSGRoute.ZSplit.nodeKummerCocharZMod_eq_zero_iff_localPowClass K ζ hζK hζ β A hA
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := A) hA)).mp h
  -- so the local Kummer character of `β` is trivial
  have hchar1 : Work.SSGRoute.ZConstruction.kummerCharMonoidHom (K := K) (p := 2) (k := k)
      (Ω := Ω) (ζ := (⟨ζ, hζK⟩ : ↥K)) (hζ := hζ') (A := A) hA β = 1 :=
    (Work.SSGRoute.ZConstruction.kummerCharMonoidHom_eq_one_iff (K := K) (p := 2) (k := k)
      (Ω := Ω) (ζ := (⟨ζ, hζK⟩ : ↥K)) (hζ := hζ') (A := A) hA
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime (K := K) A hA)
      (Work.SSGRoute.ZDataMup.OddForm.oddPrime_spec (K := K) (A := A) hA) β).mpr hpow
  -- and the local class of the cochain of `β` is zero
  have hzero : Work.SSGRoute.toClass 2 k Ω K (ZMod 2) (SSGRoute.decomp k A ⊓ K.fixingSubgroup)
      (Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ β) = 0 := by
    refine (Work.SSGRoute.ZConstruction.localModelIso_bijective (p := 2) (k := k) (Ω := Ω)
      (K := K) (A := A) hA).injective ?_
    rw [hmodel, hchar1, Work.SSGRoute.ZConstruction.localModelIso_zero]
  -- a pairing whose second argument is zero vanishes
  unfold Work.SSGRoute.ZDataMup.OddForm.oPairAt
  rw [hzero, Work.SSGRoute.ZDataMup.OddForm.oPairForm_apply,
    Work.SSGRoute.ZDataMup.OddForm.oPair_zero_right]

end Work.SSGRoute.ZDataTwo.TwoRec
