/-
# The Galois group of `Ω = L(ζ_M)`: the pairing `Γ → Gal(A/K) × (ℤ/M)ˣ`

For `Ω = CyclotomicField M L`, `A` the image of `L` in `Ω` and `ζ = ζ_M`, the map
`γ ↦ (γ|_A, χ(γ))` (with `χ(γ)` the exponent by which `γ` acts on `ζ`) is an
isomorphism `Gal(Ω/K) ≃* Gal(A/K) × (ℤ/M)ˣ`, provided no prime divisor of `M`
divides `discr L` (which makes `A` and `B = K(ζ_M)` linearly disjoint over `K`).
-/
import Mathlib
import Submission.NK.NUV2.ARL.Gap.conductor_crux.AuxSetup
import Submission.NK.CFTLib.ARL.isGalois_cyclotomicField_over_base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.NUV2.ARL.Gap.conductor_crux

/-- `LinearDisjoint` of two intermediate fields from the triviality of their intersection
(the `IsGalois` instance on the first factor is passed explicitly, since it is not found by
type-class search at the application site). -/
private theorem ld_of_inf_eq_bot {F E : Type*} [Field F] [Field E] [Algebra F E]
    {A B : IntermediateField F E} [IsGalois F ↥A] [FiniteDimensional F ↥A]
    [FiniteDimensional F ↥B] (h : A ⊓ B = ⊥) : A.LinearDisjoint ↥B :=
  IntermediateField.LinearDisjoint.of_inf_eq_bot h

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] (M : ℕ) [NeZero M]

/-! ## The two components -/

/-- Restriction of automorphisms of `Ω` to the image `A` of `L`. -/
def AuxPhi1 : ((CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)) →*
    (↥(AuxA K L M) ≃ₐ[K] ↥(AuxA K L M)) := by
  haveI : Normal K ↥(AuxA K L M) := AuxA_normal M
  exact AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L) ↥(AuxA K L M)

lemma AuxPhi1_apply (γ : (CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L))
    (x : ↥(AuxA K L M)) :
    ((AuxPhi1 M γ x : ↥(AuxA K L M)) : CyclotomicField M L) = γ (x : CyclotomicField M L) := by
  haveI : Normal K ↥(AuxA K L M) := AuxA_normal M
  have h : AuxPhi1 M γ =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L) ↥(AuxA K L M) γ := rfl
  rw [h]
  exact AlgEquiv.restrictNormalHom_apply (F := K) (K₁ := CyclotomicField M L) (AuxA K L M) γ x

/-- The cyclotomic character: the exponent by which an automorphism of `Ω` acts on `ζ_M`. -/
def AuxChi : ((CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)) →* (ZMod M)ˣ :=
  (AuxZeta_isPrimitiveRoot L M).autToPow K

lemma AuxChi_apply (γ : (CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)) :
    (AuxZeta L M) ^ (((AuxChi M γ : (ZMod M)ˣ) : ZMod M)).val = γ (AuxZeta L M) :=
  IsPrimitiveRoot.autToPow_spec K (AuxZeta_isPrimitiveRoot L M) γ

/-- The pairing `γ ↦ (γ|_A, χ(γ))`. -/
def AuxPsi : ((CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)) →*
    (↥(AuxA K L M) ≃ₐ[K] ↥(AuxA K L M)) × (ZMod M)ˣ :=
  (AuxPhi1 M).prod (AuxChi M)

@[simp] lemma AuxPsi_fst (γ : (CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)) :
    (AuxPsi M γ).1 = AuxPhi1 M γ := rfl

@[simp] lemma AuxPsi_snd (γ : (CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)) :
    (AuxPsi M γ).2 = AuxChi M γ := rfl

/-! ## Injectivity -/

/-- The cyclotomic character is trivial exactly on the automorphisms fixing `ζ_M`. -/
lemma AuxChi_eq_one_iff (γ : (CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)) :
    AuxChi M γ = 1 ↔ γ (AuxZeta L M) = AuxZeta L M := by
  have hζ := AuxZeta_isPrimitiveRoot L M
  have hord : orderOf (AuxZeta L M) = M := hζ.eq_orderOf.symm
  have hfin : IsOfFinOrder (AuxZeta L M) := hζ.isOfFinOrder (NeZero.ne M)
  constructor
  · intro h
    have hspec := AuxChi_apply M γ
    have he : (((AuxChi M γ : (ZMod M)ˣ) : ZMod M)).val ≡ 1 [MOD M] := by
      refine (ZMod.natCast_eq_natCast_iff _ _ M).mp ?_
      rw [ZMod.natCast_zmod_val, h, Units.val_one]
      simp
    have hmod : (((AuxChi M γ : (ZMod M)ˣ) : ZMod M)).val ≡ 1 [MOD orderOf (AuxZeta L M)] := by
      rw [hord]; exact he
    have h1 : (AuxZeta L M) ^ (((AuxChi M γ : (ZMod M)ˣ) : ZMod M)).val = (AuxZeta L M) ^ 1 :=
      hfin.pow_eq_pow_iff_modEq.mpr hmod
    rw [← hspec, h1, pow_one]
  · intro h
    have hspec := AuxChi_apply M γ
    rw [h] at hspec
    have hspec' : (AuxZeta L M) ^ (((AuxChi M γ : (ZMod M)ˣ) : ZMod M)).val =
        (AuxZeta L M) ^ 1 := by
      rw [pow_one]; exact hspec
    have hmod := hfin.pow_eq_pow_iff_modEq.mp hspec' 
    rw [hord] at hmod
    refine Units.ext ?_
    rw [Units.val_one, ← ZMod.natCast_zmod_val ((AuxChi M γ : (ZMod M)ˣ) : ZMod M)]
    simpa using (ZMod.natCast_eq_natCast_iff _ _ M).mpr hmod

/-- An automorphism of `Ω` fixing `A` (the image of `L`) and `ζ_M` is trivial. -/
lemma AuxPsi_eq_one {γ : (CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)}
    (hγ : AuxPsi M γ = 1) : γ = 1 := by
  have h1 : AuxPhi1 M γ = 1 := by
    have := congrArg Prod.fst hγ
    simpa using this
  have h2 : AuxChi M γ = 1 := by
    have := congrArg Prod.snd hγ
    simpa using this
  have hfixA : ∀ x ∈ (AuxA K L M : Set (CyclotomicField M L)), γ x = x := by
    intro x hx
    have hx' := AuxPhi1_apply M γ ⟨x, hx⟩
    rw [h1] at hx'
    simpa using hx'.symm
  have hfixZ : γ (AuxZeta L M) = AuxZeta L M := (AuxChi_eq_one_iff M γ).mp h2
  have hle : AuxB K L M ≤ IntermediateField.fixedField (Subgroup.zpowers γ) := by
    rw [AuxB, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    change AuxZeta L M ∈ IntermediateField.fixedField (Subgroup.zpowers γ)
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have hstab : f ∈ MulAction.stabilizer
        ((CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)) (AuxZeta L M) :=
      Subgroup.zpowers_le.mpr (by simpa [AlgEquiv.smul_def] using hfixZ) hf
    simpa [AlgEquiv.smul_def] using (MulAction.mem_stabilizer_iff.mp hstab)
  have hfixB : γ ∈ (AuxB K L M).fixingSubgroup :=
    Subgroup.zpowers_le.mp ((IntermediateField.le_iff_le (Subgroup.zpowers γ) (AuxB K L M)).mp hle)
  have hmem : γ ∈ (AuxA K L M ⊔ AuxB K L M).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff (K := AuxA K L M) γ).mpr hfixA, hfixB⟩
  rw [AuxA_sup_AuxB_eq_top (K := K) (L := L) M] at hmem
  simpa using hmem

lemma AuxPsi_injective : Function.Injective
    (fun γ : (CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L) => AuxPsi M γ) := by
  intro γ δ h
  change AuxPsi M γ = AuxPsi M δ at h
  have h' : AuxPsi M (γ * δ⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  exact mul_inv_eq_one.mp (AuxPsi_eq_one M h')

/-! ## The degree and cardinality computations -/

/-- `[L(ζ_M) : K] = [L : K]·φ(M)`. -/
lemma AuxOmega_finrank
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs) :
    Module.finrank K (CyclotomicField M L) = Module.finrank K L * M.totient := by
  have hMK : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr K).natAbs := by
    have hd : (NumberField.discr K).natAbs ∣ (NumberField.discr L).natAbs :=
      Int.natAbs_dvd_natAbs.mpr (NumberField.discr_dvd_discr K L)
    intro p hp hpm hpk
    exact hM p hp hpm (dvd_trans hpk hd)
  set Ω := CyclotomicField M L with hΩ
  set ζ := IsCyclotomicExtension.zeta M L Ω with hζdef
  have hζprim : IsPrimitiveRoot ζ M := IsCyclotomicExtension.zeta_spec M L Ω
  set Qζ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({ζ} : Set Ω) with hQζ
  set Lq : IntermediateField ℚ Ω := (⊥ : IntermediateField L Ω).restrictScalars ℚ with hLq
  haveI hQζcyc : IsCyclotomicExtension {M} ℚ ↥Qζ :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M ℚ Ω Qζ hζprim).mpr rfl
  haveI hQζgal : IsGalois ℚ ↥Qζ := IsCyclotomicExtension.isGalois {M} ℚ ↥Qζ
  haveI hQζfd : FiniteDimensional ℚ ↥Qζ :=
    IsCyclotomicExtension.finiteDimensional {M} ℚ ↥Qζ
  have hfrQζ : Module.finrank ℚ ↥Qζ = M.totient :=
    IsCyclotomicExtension.finrank ↥Qζ (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))
  haveI hLqfd : FiniteDimensional ℚ ↥Lq := by
    rw [hLq]; exact FiniteDimensional.trans ℚ L ↥(⊥ : IntermediateField L Ω)
  have hfrLq : Module.finrank ℚ ↥Lq = Module.finrank ℚ L := by
    have h1 : Module.finrank ℚ ↥Lq = Module.finrank ℚ ↥(⊥ : IntermediateField L Ω) := rfl
    rw [h1, ← Module.finrank_mul_finrank ℚ L ↥(⊥ : IntermediateField L Ω),
      (IntermediateField.botEquiv L Ω).toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]
  have hdisj : Qζ ⊓ Lq = ⊥ := by
    rw [hQζ, hLq]
    exact NK.CFTLib.ARL.intersect_cyclotomic_eq_bot_gen (F := L) M hM ζ hζprim
  have hLD : Qζ.LinearDisjoint ↥Lq :=
    @ld_of_inf_eq_bot ℚ Ω _ _ _ Qζ Lq hQζgal hQζfd hLqfd hdisj
  have hsup : Lq ⊔ Qζ = ⊤ := by
    rw [hLq, hQζ]
    exact Aux_sup_restrictScalars_adjoin_zeta_eq_top ℚ L M
  have hfrΩ : Module.finrank ℚ Ω = Module.finrank ℚ L * M.totient := by
    have h1 : Module.finrank ℚ ↥(Qζ ⊔ Lq) = Module.finrank ℚ ↥Qζ * Module.finrank ℚ ↥Lq :=
      IntermediateField.LinearDisjoint.finrank_sup (A := Qζ) (B := Lq) hLD
    rw [hfrQζ, hfrLq, mul_comm] at h1
    have h2 : Module.finrank ℚ ↥(Qζ ⊔ Lq) = Module.finrank ℚ Ω := by
      rw [sup_comm, hsup]
      exact (IntermediateField.topEquiv (F := ℚ)).toLinearEquiv.finrank_eq
    rw [← h2, h1]
  have h3 : Module.finrank ℚ K * Module.finrank K Ω = Module.finrank ℚ Ω :=
    Module.finrank_mul_finrank ℚ K Ω
  have h4 : Module.finrank ℚ K * Module.finrank K L = Module.finrank ℚ L :=
    Module.finrank_mul_finrank ℚ K L
  rw [← h4, ← h3, mul_assoc] at hfrΩ
  exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos hfrΩ

lemma AuxOmega_card
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs) :
    Nat.card ((CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)) =
      Module.finrank K L * M.totient := by
  haveI := NK.CFTLib.ARL.isGalois_cyclotomicField_over_base (K := K) (L := L) M
  rw [IsGalois.card_aut_eq_finrank K (CyclotomicField M L), AuxOmega_finrank M hM]

lemma AuxPsi_bijective
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs) :
    Function.Bijective
      (fun γ : (CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L) => AuxPsi M γ) := by
  haveI hAg : IsGalois K ↥(AuxA K L M) := AuxA_isGalois M
  haveI hAfd : FiniteDimensional K ↥(AuxA K L M) := AuxA_finiteDimensional M
  haveI : Fintype ((CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)) := Fintype.ofFinite _
  haveI : Fintype (↥(AuxA K L M) ≃ₐ[K] ↥(AuxA K L M)) := Fintype.ofFinite _
  haveI : Fintype ((↥(AuxA K L M) ≃ₐ[K] ↥(AuxA K L M)) × (ZMod M)ˣ) := Fintype.ofFinite _
  refine (Fintype.bijective_iff_injective_and_card (AuxPsi M)).mpr ⟨AuxPsi_injective M, ?_⟩
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, Nat.card_prod,
    IsGalois.card_aut_eq_finrank K ↥(AuxA K L M), AuxA_finrank, AuxOmega_card M hM]
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- The pairing as a group isomorphism. -/
def AuxPsiEquiv
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs) :
    ((CyclotomicField M L) ≃ₐ[K] (CyclotomicField M L)) ≃*
      (↥(AuxA K L M) ≃ₐ[K] ↥(AuxA K L M)) × (ZMod M)ˣ :=
  MulEquiv.ofBijective (AuxPsi M) (AuxPsi_bijective M hM)

end NK.NUV2.ARL.Gap.conductor_crux
