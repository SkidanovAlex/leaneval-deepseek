import Mathlib
import Submission.NK.CFTLib.ArtinIdeal
import Submission.NK.CFTLib.RouteB.plan
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.CFTLib.ArtinReciprocityIdeal.Assembly
import Submission.NK.Cohomology.capture_two_map_eq_zero_of_cyclic
import Submission.Commons.GroupTheory.Subgroup.card_sup_mul_card_inf_of_normal
import Submission.NK.CFTLib.Existence.rep_invariants_le_range_norm_of_auxiliary

/-!
# The verification‑free reduction of `res_inf_le_ker_res_of_auxiliary`

This file contains the cohomological reduction which turns the target

`range (inf_{Msub}) ≤ ker (res_{Nsub})`

(an inclusion of subgroups of `H²(Gal(Ω/K), C_Ω)`) into the *arithmetic* statement

`(C_Ω)^{Gal(Ω/K)} ≤ N_{Ω/L'}C_Ω`,

where `L' = fixedField Nsub`.  The reduction uses

* the five‑term exactness/factorization `res_{Nsub} ∘ inf_{Msub} = map φ ι` with
  `φ : Nsub → Gal(Ω/K) ⧸ Msub` and `ι` the coefficient inclusion
  (`groupCohomology.map_comp`),
* the capture lemma `NK.Cohomology.capture_two_map_eq_zero_of_cyclic`: for a finite cyclic group
  `N`, a morphism `Φ : A ⟶ B` of `ℤ[N]`-representations which maps every `N`-invariant element of
  `A` into the image of the norm of `B` induces the zero map on `H²`.

The remaining arithmetic statement is proved in
`NK.CFTLib.Existence.rep_invariants_le_range_norm_of_auxiliary`.

-/

namespace NK.CFTLib.Existence

open CategoryTheory
open Pointwise

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

-- Prefer the `Module`/`AddCommGroup` structures coming from a representation over the generic
-- `ℤ`-module structure, so that the `Rep ℤ G`-diamonds do not produce `isDefEq` failures.
attribute [local instance 5000] Rep.hV1 Rep.hV2
attribute [local instance 100] AddCommGroup.toIntModule

section Reduction

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field Ω] [NumberField Ω] [Algebra K Ω]
  [FiniteDimensional K Ω] [IsGalois K Ω]

open IntermediateField

set_option linter.unusedSectionVars false

/-- `fixedField` of a supremum of subgroups is the infimum of the fixed fields. -/
lemma fixedField_sup_eq (M N : Subgroup Gal(Ω/K)) :
    fixedField (M ⊔ N) = fixedField M ⊓ fixedField N := by
  refine le_antisymm ?_ ?_
  · exact le_inf (fixedField_le le_sup_left) (fixedField_le le_sup_right)
  · intro x hx
    have hxM : ∀ m ∈ M, m x = x := fun m hm => (mem_fixedField_iff M x).mp hx.1 m hm
    have hxN : ∀ n ∈ N, n x = x := fun n hn => (mem_fixedField_iff N x).mp hx.2 n hn
    rw [mem_fixedField_iff]
    intro g hg
    have hM' : M ≤ MulAction.stabilizer Gal(Ω/K) x := fun m hm =>
      (MulAction.mem_stabilizer_iff).mpr (by rw [AlgEquiv.smul_def]; exact hxM m hm)
    have hN' : N ≤ MulAction.stabilizer Gal(Ω/K) x := fun n hn =>
      (MulAction.mem_stabilizer_iff).mpr (by rw [AlgEquiv.smul_def]; exact hxN n hn)
    have hsup : M ⊔ N ≤ MulAction.stabilizer Gal(Ω/K) x := sup_le hM' hN'
    have := hsup hg
    rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this

/-- `fixedField` of an infimum of subgroups is the supremum of the fixed fields (Galois
correspondence). -/
lemma fixedField_inf_eq (M N : Subgroup Gal(Ω/K)) :
    fixedField (M ⊓ N) = fixedField M ⊔ fixedField N := by
  have h1 : (fixedField M ⊔ fixedField N).fixingSubgroup = M ⊓ N := by
    rw [fixingSubgroup_sup, fixingSubgroup_fixedField M, fixingSubgroup_fixedField N]
  calc fixedField (M ⊓ N) = fixedField (fixedField M ⊔ fixedField N).fixingSubgroup := by rw [h1]
    _ = fixedField M ⊔ fixedField N := IsGalois.fixedField_fixingSubgroup _

/-- If the fixed fields of `M` and `N` are disjoint then `M ⊔ N = ⊤`. -/
lemma sup_eq_top_of_fixedField_inf_eq_bot (M N : Subgroup Gal(Ω/K))
    (h : fixedField M ⊓ fixedField N = ⊥) : M ⊔ N = ⊤ := by
  rw [← fixingSubgroup_fixedField (M ⊔ N), fixedField_sup_eq, h, fixingSubgroup_bot]

/-- If the fixed fields of `M` and `N` generate `Ω` then `M ⊓ N = ⊥`. -/
lemma inf_eq_bot_of_fixedField_sup_eq_top (M N : Subgroup Gal(Ω/K))
    (h : fixedField M ⊔ fixedField N = ⊤) : M ⊓ N = ⊥ := by
  rw [← fixingSubgroup_fixedField (M ⊓ N), fixedField_inf_eq, h, fixingSubgroup_top]

variable (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal]

/-- `|Msub| * |Nsub| = |Gal(Ω/K)|` for the complementary pair. -/
lemma card_mul_card_eq (hdisj : fixedField Msub ⊓ fixedField Nsub = ⊥)
    (hsup : fixedField Msub ⊔ fixedField Nsub = ⊤) :
    Nat.card ↥Msub * Nat.card ↥Nsub = Nat.card Gal(Ω/K) := by
  have hMN : Msub ⊔ Nsub = ⊤ := sup_eq_top_of_fixedField_inf_eq_bot Msub Nsub hdisj
  have hMiN : Msub ⊓ Nsub = ⊥ := inf_eq_bot_of_fixedField_sup_eq_top Msub Nsub hsup
  have h := Commons.GroupTheory.Subgroup.card_sup_mul_card_inf_of_normal Msub Nsub
    (inferInstance : Nsub.Normal)
  rw [hMN, hMiN, Subgroup.card_top, Subgroup.card_bot, mul_one] at h
  exact h.symm

/-- `|Nsub| = |Gal(Ω/K) ⧸ Msub|` for the complementary pair. -/
lemma card_nsub_eq_card_quotient (hdisj : fixedField Msub ⊓ fixedField Nsub = ⊥)
    (hsup : fixedField Msub ⊔ fixedField Nsub = ⊤) :
    Nat.card ↥Nsub = Nat.card (Gal(Ω/K) ⧸ Msub) := by
  have hcard := card_mul_card_eq Msub Nsub hdisj hsup
  have hM := Subgroup.card_mul_index Msub
  rw [Subgroup.index_eq_card] at hM
  have : Nonempty ↥Msub := ⟨1⟩
  haveI := this
  have key : Nat.card ↥Msub * Nat.card ↥Nsub = Nat.card ↥Msub * Nat.card (Gal(Ω/K) ⧸ Msub) := by
    rw [hcard, hM]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos key

end Reduction


section Main

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field Ω] [NumberField Ω] [Algebra K Ω]
  [FiniteDimensional K Ω] [IsGalois K Ω]

/-- An element fixed by two subgroups (the second one normal) is fixed by their supremum. -/
lemma mem_invariants_of_sup {G : Type*} [Group G] {A : Rep ℤ G} {H K : Subgroup G} [K.Normal]
    {a : A.V} (hH : ∀ g : ↥H, A.ρ (g : G) a = a) (hK : ∀ g : ↥K, A.ρ (g : G) a = a)
    (hsup : H ⊔ K = ⊤) : a ∈ A.ρ.invariants := by
  rw [Representation.mem_invariants]
  intro g
  have hgmem : g ∈ (H : Set G) * (K : Set G) := by
    rw [← Subgroup.mul_normal H K, hsup]
    exact Subgroup.mem_top g
  obtain ⟨m, hm, n, hn, rfl⟩ := Set.mem_mul.mp hgmem
  have hK' : A.ρ n a = a := hK ⟨n, hn⟩
  have hH' : A.ρ m a = a := hH ⟨m, hm⟩
  rw [map_mul]
  change A.ρ m (A.ρ n a) = a
  rw [hK', hH']

variable (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal] [Fintype Nsub]

set_option backward.isDefEq.respectTransparency false in
/-- **The cohomological reduction.**  The target inclusion of subgroups of `H²(Gal(Ω/K), C_Ω)`
follows from the arithmetic statement `(C_Ω)^{Gal(Ω/K)} ≤ N_{Ω/L'}C_Ω`. -/
theorem range_inf_le_ker_res_of_arithmetic
    (hN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (hM : Nat.card (Gal(Ω/K) ⧸ Msub) = Nat.card Gal(L/K))
    (hcyc : IsCyclic (Gal(Ω/K) ⧸ Msub))
    (hdisj : IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥)
    (hsup : IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤)
    (harith : (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ.invariants ≤
      LinearMap.range ((Rep.res Nsub.subtype (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).ρ.norm)) :
    LinearMap.range
        ((groupCohomology.infNatTrans ℤ Msub 2).app
          (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).hom ≤
      LinearMap.ker
        ((groupCohomology.resNatTrans ℤ (G := Nsub) (H := Gal(Ω/K)) Nsub.subtype 2).app
          (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).hom := by
  classical
  set A : Rep ℤ Gal(Ω/K) := NK.GlobalCFT.IdeleClassGroup.rep K Ω with hA
  have hMN : Msub ⊔ Nsub = ⊤ := sup_eq_top_of_fixedField_inf_eq_bot Msub Nsub hdisj
  have hMiN : Msub ⊓ Nsub = ⊥ := inf_eq_bot_of_fixedField_sup_eq_top Msub Nsub hsup
  -- `φ` is bijective, hence `Nsub` is cyclic
  have hφker : ((QuotientGroup.mk' Msub).comp Nsub.subtype).ker = ⊥ := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      have hxM : ((x : ↥Nsub) : Gal(Ω/K)) ∈ Msub :=
        (QuotientGroup.eq_one_iff (x := ((x : ↥Nsub) : Gal(Ω/K)))).mp hx
      have h2 : ((x : ↥Nsub) : Gal(Ω/K)) ∈ Msub ⊓ Nsub := ⟨hxM, x.2⟩
      rw [hMiN] at h2
      rw [Subgroup.mem_bot]
      exact Subtype.ext (by simpa using h2)
    · intro hx
      rw [Subgroup.mem_bot] at hx
      subst hx
      simp
  have hφinj : Function.Injective ((QuotientGroup.mk' Msub).comp Nsub.subtype) :=
    (MonoidHom.ker_eq_bot_iff _).mp hφker
  have hφcard : Nat.card ↥Nsub = Nat.card (Gal(Ω/K) ⧸ Msub) :=
    card_nsub_eq_card_quotient Msub Nsub hdisj hsup
  have hφbij : Function.Bijective ((QuotientGroup.mk' Msub).comp Nsub.subtype) :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨hφinj, hφcard⟩
  haveI hcycN : IsCyclic ↥Nsub :=
    (MulEquiv.isCyclic (MulEquiv.ofBijective _ hφbij)).mpr hcyc
  -- the capture
  have hcap : groupCohomology.map (MonoidHom.id ↥Nsub)
      (A := Rep.res ((QuotientGroup.mk' Msub).comp Nsub.subtype) (A.quotientToInvariants Msub))
      (Rep.resMap Nsub.subtype (Rep.ofHom (A.ρ.quotientToInvariants_lift Msub))) 2 = 0 := by
    refine NK.Cohomology.capture_two_map_eq_zero_of_cyclic
      (A := Rep.res ((QuotientGroup.mk' Msub).comp Nsub.subtype) (A.quotientToInvariants Msub))
      (Rep.resMap Nsub.subtype (Rep.ofHom (A.ρ.quotientToInvariants_lift Msub))) ?_
    intro a ha
    have hH : ∀ g : ↥Msub, A.ρ (g : Gal(Ω/K)) (a : A.V) = (a : A.V) := fun g =>
      (Representation.mem_invariants (A.ρ.comp Msub.subtype) a.1).mp a.2 g
    have hK : ∀ g : ↥Nsub, A.ρ (g : Gal(Ω/K)) (a : A.V) = (a : A.V) := by
      intro g
      have h2 := Commons.RepresentationTheory.GroupCohomology.quotientToInvariants_rho_apply
        (A := A) Msub (g : Gal(Ω/K)) a
      rw [← h2]
      exact congrArg Subtype.val (ha g)
    have hGL : (a : A.V) ∈ A.ρ.invariants := mem_invariants_of_sup hH hK hMN
    obtain ⟨b, hb⟩ := harith hGL
    refine ⟨b, ?_⟩
    rw [Rep.norm_apply, hb]
    rfl
  -- the factorization
  have hfac : CategoryTheory.CategoryStruct.comp
      ((groupCohomology.infNatTrans ℤ Msub 2).app A)
      ((groupCohomology.resNatTrans ℤ (G := Nsub) (H := Gal(Ω/K)) Nsub.subtype 2).app A)
      = groupCohomology.map ((QuotientGroup.mk' Msub).comp Nsub.subtype)
          (A := A.quotientToInvariants Msub)
          (Rep.resMap Nsub.subtype (Rep.ofHom (A.ρ.quotientToInvariants_lift Msub))) 2 := by
    rw [groupCohomology.infNatTrans_app, groupCohomology.resNatTrans_app]
    rw [← groupCohomology.map_comp]
    simp only [Category.comp_id]
  have hzero : CategoryTheory.CategoryStruct.comp
      ((groupCohomology.infNatTrans ℤ Msub 2).app A)
      ((groupCohomology.resNatTrans ℤ (G := Nsub) (H := Gal(Ω/K)) Nsub.subtype 2).app A) = 0 := by
    rw [hfac]
    rw [Commons.RepresentationTheory.GroupCohomology.map_eq_map_id_comp_map
        ((QuotientGroup.mk' Msub).comp Nsub.subtype) (A := A.quotientToInvariants Msub)
        (Rep.resMap Nsub.subtype (Rep.ofHom (A.ρ.quotientToInvariants_lift Msub))) 2, hcap]
    simp
  rw [LinearMap.range_le_ker_iff]
  have h1 := congrArg ModuleCat.Hom.hom hzero
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h1
  exact h1

end Main


/-- **The requested lemma.** -/
theorem res_inf_le_ker_res_of_auxiliary (h : NK.CFTLib.ArtinReciprocityIdeal)
    {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [Field Ω] [NumberField Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal]
    (hN : Nat.card (Gal(Ω/K) ⧸ Nsub) = Nat.card Gal(L/K))
    (hM : Nat.card (Gal(Ω/K) ⧸ Msub) = Nat.card Gal(L/K))
    (hcyc : IsCyclic (Gal(Ω/K) ⧸ Msub))
    (hdisj : IntermediateField.fixedField Msub ⊓ IntermediateField.fixedField Nsub = ⊥)
    (hsup : IntermediateField.fixedField Msub ⊔ IntermediateField.fixedField Nsub = ⊤) :
    LinearMap.range
        ((groupCohomology.infNatTrans ℤ Msub 2).app
          (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).hom ≤
      LinearMap.ker
        ((groupCohomology.resNatTrans ℤ (G := Nsub) (H := Gal(Ω/K)) Nsub.subtype 2).app
          (NK.GlobalCFT.IdeleClassGroup.rep K Ω)).hom := by
  haveI hfin : Fintype ↥Nsub := Fintype.ofFinite ↥Nsub
  exact range_inf_le_ker_res_of_arithmetic Msub Nsub hN hM hcyc hdisj hsup
    (rep_invariants_le_range_norm_of_auxiliary h Msub Nsub hN hM hcyc hdisj hsup)

end NK.CFTLib.Existence
