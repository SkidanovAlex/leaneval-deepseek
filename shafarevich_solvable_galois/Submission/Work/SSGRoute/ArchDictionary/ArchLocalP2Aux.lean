import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Submission.Work.SSGRoute.ArchDictionary.Defs
import Submission.Work.SSGRoute.ArchDictionary.placeLocalFieldComplex
import Submission.Work.SSGRoute.ExtChain.resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero
import Submission.Work.SSGRoute.PT.decompK_linked
import Submission.Work.SSGRoute.PTdualControl.archimedeanLocalPush
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary vocabulary for `archLocalZeroImpCoboundaryP2`

This module collects the *general* `Ext`-lemmas and the vocabulary used in the proof of
`Work.SSGRoute.ArchDictionary.archLocalZeroImpCoboundaryP2`.

The mathematical content of the target at a complex archimedean place is the comparison between
the **localisation** of the canonical global dictionary class at `w` (a class with values in
`K_wˣ = ℂˣ`, i.e. in the completion) and the **restriction** of the class to the decomposition
group `D_w = ⟨res k K c⟩`.

The proof strategy: at a *complex* archimedean place the local field is `ℂ` and the linking
embedding `φ : Ω →+* ℂ` gives an honest coefficient map `Ωˣ → K_wˣ` (this is what fails at finite
places, where the converse of the local criterion is refuted).  The extension criterion for
`resH1_D (e1cMap R ·) = 0` (a `D`-invariant lift of the coefficient datum on the canonical cover)
is an *exactness* statement, so it can be transported along a coefficient injection whose cokernel
has no `2`-torsion — and at the archimedean place `ℂˣ/φ(Ωˣ)` has no `2`-torsion because `Ω` is
algebraically closed.

## Contents

* `subsingleton_ext0_of_subsingleton_hom`, `ext_one_postcomp_injective_of_subsingleton_ext0`,
  `shortExact_mono_cokernel`: general facts about `Ext` in an abelian category.
* `res_ne_one_of_decompK_ne_bot`: at a linked complex place, `res k K c ≠ 1`.
* `eq_one_or_eq_of_mem_zpowers`: the elements of `⟨c⟩` for an involution `c`.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1
set_option backward.isDefEq.respectTransparency false

section GeneralExt

/-- If the `Hom`-space `X ⟶ Y` is a subsingleton, so is `Ext⁰(X, Y)` (via the degree-zero
equivalence `Ext⁰(X,Y) ≃+ (X ⟶ Y)`). -/
theorem subsingleton_ext0_of_subsingleton_hom {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (h : Subsingleton (X ⟶ Y)) : Subsingleton (Abelian.Ext X Y 0) := by
  have hz : ∀ f : Abelian.Ext X Y 0, f = 0 := by
    intro f
    rw [← Abelian.Ext.mk₀_addEquiv₀_apply f,
      Subsingleton.elim (Abelian.Ext.addEquiv₀ f) 0, Abelian.Ext.mk₀_zero]
  exact ⟨fun a b => by rw [hz a, hz b]⟩

/-- **The push along the first map of a short exact sequence of coefficients is injective, provided
`Ext⁰(·, S.X₃)` vanishes.**  Concretely, for `S : 0 → S.X₁ --f--> S.X₂ --g--> S.X₃ → 0` short exact
and `X` any object, if `Ext⁰(X, S.X₃) = 0` then `Ext¹(X, S.X₁) → Ext¹(X, S.X₂)`, `x ↦ x ∘ f`, is
injective.  This is the exactness of the long exact sequence at `Ext¹(X, S.X₁)` together with the
vanishing of the preceding term. -/
theorem ext_one_postcomp_injective_of_subsingleton_ext0 {C : Type*} [Category C]
    [Abelian C] [HasExt C] {S : ShortComplex C} (hS : S.ShortExact) (X : C)
    (h : Subsingleton (Abelian.Ext X S.X₃ 0)) :
    Function.Injective (fun x : Abelian.Ext X S.X₁ 1 =>
      x.comp (Abelian.Ext.mk₀ S.f) (zero_add 1)) := by
  intro x y hxy
  have hxy' : x.comp (Abelian.Ext.mk₀ S.f) (zero_add 1)
      = y.comp (Abelian.Ext.mk₀ S.f) (zero_add 1) := hxy
  rw [← sub_eq_zero]
  have h0 : (x - y).comp (Abelian.Ext.mk₀ S.f) (zero_add 1) = 0 := by
    rw [sub_eq_add_neg, Abelian.Ext.add_comp, Abelian.Ext.neg_comp, hxy', add_neg_cancel]
  obtain ⟨x₃, hx₃⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS (x - y) h0 (zero_add 1)
  rw [Subsingleton.elim x₃ 0, Abelian.Ext.zero_comp] at hx₃
  exact hx₃.symm

/-- **A monomorphism is the kernel of its cokernel**: for a mono `φ : A ⟶ B` in an abelian
category, the short complex `A --φ--> B --π--> cokernel φ` (with `π = cokernel.π φ`) is short
exact. -/
theorem shortExact_mono_cokernel {C : Type*} [Category C] [Abelian C] {A B : C} (φ : A ⟶ B)
    [Mono φ] :
    (ShortComplex.mk φ (Limits.cokernel.π φ) (Limits.cokernel.condition φ)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [ShortComplex.exact_iff_mono_cokernel_desc]
  have h : Limits.cokernel.desc φ (Limits.cokernel.π φ)
      (ShortComplex.zero (ShortComplex.mk φ (Limits.cokernel.π φ)
        (Limits.cokernel.condition φ))) = 𝟙 (Limits.cokernel φ) := by
    rw [← cancel_epi (Limits.cokernel.π φ), Limits.cokernel.π_desc, Category.comp_id]
  rw [h]
  infer_instance

end GeneralExt

section Setup

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- At a place linked to an involution `c ≠ 1` with nontrivial decomposition group, `res k K c`
is not `1`. -/
theorem res_ne_one_of_decompK_ne_bot (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) : SSGRoute.res k K c ≠ 1 := by
  intro h
  apply hne
  rw [hw, Work.SSGRoute.PT.decompK_linked k Ω K c hc2 hc1 φ hlink,
    MonoidHom.map_zpowers, h, Subgroup.zpowers_one_eq_bot]

/-- Every element of `⟨c⟩` is `1` or `c` (for an involution `c`). -/
theorem mem_zpowers_eq_one_or_eq (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) {g : Ω ≃ₐ[k] Ω}
    (hg : g ∈ Subgroup.zpowers c) : g = 1 ∨ g = c := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hg
  have hc2' : c ^ (2 : ℤ) = 1 := by
    have h : c ^ (2 : ℤ) = c ^ (2 : ℕ) := by norm_num
    rw [h, hc2]
  rcases Int.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · left
    rw [← hm, show j + j = 2 * j from by ring, zpow_mul, hc2', one_zpow]
  · right
    rw [← hm, zpow_add, zpow_mul, hc2', one_zpow, one_mul, zpow_one]

/-- The group isomorphism `⟨c⟩ ≃* D_w` sending `g` to `res k K g` (at a linked complex place). -/
noncomputable def ePowLift (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) :
    ↥(Subgroup.zpowers c) ≃* ↥(SSGRoute.PTExt.decompK (k := k) w) := by
  classical
  have hDw : SSGRoute.PTExt.decompK (k := k) w
      = (Subgroup.zpowers c).map (SSGRoute.res k K) := by
    rw [hw]; exact Work.SSGRoute.PT.decompK_linked k Ω K c hc2 hc1 φ hlink
  have hres1 : SSGRoute.res k K c ≠ 1 :=
    res_ne_one_of_decompK_ne_bot (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne
  let f : ↥(Subgroup.zpowers c) →* ↥(SSGRoute.PTExt.decompK (k := k) w) :=
    { toFun := fun g => ⟨SSGRoute.res k K (g : Ω ≃ₐ[k] Ω), by
        rw [hDw]
        exact Subgroup.mem_map.mpr ⟨(g : Ω ≃ₐ[k] Ω), g.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  refine MulEquiv.ofBijective f ⟨fun a b hab => ?_, fun δ => ?_⟩
  · have ha : (a : Ω ≃ₐ[k] Ω) = 1 ∨ (a : Ω ≃ₐ[k] Ω) = c :=
      mem_zpowers_eq_one_or_eq c hc2 a.2
    have hb : (b : Ω ≃ₐ[k] Ω) = 1 ∨ (b : Ω ≃ₐ[k] Ω) = c :=
      mem_zpowers_eq_one_or_eq c hc2 b.2
    have hval : SSGRoute.res k K (a : Ω ≃ₐ[k] Ω) = SSGRoute.res k K (b : Ω ≃ₐ[k] Ω) :=
      congrArg Subtype.val hab
    refine Subtype.ext ?_
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [ha, hb]
    · rw [ha, hb] at hval
      exact (hres1 (by simpa using hval.symm)).elim
    · rw [ha, hb] at hval
      exact (hres1 (by simpa using hval)).elim
    · rw [ha, hb]
  · have hδ : (δ : ↥K ≃ₐ[k] ↥K) ∈ (Subgroup.zpowers c).map (SSGRoute.res k K) := by
      rw [← hDw]; exact δ.2
    obtain ⟨g, hg, hg'⟩ := Subgroup.mem_map.mp hδ
    exact ⟨⟨g, hg⟩, Subtype.ext hg'⟩

end Setup

section Seam

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- **The place-adapted archimedean seam.**  For a complex infinite place `w` of `K` linked to the
involution `c` through `φ` (`hlink`), there is a seam `φ' ∈ {φ, conj ∘ φ}` which realizes the place
embedding `w.embedding` and still intertwines `c` with complex conjugation, and the *fixed*
isomorphism `K_w ≃+* ℂ` of `ringEquivComplexOfIsComplex` carries the canonical embedding `K ↪ K_w`
to `φ'`. -/
theorem exists_seamData (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NumberField.InfinitePlace ↥K)
    (hw : w = NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω)))
    (hne : SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite w) ≠ ⊥) :
    ∃ (φ' : Ω →+* ℂ) (hwC : w.IsComplex),
      (∀ y : ↥K, φ' (algebraMap ↥K Ω y) = NumberField.InfinitePlace.embedding w y) ∧
      (∀ x : Ω, φ' (c x) = starRingEnd ℂ (φ' x)) ∧
      (∀ y : ↥K, (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hwC)
          (algebraMap ↥K (NumberField.InfinitePlace.Completion w) y) =
        φ' (algebraMap ↥K Ω y)) := by
  subst hw
  set ψ : ↥K →+* ℂ := φ.comp (algebraMap ↥K Ω) with hψ
  have hwC : (NumberField.InfinitePlace.mk ψ).IsComplex :=
    Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := ↥K) hne
  have hcoe : ∀ x : ↥K, NumberField.InfinitePlace.Completion.extensionEmbedding
      (NumberField.InfinitePlace.mk ψ)
      (algebraMap ↥K (NumberField.InfinitePlace.Completion (NumberField.InfinitePlace.mk ψ)) x) =
      (NumberField.InfinitePlace.mk ψ).embedding x := by
    intro x
    simp [NumberField.InfinitePlace.Completion.algebraMap_apply,
      NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
  rcases NumberField.InfinitePlace.embedding_mk_eq ψ with hcase | hcase
  · refine ⟨φ, hwC, ?_, hlink, ?_⟩
    · intro y
      rw [hcase, hψ]
      rfl
    · intro y
      rw [NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply, hcoe, hcase, hψ]
      rfl
  · refine ⟨NumberField.ComplexEmbedding.conjugate φ, hwC, ?_, ?_, ?_⟩
    · intro y
      rw [hcase, hψ]
      simp only [NumberField.ComplexEmbedding.conjugate, RingHom.comp_apply]
      rfl
    · intro x
      change starRingEnd ℂ (φ (c x)) = starRingEnd ℂ (starRingEnd ℂ (φ x))
      rw [hlink x]
    · intro y
      rw [NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply, hcoe, hcase]
      simp [NumberField.ComplexEmbedding.conjugate, hψ]

/-- **The representation `Ωˣ` over `D_w` with the action of `δ` given by the lift of `δ` through
`c`** (the lift being the inverse of `res k K` on `⟨c⟩`). -/
noncomputable def omegaRepD (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) :
    Rep.{0} SSGRoute.PTExt.Coeff ↥(SSGRoute.PTExt.decompK (k := k) w) :=
  Rep.res (ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne).symm.toMonoidHom
    (Rep.res (Subgroup.zpowers c).subtype (NK.HassePrinciple.unitsRep k Ω))

/-- The intertwining property of the `Kˣ → Ωˣ` map over `D_w`. -/
theorem iotaSeam_intertwining (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥)
    (δ : ↥(SSGRoute.PTExt.decompK (k := k) w)) (u : (SSGRoute.PTExt.unitsK k K).V) :
    Work.SSGRoute.ExtChain.unitsAddToOmega (k := k) (Ω := Ω) (K := K)
        ((SSGRoute.PTExt.unitsK k K).ρ ((SSGRoute.PTExt.decompK (k := k) w).subtype δ) u)
      = (omegaRepD (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne).ρ δ
          (Work.SSGRoute.ExtChain.unitsAddToOmega (k := k) (Ω := Ω) (K := K) u) := by
  have hσ : SSGRoute.res k K
      ((ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne).symm δ)
      = (δ : ↥K ≃ₐ[k] ↥K) :=
    congrArg Subtype.val
      ((ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne).apply_symm_apply δ)
  have h1 : (omegaRepD (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne).ρ δ
      (Work.SSGRoute.ExtChain.unitsAddToOmega (k := k) (Ω := Ω) (K := K) u)
      = (((ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne).symm δ :
            ↥(Subgroup.zpowers c)) : Ω ≃ₐ[k] Ω) •
          (Work.SSGRoute.ExtChain.unitsAddToOmega (k := k) (Ω := Ω) (K := K) u) := rfl
  rw [h1, Work.SSGRoute.ExtChain.smul_unitsAddToOmega (k := k) (Ω := Ω) (K := K)
    (((ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne).symm δ :
      ↥(Subgroup.zpowers c)) : Ω ≃ₐ[k] Ω) u, hσ]
  rfl

/-- The `Kˣ → Ωˣ` coefficient map over `D_w`, as a morphism of `D_w`-representations. -/
noncomputable def iotaSeam (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) :
    Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (SSGRoute.PTExt.unitsK k K) ⟶
      omegaRepD (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne :=
  Rep.ofHom
    { toFun := fun u => Work.SSGRoute.ExtChain.unitsAddToOmega (k := k) (Ω := Ω) (K := K) u
      map_add' := fun a b =>
        (Work.SSGRoute.ExtChain.unitsAddToOmega (k := k) (Ω := Ω) (K := K)).map_add a b
      map_smul' := fun n u => by
        obtain ⟨z⟩ := n
        exact (Work.SSGRoute.ExtChain.unitsAddToOmega (k := k) (Ω := Ω) (K := K)).map_zsmul z u
      isIntertwining' := fun δ => LinearMap.ext (fun u =>
        iotaSeam_intertwining (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne δ u) }

end Seam

section PsiSeam

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- The infinite place of `K` cut out by the seam `φ`.  (Named so that `omegaRepD` and `ePowLift`
can be instantiated on it with the equation `rfl`, which keeps the seam map transparent.) -/
noncomputable abbrev iPlace (φ : Ω →+* ℂ) : NumberField.InfinitePlace ↥K :=
  NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))

/-- The archimedean place of `K` cut out by the seam `φ`. -/
noncomputable abbrev seamPlace (φ : Ω →+* ℂ) : NK.GlobalCFT.Place ↥K :=
  NK.GlobalCFT.Place.ofInfinite (iPlace (K := K) φ)

/-- `omegaRepD` at the seam place, with the equations supplied by `rfl`. -/
noncomputable abbrev omegaRepDOf (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : SSGRoute.PTExt.decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥) :
    Rep.{0} SSGRoute.PTExt.Coeff ↥(SSGRoute.PTExt.decompK (k := k) (seamPlace (K := K) φ)) :=
  omegaRepD (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne

/-- **The seam map `Ωˣ → K_wˣ = ℂˣ` over `D_w`.**  With the `D_w`-action on `Ωˣ` given by the lift
through `c` (`omegaRepD`) and the honest local action on `K_wˣ`, the map `x ↦ e⁻¹(φ' x)` is
`D_w`-equivariant, by `linkedSeamUnitsMap`. -/
noncomputable def psiSeam (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : SSGRoute.PTExt.decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥)
    (φ' : Ω →+* ℂ) (hC : (iPlace (K := K) φ).IsComplex)
    (hφ'K : ∀ y : ↥K, φ' (algebraMap ↥K Ω y) =
      NumberField.InfinitePlace.embedding (iPlace (K := K) φ) y)
    (hlink' : ∀ x : Ω, φ' (c x) = starRingEnd ℂ (φ' x)) :
    omegaRepDOf (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink hne ⟶
      SSGRoute.PTExt.localUnitsK (k := k) (seamPlace (K := K) φ) := by
  classical
  let eU : (NumberField.InfinitePlace.Completion (iPlace (K := K) φ))ˣ ≃* ℂˣ :=
    Units.mapEquiv (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hC).toMulEquiv
  let LL := SSGRoute.PTExt.localUnitsK (k := k) (seamPlace (K := K) φ)
  let ωR := omegaRepDOf (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink hne
  let EP := ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink
      (seamPlace (K := K) φ) rfl hne
  let g : Ωˣ →* (NumberField.InfinitePlace.Completion (iPlace (K := K) φ))ˣ :=
    (eU.symm.toMonoidHom).comp (Units.map φ'.toMonoidHom)
  let toLoc : ωR.V →+ LL.V :=
    (MonoidHom.toAdditive g).comp (AddMonoidHom.id (Additive Ωˣ))
  refine Rep.ofHom
    { toFun := toLoc
      map_add' := fun a b => toLoc.map_add a b
      map_smul' := fun n v => by
        obtain ⟨z⟩ := n
        exact toLoc.map_zsmul z v
      isIntertwining' := fun δ => LinearMap.ext (fun x => ?_) }
  show toLoc (ωR.ρ δ x) = LL.ρ δ (toLoc x)
  have hσ : SSGRoute.res k K (EP.symm δ) = (δ : ↥K ≃ₐ[k] ↥K) :=
    congrArg Subtype.val (EP.apply_symm_apply δ)
  have hU : Additive.toMul (ωR.ρ δ x)
      = Work.SSGRoute.algEquivUnitsMapΩ k Ω ((EP.symm δ : ↥(Subgroup.zpowers c)) : Ω ≃ₐ[k] Ω)
          (Additive.toMul x) := rfl
  have keyL : Units.map φ'.toMonoidHom (Additive.toMul (ωR.ρ δ x))
      = Units.map (E1aClean.localActionC K (iPlace (K := K) φ) hC δ).toMonoidHom
          (Units.map φ'.toMonoidHom (Additive.toMul x)) := by
    rcases mem_zpowers_eq_one_or_eq c hc2
      ((EP.symm δ : ↥(Subgroup.zpowers c)).2) with h1 | hc
    · -- the lift of `δ` is `1`, hence `δ = 1`
      have h2 : ((EP.symm δ : ↥(Subgroup.zpowers c)) : Ω ≃ₐ[k] Ω) = 1 := h1
      have hδ1 : δ = 1 := by
        apply Subtype.ext
        rw [← hσ]
        simpa using congrArg (SSGRoute.res k K) h2
      have hloc1 : E1aClean.localActionC K (iPlace (K := K) φ) hC
          (1 : ↥(SSGRoute.PTExt.decompK (k := k) (seamPlace (K := K) φ))) = 1 := by
        ext z
        rw [E1aClean.localActionC_apply]
        simp
      rw [hδ1, hloc1, map_one]
      rw [show RingEquiv.toMonoidHom (1 : ℂ ≃+* ℂ) = MonoidHom.id ℂ from rfl]
      simp
    · -- the lift of `δ` is `c`: the seam computes the local action
      exact (congrArg (Units.map φ'.toMonoidHom) hU).trans
        (E1aClean.linkedSeamUnitsMap K (iPlace (K := K) φ) hC δ
          ((EP.symm δ : ↥(Subgroup.zpowers c)) : Ω ≃ₐ[k] Ω) hσ φ' hφ'K
          (fun x => by rw [hc]; exact hlink' x) (Additive.toMul x))
  have keyR : eU (NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
        (seamPlace (K := K) φ) δ
        (eU.symm (Units.map φ'.toMonoidHom (Additive.toMul x))))
      = Units.map (E1aClean.localActionC K (iPlace (K := K) φ) hC δ).toMonoidHom
          (Units.map φ'.toMonoidHom (Additive.toMul x)) := by
    rw [Work.SSGRoute.PTdualControl.localUnitsEquiv_transport (k := k) (K := K)
        (iPlace (K := K) φ) hC δ
      (eU.symm (Units.map φ'.toMonoidHom (Additive.toMul x))), MulEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  have hL2 : Additive.toMul (toLoc (ωR.ρ δ x))
      = eU.symm (Units.map φ'.toMonoidHom (Additive.toMul (ωR.ρ δ x))) := rfl
  have hR2 : Additive.toMul (LL.ρ δ (toLoc x))
      = NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
          (seamPlace (K := K) φ) δ
          (eU.symm (Units.map φ'.toMonoidHom (Additive.toMul x))) := by
    have h4 : LL.ρ δ (toLoc x)
        = Additive.ofMul ((NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K)
            (seamPlace (K := K) φ) δ) (Additive.toMul (toLoc x))) := rfl
    rw [h4]
    rfl
  rw [hL2, hR2]
  apply eU.injective
  rw [MulEquiv.apply_symm_apply, keyL, keyR]

/-- Value rule of the seam: on units it is `x ↦ e⁻¹ (φ' x)`. -/
lemma psiSeam_toMul (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : SSGRoute.PTExt.decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥)
    (φ' : Ω →+* ℂ) (hC : (iPlace (K := K) φ).IsComplex)
    (hφ'K : ∀ y : ↥K, φ' (algebraMap ↥K Ω y) =
      NumberField.InfinitePlace.embedding (iPlace (K := K) φ) y)
    (hlink' : ∀ x : Ω, φ' (c x) = starRingEnd ℂ (φ' x))
    (x : (omegaRepDOf (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink hne).V) :
    Additive.toMul (Rep.Hom.hom (psiSeam (k := k) (Ω := Ω) (K := K)
        c hc2 hc1 φ hlink hne φ' hC hφ'K hlink') x)
      = (Units.mapEquiv
          (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hC).toMulEquiv).symm
          (Units.map φ'.toMonoidHom (Additive.toMul x)) := rfl

/-- Value rule of the coefficient map `Kˣ → Ωˣ`. -/
lemma iotaSeam_apply (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) (u : (SSGRoute.PTExt.unitsK k K).V) :
    Rep.Hom.hom (iotaSeam (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink w hw hne) u
      = Work.SSGRoute.ExtChain.unitsAddToOmega (k := k) (Ω := Ω) (K := K) u := rfl

/-- The seam map is injective (i.e. a monomorphism). -/
lemma psiSeam_mono (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : SSGRoute.PTExt.decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥)
    (φ' : Ω →+* ℂ) (hC : (iPlace (K := K) φ).IsComplex)
    (hφ'K : ∀ y : ↥K, φ' (algebraMap ↥K Ω y) =
      NumberField.InfinitePlace.embedding (iPlace (K := K) φ) y)
    (hlink' : ∀ x : Ω, φ' (c x) = starRingEnd ℂ (φ' x)) :
    Mono (psiSeam (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink hne φ' hC hφ'K hlink') := by
  rw [Rep.mono_iff_injective]
  intro x y hxy
  have hxy' : Additive.toMul ((psiSeam (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink hne
        φ' hC hφ'K hlink') x)
      = Additive.toMul ((psiSeam (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink hne
        φ' hC hφ'K hlink') y) := congrArg Additive.toMul hxy
  rw [psiSeam_toMul (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink hne φ' hC hφ'K hlink' x,
    psiSeam_toMul (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink hne φ' hC hφ'K hlink' y] at hxy'
  have h1 : Units.map φ'.toMonoidHom (Additive.toMul x)
      = Units.map φ'.toMonoidHom (Additive.toMul y) :=
    (Units.mapEquiv
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hC).toMulEquiv).symm.injective
      hxy'
  exact Additive.toMul.injective (Units.map_injective φ'.injective h1)

/-- **The coefficient triangle**, pointwise: the localisation of the global units at the seam is the
seam composed with `Kˣ → Ωˣ`. -/
lemma iotaSeam_psiSeam_apply (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : SSGRoute.PTExt.decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥)
    (φ' : Ω →+* ℂ) (hC : (iPlace (K := K) φ).IsComplex)
    (hφ'K : ∀ y : ↥K, φ' (algebraMap ↥K Ω y) =
      NumberField.InfinitePlace.embedding (iPlace (K := K) φ) y)
    (hlink' : ∀ x : Ω, φ' (c x) = starRingEnd ℂ (φ' x))
    (v : (↥K)ˣ) :
    Rep.Hom.hom (psiSeam (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink hne φ' hC hφ'K hlink')
        (Work.SSGRoute.ExtChain.unitsAddToOmega (k := k) (Ω := Ω) (K := K) (Additive.ofMul v))
      = Rep.Hom.hom (NK.HassePrinciple.unitsToLocalUnits k ↥K (seamPlace (K := K) φ))
          (Additive.ofMul v) := by
  have hu : Additive.toMul (Work.SSGRoute.ExtChain.unitsAddToOmega (k := k) (Ω := Ω) (K := K)
        (Additive.ofMul v)) = Work.SSGRoute.unitsMapK (k := k) (Ω := Ω) (K := K) v := rfl
  have hU : Additive.toMul (Rep.Hom.hom (NK.HassePrinciple.unitsToLocalUnits k ↥K
        (seamPlace (K := K) φ)) (Additive.ofMul v))
      = NK.HassePrinciple.unitsToLocalUnitsHom (seamPlace (K := K) φ) v := rfl
  have heK : ∀ y : ↥K, NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hC
      (algebraMap ↥K (NumberField.InfinitePlace.Completion (iPlace (K := K) φ)) y)
      = NumberField.InfinitePlace.embedding (iPlace (K := K) φ) y := by
    intro y
    simp [NumberField.InfinitePlace.Completion.algebraMap_apply,
      NumberField.InfinitePlace.Completion.extensionEmbedding_coe]
  have h1 : Units.map φ'.toMonoidHom (Work.SSGRoute.unitsMapK (k := k) (Ω := Ω) (K := K) v)
      = Units.map (NumberField.InfinitePlace.embedding (iPlace (K := K) φ)).toMonoidHom v := by
    have hcomp : (φ'.toMonoidHom.comp ((algebraMap ↥K Ω).toMonoidWithZeroHom : ↥K →* Ω))
        = (NumberField.InfinitePlace.embedding (iPlace (K := K) φ)).toMonoidHom :=
      MonoidHom.ext (fun y => hφ'K y)
    show Units.map (φ'.toMonoidHom.comp ((algebraMap ↥K Ω).toMonoidWithZeroHom : ↥K →* Ω)) v
      = Units.map (NumberField.InfinitePlace.embedding (iPlace (K := K) φ)).toMonoidHom v
    rw [hcomp]
  have h2 : (Units.mapEquiv
        (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hC).toMulEquiv)
        (Units.map ((algebraMap ↥K (NumberField.InfinitePlace.Completion
          (iPlace (K := K) φ))).toMonoidHom) v)
      = Units.map (NumberField.InfinitePlace.embedding (iPlace (K := K) φ)).toMonoidHom v := by
    apply Units.ext
    simp only [Units.coe_mapEquiv, Units.coe_map]
    exact heK (v : ↥K)
  apply Additive.toMul.injective
  rw [psiSeam_toMul (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink hne φ' hC hφ'K hlink'
      (Work.SSGRoute.ExtChain.unitsAddToOmega (k := k) (Ω := Ω) (K := K) (Additive.ofMul v))]
  rw [hu, hU]
  apply (Units.mapEquiv
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hC).toMulEquiv).injective
  rw [MulEquiv.apply_symm_apply]
  rw [show NK.HassePrinciple.unitsToLocalUnitsHom (seamPlace (K := K) φ) v
      = Units.map ((algebraMap ↥K (NumberField.InfinitePlace.Completion
          (iPlace (K := K) φ))).toMonoidHom) v from rfl]
  rw [h2]
  exact h1

/-- **The coefficient triangle**: the localisation of the global units is the seam composed with
`Kˣ → Ωˣ`.  This is the identity that lets the vanishing of the localised class be transported to
the `Ωˣ`-valued coefficient. -/
lemma iotaSeam_psiSeam (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (φ : Ω →+* ℂ) (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : SSGRoute.PTExt.decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥)
    (φ' : Ω →+* ℂ) (hC : (iPlace (K := K) φ).IsComplex)
    (hφ'K : ∀ y : ↥K, φ' (algebraMap ↥K Ω y) =
      NumberField.InfinitePlace.embedding (iPlace (K := K) φ) y)
    (hlink' : ∀ x : Ω, φ' (c x) = starRingEnd ℂ (φ' x)) :
    iotaSeam (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne ≫
      psiSeam (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink hne φ' hC hφ'K hlink'
    = NK.HassePrinciple.unitsToLocalUnits k ↥K (seamPlace (K := K) φ) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro u
  show Rep.Hom.hom (psiSeam (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink hne
      φ' hC hφ'K hlink')
      (Work.SSGRoute.ExtChain.unitsAddToOmega (k := k) (Ω := Ω) (K := K) u)
    = Rep.Hom.hom (NK.HassePrinciple.unitsToLocalUnits k ↥K (seamPlace (K := K) φ)) u
  exact iotaSeam_psiSeam_apply (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink hne
    φ' hC hφ'K hlink' (Additive.toMul u)

end PsiSeam


end Work.SSGRoute.ArchDictionary
