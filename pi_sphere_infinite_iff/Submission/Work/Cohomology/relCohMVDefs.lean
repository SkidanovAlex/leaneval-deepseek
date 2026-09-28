import Mathlib
import Submission.Work.Cohomology.RelMVDefs
import Submission.Work.Cohomology.relMV_shortExact
import Submission.Work.Cohomology.DualComplex
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.Cohomology.relSmallCochains_iso
import Submission.Work.Cohomology.mvCochainDefs
import Submission.Work.Cohomology.isIso_biprod_lift_dualMap
import Submission.Work.Cohomology.mvCochainG_ker_le_range
import Submission.Work.Cohomology.mvCochainG_surjective

/-!
# The relative Mayer–Vietoris short exact sequence of cochain complexes: definitions

The chain level relative Mayer–Vietoris sequence
(`Work.Cohomology.relMV_shortExact`)

`0 ⟶ C^{U,V}(U ∩ V, U ∩ V ∩ A) --f--> C^{U,V}(U, U ∩ A) ⊞ C^{U,V}(V, V ∩ A) --g--> C^{U,V}(X,A) ⟶ 0`

dualises (`Work.Cohomology.dualComplex`) to the sequence of cochain complexes

`0 ⟶ C^*(X,A) ⟶ C^*(U, U ∩ A) ⊞ C^*(V, V ∩ A) ⟶ C^*(U ∩ V, U ∩ V ∩ A) ⟶ 0`

which is the relative Mayer–Vietoris sequence of the problem statement
`Work.Cohomology.relCohMV_shortExact`.

Because `relMV_shortExact` is an existence statement, the two chain maps are fixed here by
`Classical.choose` (`relMVChainLeft`, `relMVChainRight`, `relMVChainZero`, `relMVChainShortExact`)
and their components along the biproduct projections/inclusions are named
(`relMVChainBeta₁`, `relMVChainBeta₂`, `relMVChainAlpha₁`, `relMVChainAlpha₂`).  The dual maps

`relCohMVF = biprod.lift (dual α₁) (dual α₂)`, `relCohMVG = biprod.desc (dual β₁) (dual β₂)`

are then morphisms of cochain complexes with `relCohMVF ≫ relCohMVG = 0`
(`relCohMV_comp`), and the target of `relCohMV_shortExact` is the short exactness of this short
complex.

This file also records the degreewise consequences of `relMV_shortExact` used by the proof:
the degreewise injectivity of the first chain map (`relMVChainDegreewise_injective`), the
degreewise surjectivity of the second one (`relMVChainDegreewise_surjective`) and the degreewise
identification of its kernel with the range of the first one (`relMVChainDegreewise_ker`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

open DualBiprod

/-! ## Generic helper lemmas on transposes and on the dual complex -/

/-- The transpose of a sum of linear maps is the sum of the transposes. -/
lemma dualMap_add_z {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] (f g : M →ₗ[R] N) :
    (f + g).dualMap = f.dualMap + g.dualMap := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  simp only [LinearMap.dualMap_apply, LinearMap.add_apply, map_add]

/-- The transpose of the zero linear map is zero. -/
lemma dualMap_zero_z {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] :
    (0 : M →ₗ[R] N).dualMap = 0 := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  simp only [LinearMap.dualMap_apply, LinearMap.zero_apply, map_zero]

/-- The dual of the zero chain map is the zero cochain map. -/
theorem dualComplexMap_zero (R : Type) [CommRing R] {C D : ChainComplex (ModuleCat R) ℕ} :
    dualComplexMap R C D 0 = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  simp only [dualComplexMap_f, dualComplexMapComp, HomologicalComplex.zero_f, ModuleCat.hom_ofHom,
    ModuleCat.hom_zero, dualMap_zero_z]

/-- The dual of a sum of chain maps is the sum of the duals. -/
theorem dualComplexMap_add (R : Type) [CommRing R] {C D : ChainComplex (ModuleCat R) ℕ}
    (f g : C ⟶ D) :
    dualComplexMap R C D (f + g) = dualComplexMap R C D f + dualComplexMap R C D g := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.add_f_apply]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_add]
  simp only [dualComplexMap_f, dualComplexMapComp, ModuleCat.hom_ofHom, ModuleCat.hom_add,
    HomologicalComplex.add_f_apply, dualMap_add_z]

/-- **Decomposition of an element of the degree-`n` part of a biproduct of chain complexes**
into its two components. -/
theorem biprodTotal_apply_chain (K L : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ)
    (x : (K ⊞ L).X n) :
    (biprod.inl : K ⟶ K ⊞ L).f n ((biprod.fst : K ⊞ L ⟶ K).f n x)
      + (biprod.inr : L ⟶ K ⊞ L).f n ((biprod.snd : K ⊞ L ⟶ L).f n x) = x := by
  have htot := HomologicalComplex.biprod_total_f (K := K) (L := L) n
  have h := congrArg (fun (f : (K ⊞ L).X n ⟶ (K ⊞ L).X n) => f x) htot
  simpa only [ModuleCat.hom_add, LinearMap.add_apply, ConcreteCategory.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] using h

/-- Two elements of the degree-`n` part of a biproduct of chain complexes agree as soon as their
two components do. -/
theorem biprodExt_apply_chain (K L : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) {x y : (K ⊞ L).X n}
    (h₁ : (biprod.fst : K ⊞ L ⟶ K).f n x = (biprod.fst : K ⊞ L ⟶ K).f n y)
    (h₂ : (biprod.snd : K ⊞ L ⟶ L).f n x = (biprod.snd : K ⊞ L ⟶ L).f n y) : x = y := by
  rw [← biprodTotal_apply_chain K L n x, ← biprodTotal_apply_chain K L n y, h₁, h₂]

/-! ## The transpose of a composite, applied -/

/-- The transpose of a composite of module morphisms, evaluated on a functional. -/
lemma dualMapHom_comp_apply {A B C : ModuleCat ℤ} (f : A ⟶ B) (g : B ⟶ C)
    (φ : ↥(DualBiprod.dualObj C)) :
    (dualMapHom f).hom ((dualMapHom g).hom φ) = (dualMapHom (f ≫ g)).hom φ := by
  rw [dualMapHom_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- The transpose of a sum of module morphisms, evaluated on a functional. -/
lemma dualMapHom_add_apply {A B : ModuleCat ℤ} (f g : A ⟶ B) (φ : ↥(DualBiprod.dualObj B)) :
    (dualMapHom (f + g)).hom φ = (dualMapHom f).hom φ + (dualMapHom g).hom φ := by
  rw [dualMapHom_add, ModuleCat.hom_add, LinearMap.add_apply]

/-- The transpose of the identity, evaluated on a functional. -/
lemma dualMapHom_id_apply {A : ModuleCat ℤ} (φ : ↥(DualBiprod.dualObj A)) :
    (dualMapHom (𝟙 A)).hom φ = φ := by
  rw [dualMapHom_id, ModuleCat.hom_id, LinearMap.id_apply]

/-! ## The chain level relative Mayer–Vietoris sequence -/


variable (X : TopCat) (A U V : Set X)

/-- The first term of the relative Mayer–Vietoris sequence:
`C^{U,V}(U ∩ V, U ∩ V ∩ A)`. -/
abbrev relMVUV : ChainComplex (ModuleCat ℤ) ℕ :=
  relSmallChains U V (U ∩ V) (U ∩ V ∩ A) Set.inter_subset_left

/-- The `U`-part of the middle term: `C^{U,V}(U, U ∩ A)`. -/
abbrev relMVUU : ChainComplex (ModuleCat ℤ) ℕ :=
  relSmallChains U V U (U ∩ A) Set.inter_subset_left

/-- The `V`-part of the middle term: `C^{U,V}(V, V ∩ A)`. -/
abbrev relMVVV : ChainComplex (ModuleCat ℤ) ℕ :=
  relSmallChains U V V (V ∩ A) Set.inter_subset_left

/-- The last term of the relative Mayer–Vietoris sequence: `C^{U,V}(X,A)`. -/
abbrev relMVTopC : ChainComplex (ModuleCat ℤ) ℕ := relSmallTop U V A

/-- The first map of the chain level relative Mayer–Vietoris sequence. -/
noncomputable def relMVChainLeft : relMVUV X A U V ⟶ relMVUU X A U V ⊞ relMVVV X A U V :=
  Classical.choose (relMV_shortExact X A U V)

/-- The second map of the chain level relative Mayer–Vietoris sequence. -/
noncomputable def relMVChainRight : relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVTopC X A U V :=
  Classical.choose (Classical.choose_spec (relMV_shortExact X A U V))

/-- The two chain level relative Mayer–Vietoris maps compose to zero. -/
theorem relMVChainZero : relMVChainLeft X A U V ≫ relMVChainRight X A U V = 0 :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (relMV_shortExact X A U V)))

/-- **The chain level relative Mayer–Vietoris sequence is short exact.** -/
theorem relMVChainShortExact :
    (ShortComplex.mk (relMVChainLeft X A U V) (relMVChainRight X A U V)
      (relMVChainZero X A U V)).ShortExact :=
  Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (relMV_shortExact X A U V)))

/-- The `U`-component of the first chain map: `C^{U,V}(U ∩ V, U ∩ V ∩ A) ⟶ C^{U,V}(U, U ∩ A)`. -/
noncomputable def relMVChainBeta₁ : relMVUV X A U V ⟶ relMVUU X A U V :=
  relMVChainLeft X A U V ≫ biprod.fst

/-- The `V`-component of the first chain map. -/
noncomputable def relMVChainBeta₂ : relMVUV X A U V ⟶ relMVVV X A U V :=
  relMVChainLeft X A U V ≫ biprod.snd

/-- The `U`-component of the second chain map: `C^{U,V}(U, U ∩ A) ⟶ C^{U,V}(X,A)`. -/
noncomputable def relMVChainAlpha₁ : relMVUU X A U V ⟶ relMVTopC X A U V :=
  biprod.inl ≫ relMVChainRight X A U V

/-- The `V`-component of the second chain map. -/
noncomputable def relMVChainAlpha₂ : relMVVV X A U V ⟶ relMVTopC X A U V :=
  biprod.inr ≫ relMVChainRight X A U V

/-- The first chain map is the lift of its two components. -/
theorem relMVChainLeft_eq_lift :
    relMVChainLeft X A U V = biprod.lift (relMVChainBeta₁ X A U V) (relMVChainBeta₂ X A U V) := by
  refine biprod.hom_ext _ _ ?_ ?_ <;> simp [relMVChainBeta₁, relMVChainBeta₂]

/-- The second chain map is the desc of its two components. -/
theorem relMVChainRight_eq_desc :
    relMVChainRight X A U V = biprod.desc (relMVChainAlpha₁ X A U V) (relMVChainAlpha₂ X A U V) := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [relMVChainAlpha₁, relMVChainAlpha₂]

/-- The components of the chain level relative Mayer–Vietoris maps satisfy
`β₁ ≫ α₁ + β₂ ≫ α₂ = 0`. -/
theorem relMVChain_alpha_beta_zero :
    relMVChainBeta₁ X A U V ≫ relMVChainAlpha₁ X A U V
      + relMVChainBeta₂ X A U V ≫ relMVChainAlpha₂ X A U V = 0 := by
  rw [← (biprod.lift_desc (f := relMVChainBeta₁ X A U V) (g := relMVChainBeta₂ X A U V)
      (h := relMVChainAlpha₁ X A U V) (i := relMVChainAlpha₂ X A U V)),
    ← relMVChainLeft_eq_lift X A U V, ← relMVChainRight_eq_desc X A U V]
  exact relMVChainZero X A U V

/-! ## The dualised sequence -/

/-- **The first map of the relative cohomological Mayer–Vietoris sequence**,
`C^*(X,A) ⟶ C^*(U, U ∩ A) ⊞ C^*(V, V ∩ A)`: the dual of `(α₁, α₂)`. -/
noncomputable def relCohMVF :
    dualComplex ℤ (relMVTopC X A U V) ⟶
      dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V) :=
  biprod.lift (dualComplexMap ℤ (relMVUU X A U V) (relMVTopC X A U V) (relMVChainAlpha₁ X A U V))
    (dualComplexMap ℤ (relMVVV X A U V) (relMVTopC X A U V) (relMVChainAlpha₂ X A U V))

/-- **The second map of the relative cohomological Mayer–Vietoris sequence**,
`C^*(U, U ∩ A) ⊞ C^*(V, V ∩ A) ⟶ C^*(U ∩ V, U ∩ V ∩ A)`: the dual of `(β₁, β₂)`. -/
noncomputable def relCohMVG :
    dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V) ⟶
      dualComplex ℤ (relMVUV X A U V) :=
  biprod.desc (dualComplexMap ℤ (relMVUV X A U V) (relMVUU X A U V) (relMVChainBeta₁ X A U V))
    (dualComplexMap ℤ (relMVUV X A U V) (relMVVV X A U V) (relMVChainBeta₂ X A U V))

/-- **The relative cohomological Mayer–Vietoris maps compose to zero.** -/
theorem relCohMV_comp : relCohMVF X A U V ≫ relCohMVG X A U V = 0 := by
  rw [relCohMVF, relCohMVG, biprod.lift_desc, ← dualComplexMap_comp, ← dualComplexMap_comp,
    ← dualComplexMap_add, relMVChain_alpha_beta_zero, dualComplexMap_zero]

/-- The short complex of cochain complexes whose short exactness is
`Work.Cohomology.relCohMV_shortExact`. -/
noncomputable def relCohMVShortComplex :
    ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (relCohMVF X A U V) (relCohMVG X A U V) (relCohMV_comp X A U V)

/-! ## The degreewise components of the maps -/

/-- The `U`-component of the dualised first map is the transpose of `α₁`. -/
theorem relCohMVF_fst (n : ℕ) :
    (relCohMVF X A U V).f n ≫ (biprod.fst :
        dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V) ⟶
          dualComplex ℤ (relMVUU X A U V)).f n
      = dualMapHom ((relMVChainAlpha₁ X A U V).f n) := by
  rw [relCohMVF, HomologicalComplex.biprod_lift_fst_f]
  rfl

/-- The `V`-component of the dualised first map is the transpose of `α₂`. -/
theorem relCohMVF_snd (n : ℕ) :
    (relCohMVF X A U V).f n ≫ (biprod.snd :
        dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V) ⟶
          dualComplex ℤ (relMVVV X A U V)).f n
      = dualMapHom ((relMVChainAlpha₂ X A U V).f n) := by
  rw [relCohMVF, HomologicalComplex.biprod_lift_snd_f]
  rfl

/-- The `U`-component of the dualised second map is the transpose of `β₁`. -/
theorem relCohMVG_inl (n : ℕ) :
    (biprod.inl : dualComplex ℤ (relMVUU X A U V) ⟶
        dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).f n
        ≫ (relCohMVG X A U V).f n
      = dualMapHom ((relMVChainBeta₁ X A U V).f n) := by
  rw [relCohMVG, HomologicalComplex.biprod_inl_desc_f]
  rfl

/-- The `V`-component of the dualised second map is the transpose of `β₂`. -/
theorem relCohMVG_inr (n : ℕ) :
    (biprod.inr : dualComplex ℤ (relMVVV X A U V) ⟶
        dualComplex ℤ (relMVUU X A U V) ⊞ dualComplex ℤ (relMVVV X A U V)).f n
        ≫ (relCohMVG X A U V).f n
      = dualMapHom ((relMVChainBeta₂ X A U V).f n) := by
  rw [relCohMVG, HomologicalComplex.biprod_inr_desc_f]
  rfl

/-! ## The degreewise components of the chain level maps -/

/-- The `U`-component of the first chain map, degreewise. -/
theorem relMVChainBeta₁_f (n : ℕ) :
    (relMVChainBeta₁ X A U V).f n
      = (relMVChainLeft X A U V).f n
        ≫ (biprod.fst : relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVUU X A U V).f n := by
  rw [relMVChainBeta₁, HomologicalComplex.comp_f]

/-- The `V`-component of the first chain map, degreewise. -/
theorem relMVChainBeta₂_f (n : ℕ) :
    (relMVChainBeta₂ X A U V).f n
      = (relMVChainLeft X A U V).f n
        ≫ (biprod.snd : relMVUU X A U V ⊞ relMVVV X A U V ⟶ relMVVV X A U V).f n := by
  rw [relMVChainBeta₂, HomologicalComplex.comp_f]

/-- The `U`-component of the second chain map, degreewise. -/
theorem relMVChainAlpha₁_f (n : ℕ) :
    (relMVChainAlpha₁ X A U V).f n
      = (biprod.inl : relMVUU X A U V ⟶ relMVUU X A U V ⊞ relMVVV X A U V).f n
        ≫ (relMVChainRight X A U V).f n := by
  rw [relMVChainAlpha₁, HomologicalComplex.comp_f]

/-- The `V`-component of the second chain map, degreewise. -/
theorem relMVChainAlpha₂_f (n : ℕ) :
    (relMVChainAlpha₂ X A U V).f n
      = (biprod.inr : relMVVV X A U V ⟶ relMVUU X A U V ⊞ relMVVV X A U V).f n
        ≫ (relMVChainRight X A U V).f n := by
  rw [relMVChainAlpha₂, HomologicalComplex.comp_f]

/-! ## Degreewise short exactness of the chain level sequence -/

/-- The degreewise part of the chain level relative Mayer–Vietoris sequence. -/
noncomputable def relMVChainDegreewise (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  (ShortComplex.mk (relMVChainLeft X A U V) (relMVChainRight X A U V) (relMVChainZero X A U V)).map
    (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)

/-- **The chain level relative Mayer–Vietoris sequence is degreewise short exact.** -/
theorem relMVChainDegreewise_shortExact (n : ℕ) :
    (relMVChainDegreewise X A U V n).ShortExact := by
  have hS := relMVChainShortExact X A U V
  have h1 : Mono ((relMVChainLeft X A U V).f n) := by
    haveI : Mono (relMVChainLeft X A U V) := hS.mono_f
    infer_instance
  have h2 : Epi ((relMVChainRight X A U V).f n) := by
    haveI : Epi (relMVChainRight X A U V) := hS.epi_g
    infer_instance
  have h3 : Mono ((HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
      (relMVChainLeft X A U V)) := h1
  have h4 : Epi ((HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n).map
      (relMVChainRight X A U V)) := h2
  haveI := h3
  haveI := h4
  exact hS.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.down ℕ) n)

/-- The first chain map of the relative Mayer–Vietoris sequence is degreewise injective. -/
theorem relMVChainDegreewise_injective (n : ℕ) :
    Function.Injective (ModuleCat.Hom.hom ((relMVChainLeft X A U V).f n)) := by
  have h : Mono (relMVChainDegreewise X A U V n).f :=
    (relMVChainDegreewise_shortExact X A U V n).mono_f
  rw [show (relMVChainDegreewise X A U V n).f = (relMVChainLeft X A U V).f n from
    HomologicalComplex.eval_map (ModuleCat ℤ) (ComplexShape.down ℕ) n (relMVChainLeft X A U V)] at h
  exact (ModuleCat.mono_iff_injective _).1 h

/-- The second chain map of the relative Mayer–Vietoris sequence is degreewise surjective. -/
theorem relMVChainDegreewise_surjective (n : ℕ) :
    Function.Surjective (ModuleCat.Hom.hom ((relMVChainRight X A U V).f n)) := by
  have h : Epi (relMVChainDegreewise X A U V n).g :=
    (relMVChainDegreewise_shortExact X A U V n).epi_g
  rw [show (relMVChainDegreewise X A U V n).g = (relMVChainRight X A U V).f n from
    HomologicalComplex.eval_map (ModuleCat ℤ) (ComplexShape.down ℕ) n
      (relMVChainRight X A U V)] at h
  exact (ModuleCat.epi_iff_surjective _).1 h

/-- **Degreewise exactness of the chain level relative Mayer–Vietoris sequence.** -/
theorem relMVChainDegreewise_ker (n : ℕ) :
    LinearMap.ker (ModuleCat.Hom.hom ((relMVChainRight X A U V).f n))
      = LinearMap.range (ModuleCat.Hom.hom ((relMVChainLeft X A U V).f n)) := by
  have hS := relMVChainDegreewise_shortExact X A U V n
  have hd : (relMVChainDegreewise X A U V n).f ≫ (relMVChainDegreewise X A U V n).g = 0 :=
    (relMVChainDegreewise X A U V n).zero
  have hf : (relMVChainDegreewise X A U V n).f = (relMVChainLeft X A U V).f n :=
    HomologicalComplex.eval_map (ModuleCat ℤ) (ComplexShape.down ℕ) n (relMVChainLeft X A U V)
  have hg : (relMVChainDegreewise X A U V n).g = (relMVChainRight X A U V).f n :=
    HomologicalComplex.eval_map (ModuleCat ℤ) (ComplexShape.down ℕ) n (relMVChainRight X A U V)
  have hker : ∀ x, (ModuleCat.Hom.hom ((relMVChainRight X A U V).f n)) x = 0 →
      ∃ y, (ModuleCat.Hom.hom ((relMVChainLeft X A U V).f n)) y = x := by
    intro x hx
    rw [← hg] at hx
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff (relMVChainDegreewise X A U V n)).1
      hS.exact x hx
    exact ⟨y, by rw [← hf]; exact hy⟩
  refine le_antisymm (fun x hx => ?_) ?_
  · rw [LinearMap.mem_ker] at hx
    obtain ⟨y, hy⟩ := hker x hx
    exact LinearMap.mem_range.mpr ⟨y, hy⟩
  · rintro x ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    have h2 := congrArg ModuleCat.Hom.hom hd
    rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
    rw [hf, hg] at h2
    exact LinearMap.congr_fun h2 y

end

end Work.Cohomology
