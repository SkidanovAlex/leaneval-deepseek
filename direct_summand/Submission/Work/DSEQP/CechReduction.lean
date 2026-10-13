/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reduction of the equal characteristic `p` area statement to the Čech model

The frozen area statement `DSMap.area_EQP` asks for `DSMap.DSplit A X f` for `A` a complete
regular local ring of characteristic `p` and `X → Spec A` proper, surjective, generically
finite and projective.  The equal characteristic `p` proof (proof map §4(a)) runs through the
Čech complex of a finite affine cover: the obstruction to splitting becomes an ideal of `A`
(the set of values of degree-`0` functionals on the class of `1`), and the Frobenius/perfection
argument shows that this ideal is the unit ideal.

This file formalises the *reduction* to that Čech model:

* `coaugIdeal A X f U cc` : the obstruction ideal, i.e. the set of values `φ₀ (cc.f 0 1)`
  for `A`-linear functionals `φ₀` on the degree-`0` part of the Čech complex;
* `mem_coaugIdeal_iff` : `1 ∈ coaugIdeal` iff some degree-`0` functional sends the
  coaugmentation class to `1`;
* `isSplitMono_of_one_mem_coaugIdeal` : `1 ∈ coaugIdeal` ⟹ `IsSplitMono (rgUnit A X f)`,
  using `exists_chainMap_retraction_of_functional` (a degree-`0` functional extends to a chain
  map `Č → A[0]` because the Čech complex vanishes in negative degrees) and the chain-model
  criterion `Work.DSEQ0.isSplitMono_of_chainModel`;
* `one_mem_coaugIdeal_of_forall_pthRoot` : the **descent** step of the char-`p` argument:
  if some nonzero element of the obstruction ideal acquires all its `p^e`-th roots inside
  `I·S` after base change to a faithfully flat `A`-algebra `S`, then `1 ∈ I`.

What is *not* here: the production of the almost splitting over the perfection (the Frobenius
twist applied to the cohomology of the perfected Čech complex, using COH), which is the
remaining mathematical input; and the Čech model itself (area `F1`).
-/
import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map
import Submission.Work.DSEQ0.Model
import Submission.Work.DSEQP.Basic
import Submission.Work.DSEQP.Descent
import Submission.Work.DSEQP.exists_chainMap_retraction_of_functional

open CategoryTheory AlgebraicGeometry Limits
open scoped TensorProduct

namespace Work.DSEQP

universe u w₁ w₂

/-- Evaluation of a degree-`0` functional on the Čech complex at the class of `1` under the
coaugmentation `cc`. -/
noncomputable def coaugEval (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens)
    (cc : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
      DSMap.cechZ A X f U) :
    ((DSMap.cechZ A X f U).X 0 ⟶ ModuleCat.of A A) →ₗ[A] A where
  toFun φ₀ := φ₀ (cc.f 0 (1 : A))
  map_add' φ ψ := by simp
  map_smul' a φ := by simp

/-- **The obstruction ideal** of the Čech model: the set of values `φ₀ (cc.f 0 1)` of
`A`-linear functionals `φ₀` on the degree-`0` part of the Čech complex `Č(U; 𝒪_X)`.

This is the ideal whose being the unit ideal is *equivalent* to the splitting of the
coaugmentation `cc : A[0] ⟶ Č(U; 𝒪_X)` in the category of complexes. -/
noncomputable def coaugIdeal (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens)
    (cc : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
      DSMap.cechZ A X f U) : Ideal A :=
  (coaugEval A X f U cc).range

theorem mem_coaugIdeal_iff (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens)
    (cc : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
      DSMap.cechZ A X f U) {a : A} :
    a ∈ coaugIdeal A X f U cc ↔ ∃ φ₀ : (DSMap.cechZ A X f U).X 0 ⟶ ModuleCat.of A A,
      φ₀ (cc.f 0 (1 : A)) = a :=
  LinearMap.mem_range

/-- The Čech complex vanishes in negative degrees; this is what lets `mkHomToSingle` extend
every degree-`0` functional to a chain map `Č → A[0]`. -/
theorem isZero_cechZ_neg_one (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    {ι : Type u} (U : ι → X.Opens) : IsZero ((DSMap.cechZ A X f U).X (-1)) := by
  have h : DSMap.cechZ A X f U = (DSMap.cech A X f U).extend ComplexShape.embeddingUpNat := rfl
  rw [h]
  refine HomologicalComplex.isZero_extend_X _ _ _ ?_
  intro i hi
  have h2 : ((i : ℤ)) = -1 := hi
  omega

/-- **From the obstruction ideal to the splitting.**  Suppose the frozen `DSMap.area_F1_cech`
provides the Čech model: a finite affine cover `U`, the coaugmentation `cc` and the isomorphism
`e` intertwining the challenge unit with `cc` (the hypotheses are exactly the conclusion of
`DSMap.area_F1_cech`).  If some degree-`0` functional sends the coaugmentation class to `1`,
then the challenge unit `rgUnit A X f` is a split monomorphism.

Proof: such a functional extends to a chain map `φ : Č → A[0]` (the Čech complex is zero in
negative degrees), `φ` retracts `cc` on the chain level, and `Work.DSEQ0.isSplitMono_of_chainModel`
transports that retraction to the derived category along `e`. -/
theorem isSplitMono_of_one_mem_coaugIdeal (A : Type u) [CommRing A]
    (h₁ : HasDerivedCategory.{w₁} (ModuleCat.{u} A))
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (h₂ : HasDerivedCategory.{w₂} (SheafOfModules X.ringCatSheaf))
    (h₃ : EnoughInjectives (SheafOfModules X.ringCatSheaf))
    {ι : Type u} (U : ι → X.Opens)
    (cc : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
      DSMap.cechZ A X f U)
    (e : DerivedCategory.Plus.ι.obj (DSMap.RG A X f) ≅
      DerivedCategory.Q.obj (DSMap.cechZ A X f U))
    (he : DerivedCategory.Plus.ι.map (DSMap.rgUnit A X f) ≫ e.hom =
      (DerivedCategory.Plus.singleFunctorιIso (ModuleCat.{u} A) 0).hom.app (ModuleCat.of A A) ≫
        (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).hom.app (ModuleCat.of A A) ≫
          DerivedCategory.Q.map cc)
    (h1 : (1 : A) ∈ coaugIdeal A X f U cc) :
    IsSplitMono (DSMap.rgUnit A X f) := by
  letI := h₁
  letI := h₂
  letI := h₃
  obtain ⟨φ₀, hφ₀⟩ := (mem_coaugIdeal_iff A X f U cc).mp h1
  obtain ⟨φ, hφ⟩ := exists_chainMap_retraction_of_functional (DSMap.cechZ A X f U)
    (isZero_cechZ_neg_one A X f U) cc φ₀ hφ₀
  refine Work.DSEQ0.isSplitMono_of_chainModel A X f _ cc φ e ?_ hφ
  dsimp only [Work.DSEQ0.singleIsoCompQ]
  rw [Iso.trans_hom, Category.assoc]
  exact he

/-- **Descent of almost splitting to splitting** (the abstract step 6 of the proof map's
§4(a)).  Let `A` be a Noetherian local domain, `S` a faithfully flat `A`-algebra, and let
`I ⊆ A` be an ideal (in the application, the obstruction ideal `coaugIdeal` of a Čech model).
If some `0 ≠ a ∈ I` has all its `p^e`-th roots inside `I·S` for every `e`, then `I` is the unit
ideal.

This is `Work.DSEQP.one_mem_of_forall_pthRoot_mem` restated in the Čech vocabulary. -/
theorem one_mem_coaugIdeal_of_forall_pthRoot (A S : Type u) [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] [CommRing S] [Algebra A S]
    [Module.FaithfullyFlat A S] (p : ℕ) [Fact p.Prime]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) {ι : Type u} (U : ι → X.Opens)
    (cc : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⟶
      DSMap.cechZ A X f U)
    (h : ∃ a ∈ coaugIdeal A X f U cc, a ≠ 0 ∧ ∀ e : ℕ, ∃ t : S,
      t ∈ (coaugIdeal A X f U cc).map (algebraMap A S) ∧ t ^ (p ^ e) = algebraMap A S a) :
    (1 : A) ∈ coaugIdeal A X f U cc := by
  obtain ⟨a, ha, ha0, hroot⟩ := h
  exact one_mem_of_forall_pthRoot_mem A S p ha ha0 hroot

end Work.DSEQP
