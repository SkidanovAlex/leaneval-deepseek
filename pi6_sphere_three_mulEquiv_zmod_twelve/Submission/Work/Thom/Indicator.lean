import Mathlib
import Submission.Work.Cohomology.mixedRelCupH
import Submission.Work.Cohomology.AlexanderWhitney

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-!
# The indicator class of a union of connected components, and the pullback of a cohomology class

This module supplies the two cochain-level tools that the Thom isomorphism of the trivial real
line bundle needs.

* **`Work.Thom.homologyMap_cohomologyClassOf`** — the *computation rule for the pullback of a
  cohomology class*: the pullback of the class of a cocycle is the class of the pulled-back
  cocycle, for an arbitrary continuous map.  (The workspace has this for the restriction to a
  subspace, `Work.Cohomology.homologyMap_restr_cohomologyClassOf`; here it is stated for an
  arbitrary `f : C(X,Y)`.)

* **`Work.Thom.indicatorCochain`** and **`Work.Thom.indicatorClass`** — the *indicator cochain of
  a union of connected components* of a space: the `0`-cochain that is `1` on the components in
  `P` and `0` on the others.  It is a `0`-cocycle (`Work.Thom.indicatorCochain_cocycle`), so it
  defines a class `Work.Thom.indicatorClass X P ∈ H⁰(X;ℤ)`; its values on the generators are
  `Work.Thom.genEval_indicatorCochain`, and it is natural
  (`Work.Thom.indicatorClass_pullback`, `Work.Thom.indicatorCochain_pullback`).

The indicator class is the model of the "difference of the two ends" of a line bundle: for the
pair `(E, E∖0)` of the trivial line bundle the zero complement `E∖0` has (at least) two connected
components, and the Thom class of the pair is the connecting image of the indicator class of the
"negative" components.
-/

open CategoryTheory AlgebraicTopology Limits Simplicial

open scoped Simplicial

open Classical

namespace Work.Thom

noncomputable section

/-! ## The pullback of a cohomology class -/

/-- The cycle built from a cocycle has the cocycle as underlying cochain. -/
theorem cyclesMap_cocycleOfK (K L : CochainComplex (ModuleCat ℤ) ℕ) (φ : K ⟶ L) {n : ℕ}
    (α : ↑(K.X n)) (hα : (ModuleCat.Hom.hom (K.d n (n + 1))) α = 0)
    (h : (ModuleCat.Hom.hom (L.d n (n + 1))) ((ModuleCat.Hom.hom (φ.f n)) α) = 0) :
    HomologicalComplex.cyclesMap φ n (Work.Cohomology.cocycleOfK K α hα) =
      Work.Cohomology.cocycleOfK L ((ModuleCat.Hom.hom (φ.f n)) α) h := by
  apply Work.Cohomology.iCycles_injective_K L n
  have h1 := congrArg (fun (g : K.cycles n ⟶ L.X n) => g.hom (Work.Cohomology.cocycleOfK K α hα))
    (HomologicalComplex.cyclesMap_i φ n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
  rw [Work.Cohomology.iCycles_cocycleOfK K α hα] at h1
  rw [h1, Work.Cohomology.iCycles_cocycleOfK L ((ModuleCat.Hom.hom (φ.f n)) α) h]

/-- **The pullback of a cohomology class is the class of the pulled-back cocycle.** -/
theorem homologyMap_cohomologyClassOf {X Y : TopCat} (f : X ⟶ Y) {n : ℕ}
    (α : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj Y) n)
    (hα : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj Y) α = 0)
    (h : Work.Cohomology.cochainDiff ℤ (TopCat.toSSet.obj X)
      (((Work.Cohomology.dualChainMap ℤ X Y f).f n).hom α) = 0) :
    (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap ℤ X Y f) n)
        (Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj Y) α hα)
      = Work.Cohomology.cohomologyClassOf ℤ (TopCat.toSSet.obj X)
          (((Work.Cohomology.dualChainMap ℤ X Y f).f n).hom α) h := by
  have hα' : (ModuleCat.Hom.hom ((Work.Cohomology.singularCochainComplex ℤ Y).d n (n+1))) α = 0 := by
    rw [Work.Cohomology.singularCochain_d_apply]; exact hα
  have h' : (ModuleCat.Hom.hom ((Work.Cohomology.singularCochainComplex ℤ X).d n (n+1)))
      (((Work.Cohomology.dualChainMap ℤ X Y f).f n).hom α) = 0 := by
    rw [Work.Cohomology.singularCochain_d_apply]; exact h
  change (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap ℤ X Y f) n)
      (((Work.Cohomology.singularCochainComplex ℤ Y).homologyπ n).hom
        (Work.Cohomology.cocycleOfK (Work.Cohomology.singularCochainComplex ℤ Y) α hα'))
    = ((Work.Cohomology.singularCochainComplex ℤ X).homologyπ n).hom
        (Work.Cohomology.cocycleOfK (Work.Cohomology.singularCochainComplex ℤ X)
          (((Work.Cohomology.dualChainMap ℤ X Y f).f n).hom α) h')
  have hnat := congrArg (fun (g : (Work.Cohomology.singularCochainComplex ℤ Y).cycles n ⟶
        (Work.Cohomology.singularCochainComplex ℤ X).homology n) => g.hom
      (Work.Cohomology.cocycleOfK (Work.Cohomology.singularCochainComplex ℤ Y) α hα'))
    (HomologicalComplex.homologyπ_naturality (Work.Cohomology.dualChainMap ℤ X Y f) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [hnat, cyclesMap_cocycleOfK]

/-! ## The indicator cochain of a union of connected components -/

/-- **The indicator cochain of a union of connected components.**  For a simplicial set `X` and a
set `P` of its connected components, this is the `0`-cochain that is `1` on the `0`-simplices
whose component lies in `P` and `0` on the others. -/
noncomputable def indicatorCochain (X : SSet) (P : Set (SSet.π₀ X)) :
    Work.Cohomology.Cochain ℤ X 0 :=
  ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero X (ModuleCat.of ℤ ℤ) ≫
    Sigma.desc (fun c : SSet.π₀ X =>
      if c ∈ P then 𝟙 (ModuleCat.of ℤ ℤ) else 0))

/-- **The indicator cochain is a `0`-cocycle.** -/
theorem indicatorCochain_cocycle (X : SSet) (P : Set (SSet.π₀ X)) :
    Work.Cohomology.cochainDiff ℤ X (indicatorCochain X P) = 0 := by
  have h : (X.chainComplex (ModuleCat.of ℤ ℤ)).d 1 0 ≫
      (SSet.π₀.fromChainComplexXZero X (ModuleCat.of ℤ ℤ) ≫
        Sigma.desc (fun c : SSet.π₀ X =>
          if c ∈ P then 𝟙 (ModuleCat.of ℤ ℤ) else 0)) = 0 := by
    rw [← Category.assoc, SSet.π₀.d_fromChainComplexXZero, zero_comp]
  have h2 := congrArg ModuleCat.Hom.hom h
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  have h3 : (indicatorCochain X P).comp
      ((X.chainComplex (ModuleCat.of ℤ ℤ)).d 1 0).hom = 0 := by
    rw [indicatorCochain]
    exact h2
  exact h3

/-- The unfolding of the indicator cochain. -/
theorem indicatorCochain_eq (X : SSet) (P : Set (SSet.π₀ X)) :
    (indicatorCochain X P) =
      (ModuleCat.Hom.hom (Sigma.desc (fun c : SSet.π₀ X =>
        if c ∈ P then 𝟙 (ModuleCat.of ℤ ℤ) else 0))).comp
        (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero X (ModuleCat.of ℤ ℤ))) := by
  rw [indicatorCochain, ModuleCat.hom_comp]

/-- The value of the indicator cochain on a `0`-simplex whose component lies in `P`. -/
theorem genEval_indicatorCochain_of_mem (X : SSet) (P : Set (SSet.π₀ X)) (s : X _⦋0⦌)
    (hs : SSet.π₀.mk s ∈ P) :
    Work.Cohomology.genEval ℤ X (indicatorCochain X P) s = 1 := by
  have h2 : (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero X (ModuleCat.of ℤ ℤ)))
        (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) s)).hom 1)
      = (ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ X => ModuleCat.of ℤ ℤ)
          (SSet.π₀.mk s))) 1 := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (SSet.π₀.comp_fromChainComplexXZero (X := X) (R := ModuleCat.of ℤ ℤ) s)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  have h3 : (ModuleCat.Hom.hom (Sigma.desc (fun c : SSet.π₀ X =>
        if c ∈ P then 𝟙 (ModuleCat.of ℤ ℤ) else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ))))
        ((ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ X => ModuleCat.of ℤ ℤ)
          (SSet.π₀.mk s))) 1)
      = (ModuleCat.Hom.hom (if SSet.π₀.mk s ∈ P then 𝟙 (ModuleCat.of ℤ ℤ)
          else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ))) 1 := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (Sigma.ι_desc (fun c : SSet.π₀ X =>
        if c ∈ P then 𝟙 (ModuleCat.of ℤ ℤ)
        else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)) (SSet.π₀.mk s))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  show (indicatorCochain X P) (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) s)).hom 1) = 1
  rw [indicatorCochain_eq]
  simp only [LinearMap.comp_apply]
  rw [h2, h3, if_pos hs]
  rfl

/-- The value of the indicator cochain on a `0`-simplex whose component does not lie in `P`. -/
theorem genEval_indicatorCochain_of_not_mem (X : SSet) (P : Set (SSet.π₀ X)) (s : X _⦋0⦌)
    (hs : SSet.π₀.mk s ∉ P) :
    Work.Cohomology.genEval ℤ X (indicatorCochain X P) s = 0 := by
  have h2 : (ModuleCat.Hom.hom (SSet.π₀.fromChainComplexXZero X (ModuleCat.of ℤ ℤ)))
        (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) s)).hom 1)
      = (ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ X => ModuleCat.of ℤ ℤ)
          (SSet.π₀.mk s))) 1 := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (SSet.π₀.comp_fromChainComplexXZero (X := X) (R := ModuleCat.of ℤ ℤ) s)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  have h3 : (ModuleCat.Hom.hom (Sigma.desc (fun c : SSet.π₀ X =>
        if c ∈ P then 𝟙 (ModuleCat.of ℤ ℤ) else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ))))
        ((ModuleCat.Hom.hom (Sigma.ι (fun _ : SSet.π₀ X => ModuleCat.of ℤ ℤ)
          (SSet.π₀.mk s))) 1)
      = (ModuleCat.Hom.hom (if SSet.π₀.mk s ∈ P then 𝟙 (ModuleCat.of ℤ ℤ)
          else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ))) 1 := by
    have hh := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (Sigma.ι_desc (fun c : SSet.π₀ X =>
        if c ∈ P then 𝟙 (ModuleCat.of ℤ ℤ)
        else (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)) (SSet.π₀.mk s))
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  show (indicatorCochain X P) (((X.ιChainComplex (R := ModuleCat.of ℤ ℤ) s)).hom 1) = 0
  rw [indicatorCochain_eq]
  simp only [LinearMap.comp_apply]
  rw [h2, h3, if_neg hs]
  rfl

/-- **The indicator class of a union of connected components** in `H⁰(X;ℤ)`. -/
noncomputable def indicatorClass (X : SSet) (P : Set (SSet.π₀ X)) :
    (Work.Cohomology.SSetCochainComplex ℤ X).homology 0 :=
  Work.Cohomology.cohomologyClassOf ℤ X (indicatorCochain X P) (indicatorCochain_cocycle X P)



/-- **Evaluation of the pullback of a cochain on a generator.** -/
theorem genEval_dualChainMap {X Y : TopCat} (f : X ⟶ Y) {n : ℕ}
    (α : Work.Cohomology.Cochain ℤ (TopCat.toSSet.obj Y) n) (s : (TopCat.toSSet.obj X) _⦋n⦌) :
    Work.Cohomology.genEval ℤ (TopCat.toSSet.obj X)
        (((Work.Cohomology.dualChainMap ℤ X Y f).f n).hom α) s
      = Work.Cohomology.genEval ℤ (TopCat.toSSet.obj Y) α
          ((TopCat.toSSet.map f).app _ s) := by
  show (Work.Cohomology.cochainPullbackHom ℤ X Y f n).hom α
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1) = _
  rw [Work.Cohomology.cochainPullbackHom_apply]
  have h : ((Work.Cohomology.chainMap ℤ X Y f).f n).hom
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1)
      = ((TopCat.toSSet.obj Y).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map f).app _ s)).hom 1 := by
    have h2 := congrArg (fun k => (ModuleCat.Hom.hom k) 1)
      (SSet.ι_chainComplexMap_f (X := TopCat.toSSet.obj X) (Y := TopCat.toSSet.obj Y)
        (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ) s)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    exact h2
  rw [h]
  rfl

theorem dualChainMap_indicatorCochain {X Y : TopCat} (f : X ⟶ Y)
    (P : Set (SSet.π₀ (TopCat.toSSet.obj Y))) :
    ((Work.Cohomology.dualChainMap ℤ X Y f).f 0).hom
        (indicatorCochain (TopCat.toSSet.obj Y) P)
      = indicatorCochain (TopCat.toSSet.obj X)
          {c | SSet.mapπ₀ (TopCat.toSSet.map f) c ∈ P} := by
  have h : ModuleCat.ofHom (((Work.Cohomology.dualChainMap ℤ X Y f).f 0).hom
        (indicatorCochain (TopCat.toSSet.obj Y) P))
      = ModuleCat.ofHom (indicatorCochain (TopCat.toSSet.obj X)
          {c | SSet.mapπ₀ (TopCat.toSSet.map f) c ∈ P}) := by
    apply Cofan.IsColimit.hom_ext
      ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) 0)
    intro s
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    have hr : r = r • (1 : ℤ) := by simp
    rw [hr, map_smul, map_smul]
    congr 1
    show Work.Cohomology.genEval ℤ (TopCat.toSSet.obj X)
        (((Work.Cohomology.dualChainMap ℤ X Y f).f 0).hom
          (indicatorCochain (TopCat.toSSet.obj Y) P)) s
      = Work.Cohomology.genEval ℤ (TopCat.toSSet.obj X)
          (indicatorCochain (TopCat.toSSet.obj X)
            {c | SSet.mapπ₀ (TopCat.toSSet.map f) c ∈ P}) s
    rw [genEval_dualChainMap f _ s]
    by_cases hP : SSet.mapπ₀ (TopCat.toSSet.map f) (SSet.π₀.mk s) ∈ P
    · have h1 : SSet.π₀.mk ((TopCat.toSSet.map f).app _ s) ∈ P := by
        rwa [SSet.mapπ₀_mk] at hP
      rw [genEval_indicatorCochain_of_mem (TopCat.toSSet.obj Y) P _ h1,
        genEval_indicatorCochain_of_mem (TopCat.toSSet.obj X)
          {c | SSet.mapπ₀ (TopCat.toSSet.map f) c ∈ P} s hP]
    · have h1 : SSet.π₀.mk ((TopCat.toSSet.map f).app _ s) ∉ P := by
        rwa [SSet.mapπ₀_mk] at hP
      rw [genEval_indicatorCochain_of_not_mem (TopCat.toSSet.obj Y) P _ h1,
        genEval_indicatorCochain_of_not_mem (TopCat.toSSet.obj X)
          {c | SSet.mapπ₀ (TopCat.toSSet.map f) c ∈ P} s hP]
  have h2 := congrArg ModuleCat.Hom.hom h
  simpa using h2



theorem indicatorClass_pullback {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (P : Set (SSet.π₀ (TopCat.toSSet.obj (TopCat.of Y)))) :
    (Work.Cohomology.singularCohomologyMap ℤ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) 0).hom
        (indicatorClass (TopCat.toSSet.obj (TopCat.of Y)) P)
      = indicatorClass (TopCat.toSSet.obj (TopCat.of X))
          {c | SSet.mapπ₀ (TopCat.toSSet.map (TopCat.ofHom f)) c ∈ P} := by
  rw [indicatorClass, indicatorClass, Work.Cohomology.singularCohomologyMap]
  erw [homologyMap_cohomologyClassOf (TopCat.ofHom f) (indicatorCochain (TopCat.toSSet.obj (TopCat.of Y)) P)
      (indicatorCochain_cocycle _ _)
      (by rw [dualChainMap_indicatorCochain]; exact indicatorCochain_cocycle _ _)]
  exact Work.Cohomology.cohomologyClassOf_congr ℤ (TopCat.toSSet.obj (TopCat.of X))
    (dualChainMap_indicatorCochain (TopCat.ofHom f) P) _ _


end

end Work.Thom
