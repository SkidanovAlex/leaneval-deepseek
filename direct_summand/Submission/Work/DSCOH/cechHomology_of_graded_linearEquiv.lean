/-
Area DSCOH — transport of the chart Čech cohomology along a grading-preserving linear
equivalence of graded modules.

The two graded modules `M`, `M'` in the statement of
`Work.DSCOH.cechHomology_of_graded_linearEquiv` live in *a priori* different universes, so their
chart Čech complexes `chartCech ℳ` and `chartCech ℳ'` are (cochain) complexes in two different
categories `ModuleCat.{max u₁ u₂} A` and `ModuleCat.{max u₁ u₃} A`: there is no morphism between
them to speak of.  The way out is to lift both complexes into a common (larger) universe with
`ULift`, which is exact, so that it commutes with homology.  In the common universe the two
complexes *are* isomorphic — the isomorphism is induced by the maps `cechMap` — and homological
and finiteness statements can be transported back and forth.

Everything in this file except the final theorem is a private helper.

The lifted complex is written down explicitly (`chartCechLift`), rather than as the image of
`chartCech ℳ` under the `ULift` functor, so that its terms are *syntactically* the `ULift`s of the
terms of `chartCech ℳ`; this makes the components of the comparison morphisms elaborate without
any definitional unfolding of `chartCech`.  The identification with the image of the `ULift`
functor (`chartCechLift_eq`) is what lets us use Mathlib's functoriality of homology.
-/
import Mathlib
import Submission.Work.DSCOH.ChartFree
import Submission.Work.DSCOH.cechMap_natural

open MvPolynomial CategoryTheory CategoryTheory.Limits

set_option allowUnsafeReducibility true


namespace Work.DSCOH

universe uA uM uM' uW uC uD uI

/-! ## Lifting linear maps along `ULift` -/

/-- The `ULift` of a linear map. -/
private noncomputable def uliftLinearMap {R : Type*} [CommRing R] {X Y : Type*}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) :
    ULift X →ₗ[R] ULift Y :=
  (ULift.moduleEquiv (R := R) (M := Y)).symm.toLinearMap.comp
    (f.comp (ULift.moduleEquiv (R := R) (M := X)).toLinearMap)

private lemma uliftLinearMap_apply {R : Type*} [CommRing R] {X Y : Type*}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) (x : ULift X) :
    uliftLinearMap f x =
      (ULift.moduleEquiv (R := R) (M := Y)).symm
        (f ((ULift.moduleEquiv (R := R) (M := X)) x)) := rfl

private lemma uliftLinearMap_comp {R : Type*} [CommRing R] {X Y Z : Type*}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) :
    uliftLinearMap (g.comp f) = (uliftLinearMap g).comp (uliftLinearMap f) := by
  ext x
  simp only [LinearMap.comp_apply, uliftLinearMap_apply, LinearEquiv.apply_symm_apply]

private lemma uliftLinearMap_id {R : Type*} [CommRing R] {X : Type*}
    [AddCommGroup X] [Module R X] :
    uliftLinearMap (LinearMap.id : X →ₗ[R] X) = LinearMap.id := by
  ext x
  simp only [uliftLinearMap_apply, LinearMap.id_apply, LinearEquiv.symm_apply_apply]

private lemma uliftLinearMap_zero {R : Type*} [CommRing R] {X Y : Type*}
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] :
    uliftLinearMap (R := R) (0 : X →ₗ[R] Y) = 0 := by
  ext x
  simp only [uliftLinearMap_apply, LinearMap.zero_apply, map_zero, LinearEquiv.map_zero]

/-! ## Functoriality of the localization maps `locMapOf` -/

private lemma locMapOf_comp' {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N] [IsScalarTower A (Poly A n) N]
    {P : Type*} [AddCommGroup P] [Module A P] [Module (Poly A n) P] [IsScalarTower A (Poly A n) P]
    (φ : M →ₗ[Poly A n] N) (ψ : N →ₗ[Poly A n] P) (S : Finset (Fin n)) :
    (locMapOf (A := A) (M := N) ψ S).comp (locMapOf (A := A) (M := M) φ S) =
      locMapOf (A := A) (M := M) (ψ.comp φ) S :=
  (IsLocalizedModule.map_comp' (subS (A := A) S)
    (LocalizedModule.mkLinearMap (subS (A := A) S) M)
    (LocalizedModule.mkLinearMap (subS (A := A) S) N)
    (LocalizedModule.mkLinearMap (subS (A := A) S) P) φ ψ).symm

private lemma locMapOf_comp_apply' {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N] [IsScalarTower A (Poly A n) N]
    {P : Type*} [AddCommGroup P] [Module A P] [Module (Poly A n) P] [IsScalarTower A (Poly A n) P]
    (φ : M →ₗ[Poly A n] N) (ψ : N →ₗ[Poly A n] P) (S : Finset (Fin n))
    (x : locAt (A := A) (M := M) S) :
    locMapOf (A := A) (M := N) ψ S (locMapOf (A := A) (M := M) φ S x) =
      locMapOf (A := A) (M := M) (ψ.comp φ) S x := by
  rw [← LinearMap.comp_apply, locMapOf_comp']

private lemma locMapOf_id' {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (S : Finset (Fin n)) :
    locMapOf (A := A) (M := M) (LinearMap.id : M →ₗ[Poly A n] M) S = LinearMap.id := by
  simpa only [locMapOf] using IsLocalizedModule.map_id (S := subS (A := A) S)
    (f := LocalizedModule.mkLinearMap (subS (A := A) S) M)

private lemma degZeroMapOf_coe {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    {N : Type*} [AddCommGroup N] [Module A N] [Module (Poly A n) N] [IsScalarTower A (Poly A n) N]
    (ℳ : ℕ → Submodule A M) (𝒩 : ℕ → Submodule A N) (φ : M →ₗ[Poly A n] N) (S : Finset (Fin n))
    (h : ∀ x ∈ degZero (A := A) (M := M) ℳ S,
      locMapOf (A := A) (M := M) φ S x ∈ degZero (A := A) (M := N) 𝒩 S)
    (x : degZero (A := A) (M := M) ℳ S) :
    ((degZeroMapOf (A := A) (n := n) ℳ 𝒩 φ S h x : locAt (A := A) (M := N) S)) =
      locMapOf (A := A) (M := M) φ S x := by
  simp only [degZeroMapOf, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply,
    LinearMap.coe_restrictScalars, Submodule.coe_subtype]
  rfl

/-! ## Lifting the chart Čech complex to a larger universe

`chartCechLift ℳ` is the complex whose `q`-th term is `of A (ULift (CechTerm ℳ q))` and whose
differential is the `ULift` of the Čech differential.  It is (propositionally, see
`chartCechLift_eq`) the image of `chartCech ℳ` under the exact functor `ModuleCat.uliftFunctor`,
but it is written down explicitly so that its terms are syntactically `ULift`s of the terms of
`chartCech ℳ`. -/

private noncomputable def chartCechLift {A : Type uA} [CommRing A] {n : ℕ} {M : Type uM}
    [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] :
    CochainComplex (ModuleCat.{max (max uA uM) uW} A) ℕ :=
  CochainComplex.of
    (fun q => ModuleCat.of A (ULift.{uW} (CechTerm (A := A) (n := n) (M := M) ℳ q)))
    (fun q => ModuleCat.ofHom (uliftLinearMap (R := A)
      (cechDiff (A := A) (n := n) (M := M) ℳ q)))
    (fun q => by
      rw [← ModuleCat.ofHom_comp, ← uliftLinearMap_comp, cechDiff_comp, uliftLinearMap_zero,
        ModuleCat.ofHom_zero])

private lemma chartCechLift_X {A : Type uA} [CommRing A] {n : ℕ} {M : Type uM}
    [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] (q : ℕ) :
    (chartCechLift (A := A) (n := n) (M := M) ℳ).X q =
      ModuleCat.of A (ULift.{uW} (CechTerm (A := A) (n := n) (M := M) ℳ q)) :=
  rfl

private lemma chartCechLift_d {A : Type uA} [CommRing A] {n : ℕ} {M : Type uM}
    [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] (q : ℕ) :
    (chartCechLift (A := A) (n := n) (M := M) ℳ).d q (q + 1) =
      ModuleCat.ofHom (uliftLinearMap (R := A)
        (cechDiff (A := A) (n := n) (M := M) ℳ q)) := by
  simp only [chartCechLift, CochainComplex.of_d]

attribute [local reducible] chartCechLift

/-- The explicit lifted complex is the image of `chartCech ℳ` under the `ULift` functor. -/
private lemma chartCechLift_eq {A : Type uA} [CommRing A] {n : ℕ} {M : Type uM}
    [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] :
    chartCechLift (A := A) (n := n) (M := M) ℳ =
      ((ModuleCat.uliftFunctor.{uW, max uA uM} A).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (chartCech (A := A) (n := n) (M := M) ℳ) := by
  apply HomologicalComplex.ext
  · intro i j hij
    rw [ComplexShape.up_Rel] at hij
    subst hij
    simp only [chartCechLift, CochainComplex.of_d, Functor.mapHomologicalComplex_obj_d]
    rw [show (chartCech (A := A) (n := n) (M := M) ℳ).d i (i + 1) =
        ModuleCat.ofHom (cechDiff (A := A) (n := n) (M := M) ℳ i) by
      simp only [chartCech, chartCechOf, CochainComplex.of_d]]
    rfl
  · funext q
    simp only [chartCechLift, CochainComplex.of_X, Functor.mapHomologicalComplex_obj_X,
      ModuleCat.uliftFunctor_obj, chartCech, chartCechOf, CochainComplex.of_X]

/-! ## Homology commutes with an exact functor applied to a complex -/

/-- Homology commutes with an exact functor applied to a cochain complex. -/
private noncomputable def mapHomologicalComplexHomologyIso {C : Type uC} [Category C]
    [HasZeroMorphisms C] [CategoryWithHomology C]
    {D : Type uD} [Category D] [HasZeroMorphisms D] [CategoryWithHomology D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.PreservesHomology]
    {ι : Type uI} (c : ComplexShape ι) (i : ι) (K : HomologicalComplex C c) :
    ((F.mapHomologicalComplex c).obj K).homology i ≅ F.obj (K.homology i) := by
  have hsc : ((F.mapHomologicalComplex c).obj K).sc i = (K.sc i).map F := rfl
  dsimp only [HomologicalComplex.homology]
  rw [hsc]
  exact ShortComplex.mapHomologyIso (K.sc i) F

/-! ## Transfer of `Subsingleton` -/

private lemma subsingleton_linearEquiv {R : Type*} [Semiring R] {M N : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) :
    Subsingleton M ↔ Subsingleton N :=
  ⟨fun h => by haveI := h; exact e.surjective.subsingleton,
   fun h => by haveI := h; exact Equiv.subsingleton e.toEquiv⟩

private lemma subsingleton_ulift {α : Type*} : Subsingleton (ULift α) ↔ Subsingleton α := by
  constructor
  · intro h
    refine ⟨fun a b => ?_⟩
    have hh : (ULift.up a : ULift α) = ULift.up b := Subsingleton.elim _ _
    exact ULift.up.inj hh
  · intro h
    exact ⟨fun x y => by
      obtain ⟨a⟩ := x
      obtain ⟨b⟩ := y
      exact congrArg ULift.up (h.elim a b)⟩

section ChartCechLiftIso

/-- **The two lifted chart Čech complexes are isomorphic.**  The isomorphism is induced by the
maps `cechMap`; it exists only after both complexes have been lifted into a common universe. -/
private noncomputable def chartCechLift_iso {A : Type uA} [CommRing A] {n : ℕ}
    {M : Type uM} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    {M' : Type uM'} [AddCommGroup M'] [Module A M'] [Module (Poly A n) M']
    [IsScalarTower A (Poly A n) M']
    (ℳ' : ℕ → Submodule A M') [SetLike.GradedSMul (homSub A n) ℳ']
    (φ : M ≃ₗ[Poly A n] M')
    (hφ : ∀ e, Submodule.map ((φ : M →ₗ[Poly A n] M').restrictScalars A) (ℳ e) = ℳ' e) :
    chartCechLift.{uA, uM, uM'} (A := A) (n := n) (M := M) ℳ ≅
      chartCechLift.{uA, uM', uM} (A := A) (n := n) (M := M') ℳ' := by
  classical
  have hle : ∀ d, Submodule.map ((φ : M →ₗ[Poly A n] M').restrictScalars A) (ℳ d) ≤ ℳ' d :=
    fun d => le_of_eq (hφ d)
  have hle' : ∀ d, Submodule.map (((φ.symm : M' →ₗ[Poly A n] M)).restrictScalars A) (ℳ' d) ≤ ℳ d := by
    intro d
    rw [← hφ d]
    rintro _ ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  have h21 : ∀ i : ℕ,
      (cechMap (A := A) (n := n) ℳ' ℳ (φ.symm : M' →ₗ[Poly A n] M) hle' i).comp
        (cechMap (A := A) (n := n) ℳ ℳ' (φ : M →ₗ[Poly A n] M') hle i) = LinearMap.id := by
    intro i
    apply LinearMap.ext
    intro x
    funext S
    apply Subtype.ext
    simp only [LinearMap.comp_apply, cechMap, LinearMap.pi_apply, LinearMap.proj_apply,
      degZeroMapOf_coe]
    rw [locMapOf_comp_apply' (A := A) (M := M) (N := M') (P := M)
      (φ := (φ : M →ₗ[Poly A n] M')) (ψ := (φ.symm : M' →ₗ[Poly A n] M)) S]
    have hs : ((φ.symm : M' →ₗ[Poly A n] M).comp (φ : M →ₗ[Poly A n] M')) = LinearMap.id := by
      ext m
      simp
    rw [hs, locMapOf_id']
    rfl
  have h12 : ∀ i : ℕ,
      (cechMap (A := A) (n := n) ℳ ℳ' (φ : M →ₗ[Poly A n] M') hle i).comp
        (cechMap (A := A) (n := n) ℳ' ℳ (φ.symm : M' →ₗ[Poly A n] M) hle' i) = LinearMap.id := by
    intro i
    apply LinearMap.ext
    intro x
    funext S
    apply Subtype.ext
    simp only [LinearMap.comp_apply, cechMap, LinearMap.pi_apply, LinearMap.proj_apply,
      degZeroMapOf_coe]
    rw [locMapOf_comp_apply' (A := A) (M := M') (N := M) (P := M')
      (φ := (φ.symm : M' →ₗ[Poly A n] M)) (ψ := (φ : M →ₗ[Poly A n] M')) S]
    have hs : ((φ : M →ₗ[Poly A n] M').comp (φ.symm : M' →ₗ[Poly A n] M)) = LinearMap.id := by
      ext m
      simp
    rw [hs, locMapOf_id']
    rfl
  let α : chartCechLift.{uA, uM, uM'} (A := A) (n := n) (M := M) ℳ ⟶
      chartCechLift.{uA, uM', uM} (A := A) (n := n) (M := M') ℳ' := CochainComplex.ofHom
    (fun i => ModuleCat.ofHom (uliftLinearMap (R := A)
      (cechMap (A := A) (n := n) ℳ ℳ' (φ : M →ₗ[Poly A n] M') hle i)))
    (fun i => by
      rw [chartCechLift_d, chartCechLift_d, ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
      congr 1
      rw [← uliftLinearMap_comp, ← uliftLinearMap_comp]
      congr 1
      exact (cechMap_natural (A := A) (n := n) ℳ ℳ' (φ : M →ₗ[Poly A n] M') hle i).symm)
  let β : chartCechLift.{uA, uM', uM} (A := A) (n := n) (M := M') ℳ' ⟶
      chartCechLift.{uA, uM, uM'} (A := A) (n := n) (M := M) ℳ := CochainComplex.ofHom
    (fun i => ModuleCat.ofHom (uliftLinearMap (R := A)
      (cechMap (A := A) (n := n) ℳ' ℳ (φ.symm : M' →ₗ[Poly A n] M) hle' i)))
    (fun i => by
      rw [chartCechLift_d, chartCechLift_d, ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
      congr 1
      rw [← uliftLinearMap_comp, ← uliftLinearMap_comp]
      congr 1
      exact (cechMap_natural (A := A) (n := n) ℳ' ℳ (φ.symm : M' →ₗ[Poly A n] M) hle' i).symm)
  have hαβ : α ≫ β = 𝟙 (chartCechLift.{uA, uM, uM'} (A := A) (n := n) (M := M) ℳ) := by
    apply HomologicalComplex.hom_ext
    intro i
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    show ModuleCat.ofHom (uliftLinearMap (R := A)
        (cechMap (A := A) (n := n) ℳ ℳ' (φ : M →ₗ[Poly A n] M') hle i)) ≫
      ModuleCat.ofHom (uliftLinearMap (R := A)
        (cechMap (A := A) (n := n) ℳ' ℳ (φ.symm : M' →ₗ[Poly A n] M) hle' i)) =
      𝟙 ((chartCechLift.{uA, uM, uM'} (A := A) (n := n) (M := M) ℳ).X i)
    rw [← ModuleCat.ofHom_comp, ← uliftLinearMap_comp, h21 i, uliftLinearMap_id,
      ModuleCat.ofHom_id]
    try rfl
  have hβα : β ≫ α = 𝟙 (chartCechLift.{uA, uM', uM} (A := A) (n := n) (M := M') ℳ') := by
    apply HomologicalComplex.hom_ext
    intro i
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    show ModuleCat.ofHom (uliftLinearMap (R := A)
        (cechMap (A := A) (n := n) ℳ' ℳ (φ.symm : M' →ₗ[Poly A n] M) hle' i)) ≫
      ModuleCat.ofHom (uliftLinearMap (R := A)
        (cechMap (A := A) (n := n) ℳ ℳ' (φ : M →ₗ[Poly A n] M') hle i)) =
      𝟙 ((chartCechLift.{uA, uM', uM} (A := A) (n := n) (M := M') ℳ').X i)
    rw [← ModuleCat.ofHom_comp, ← uliftLinearMap_comp, h12 i, uliftLinearMap_id,
      ModuleCat.ofHom_id]
    try rfl
  exact ⟨α, β, hαβ, hβα⟩

end ChartCechLiftIso

end Work.DSCOH

namespace Work.DSCOH

theorem cechHomology_of_graded_linearEquiv {A : Type*} [CommRing A] {n : ℕ}
    {M : Type*} [AddCommGroup M] [Module A M] [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ]
    {M' : Type*} [AddCommGroup M'] [Module A M'] [Module (Poly A n) M'] [IsScalarTower A (Poly A n) M']
    (ℳ' : ℕ → Submodule A M') [SetLike.GradedSMul (homSub A n) ℳ']
    (φ : M ≃ₗ[Poly A n] M')
    (hφ : ∀ e, Submodule.map ((φ : M →ₗ[Poly A n] M').restrictScalars A) (ℳ e) = ℳ' e) (q : ℕ) :
    (Module.Finite A ((chartCech (A := A) (n := n) (M := M) ℳ).homology q) ↔
      Module.Finite A ((chartCech (A := A) (n := n) (M := M') ℳ').homology q)) ∧
      (CategoryTheory.Limits.IsZero ((chartCech (A := A) (n := n) (M := M) ℳ).homology q) ↔
        CategoryTheory.Limits.IsZero ((chartCech (A := A) (n := n) (M := M') ℳ').homology q)) := by
  classical
  -- the isomorphism of the two lifted complexes, in the common universe
  have eK : chartCechLift.{u_1, u_2, u_3} (A := A) (n := n) (M := M) ℳ ≅
      chartCechLift.{u_1, u_3, u_2} (A := A) (n := n) (M := M') ℳ' :=
    chartCechLift_iso ℳ ℳ' φ hφ
  have hHom : (chartCechLift.{u_1, u_2, u_3} (A := A) (n := n) (M := M) ℳ).homology q ≅
      (chartCechLift.{u_1, u_3, u_2} (A := A) (n := n) (M := M') ℳ').homology q :=
    (HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℕ) q).mapIso eK
  have hF₁ : (chartCechLift.{u_1, u_2, u_3} (A := A) (n := n) (M := M) ℳ).homology q ≅
      (ModuleCat.uliftFunctor.{u_3, max u_1 u_2} A).obj
        ((chartCech (A := A) (n := n) (M := M) ℳ).homology q) := by
    rw [chartCechLift_eq]
    exact mapHomologicalComplexHomologyIso (ModuleCat.uliftFunctor.{u_3, max u_1 u_2} A)
      (ComplexShape.up ℕ) q (chartCech (A := A) (n := n) (M := M) ℳ)
  have hF₂ : (chartCechLift.{u_1, u_3, u_2} (A := A) (n := n) (M := M') ℳ').homology q ≅
      (ModuleCat.uliftFunctor.{u_2, max u_1 u_3} A).obj
        ((chartCech (A := A) (n := n) (M := M') ℳ').homology q) := by
    rw [chartCechLift_eq]
    exact mapHomologicalComplexHomologyIso (ModuleCat.uliftFunctor.{u_2, max u_1 u_3} A)
      (ComplexShape.up ℕ) q (chartCech (A := A) (n := n) (M := M') ℳ')
  -- ### finiteness
  have hA1 : Module.Finite A
        ↥((chartCechLift.{u_1, u_2, u_3} (A := A) (n := n) (M := M) ℳ).homology q) ↔
      Module.Finite A ↥((ModuleCat.uliftFunctor.{u_3, max u_1 u_2} A).obj
        ((chartCech (A := A) (n := n) (M := M) ℳ).homology q)) :=
    Module.Finite.equiv_iff hF₁.toLinearEquiv
  have hA2 : Module.Finite A ↥((ModuleCat.uliftFunctor.{u_3, max u_1 u_2} A).obj
        ((chartCech (A := A) (n := n) (M := M) ℳ).homology q)) ↔
      Module.Finite A ↥((chartCech (A := A) (n := n) (M := M) ℳ).homology q) :=
    Module.Finite.equiv_iff (ULift.moduleEquiv (R := A)
      (M := ↥((chartCech (A := A) (n := n) (M := M) ℳ).homology q)))
  have hB : Module.Finite A
        ↥((chartCechLift.{u_1, u_2, u_3} (A := A) (n := n) (M := M) ℳ).homology q) ↔
      Module.Finite A
        ↥((chartCechLift.{u_1, u_3, u_2} (A := A) (n := n) (M := M') ℳ').homology q) :=
    Module.Finite.equiv_iff hHom.toLinearEquiv
  have hA3 : Module.Finite A
        ↥((chartCechLift.{u_1, u_3, u_2} (A := A) (n := n) (M := M') ℳ').homology q) ↔
      Module.Finite A ↥((ModuleCat.uliftFunctor.{u_2, max u_1 u_3} A).obj
        ((chartCech (A := A) (n := n) (M := M') ℳ').homology q)) :=
    Module.Finite.equiv_iff hF₂.toLinearEquiv
  have hA4 : Module.Finite A ↥((ModuleCat.uliftFunctor.{u_2, max u_1 u_3} A).obj
        ((chartCech (A := A) (n := n) (M := M') ℳ').homology q)) ↔
      Module.Finite A ↥((chartCech (A := A) (n := n) (M := M') ℳ').homology q) :=
    Module.Finite.equiv_iff (ULift.moduleEquiv (R := A)
      (M := ↥((chartCech (A := A) (n := n) (M := M') ℳ').homology q)))
  have hfin : Module.Finite A ↥((chartCech (A := A) (n := n) (M := M) ℳ).homology q) ↔
      Module.Finite A ↥((chartCech (A := A) (n := n) (M := M') ℳ').homology q) :=
    hA2.symm.trans (hA1.symm.trans (hB.trans (hA3.trans hA4)))
  -- ### vanishing
  have hsub1 : Subsingleton
        ↥((chartCechLift.{u_1, u_2, u_3} (A := A) (n := n) (M := M) ℳ).homology q) ↔
      Subsingleton ↥((ModuleCat.uliftFunctor.{u_3, max u_1 u_2} A).obj
        ((chartCech (A := A) (n := n) (M := M) ℳ).homology q)) :=
    subsingleton_linearEquiv hF₁.toLinearEquiv
  have hsub2 : Subsingleton ↥((ModuleCat.uliftFunctor.{u_3, max u_1 u_2} A).obj
        ((chartCech (A := A) (n := n) (M := M) ℳ).homology q)) ↔
      Subsingleton ↥((chartCech (A := A) (n := n) (M := M) ℳ).homology q) :=
    subsingleton_ulift
  have hsubB : Subsingleton
        ↥((chartCechLift.{u_1, u_2, u_3} (A := A) (n := n) (M := M) ℳ).homology q) ↔
      Subsingleton ↥((chartCechLift.{u_1, u_3, u_2} (A := A) (n := n) (M := M') ℳ').homology q) :=
    subsingleton_linearEquiv hHom.toLinearEquiv
  have hsub3 : Subsingleton
        ↥((chartCechLift.{u_1, u_3, u_2} (A := A) (n := n) (M := M') ℳ').homology q) ↔
      Subsingleton ↥((ModuleCat.uliftFunctor.{u_2, max u_1 u_3} A).obj
        ((chartCech (A := A) (n := n) (M := M') ℳ').homology q)) :=
    subsingleton_linearEquiv hF₂.toLinearEquiv
  have hsub4 : Subsingleton ↥((ModuleCat.uliftFunctor.{u_2, max u_1 u_3} A).obj
        ((chartCech (A := A) (n := n) (M := M') ℳ').homology q)) ↔
      Subsingleton ↥((chartCech (A := A) (n := n) (M := M') ℳ').homology q) :=
    subsingleton_ulift
  have hsub : Subsingleton ↥((chartCech (A := A) (n := n) (M := M) ℳ).homology q) ↔
      Subsingleton ↥((chartCech (A := A) (n := n) (M := M') ℳ').homology q) :=
    hsub2.symm.trans (hsub1.symm.trans (hsubB.trans (hsub3.trans hsub4)))
  have hZ : CategoryTheory.Limits.IsZero
        ((chartCech (A := A) (n := n) (M := M) ℳ).homology q) ↔
      CategoryTheory.Limits.IsZero
        ((chartCech (A := A) (n := n) (M := M') ℳ').homology q) :=
    (ModuleCat.isZero_iff_subsingleton).trans (hsub.trans
      (ModuleCat.isZero_iff_subsingleton).symm)
  exact ⟨hfin, hZ⟩

end Work.DSCOH
