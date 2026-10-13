import Mathlib
import Submission.Work.DSCOH.Chart
import Submission.Work.DSCOH.cechDiff_comp

/-!
# Transporting the chart Čech complex to a larger universe

The three modules of `Work.DSCOH.homology_finite_of_graded_shortExact` live in independent
universes, so the three chart Čech complexes are objects of different categories
`CochainComplex (ModuleCat.{·} A) ℕ` and cannot be compared directly.  This file provides:

* `uliftLinearMap`, the `ULift` of a linear map;
* `uliftFunctor_homologyIso`, the compatibility of `ModuleCat.uliftFunctor` with homology;
* `moduleFinite_uliftFunctor_obj`, the invariance of `Module.Finite` under `uliftFunctor`;
* `chartCechULift`, the chart Čech complex "with every degreewise module lifted by `ULift`",
  whose terms live in a single (large) universe.
-/

open MvPolynomial CategoryTheory Limits

namespace Work.DSCOH

set_option allowUnsafeReducibility true
attribute [local reducible] chartCech chartCechOf

universe u uA v v' v'' w w' w''

section Ulift

variable {R : Type u} [Ring R]
variable {X : Type v} {Y : Type v'} [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]

/-- The `ULift` of a linear map, `f ↦ ULift.moduleEquiv.symm ∘ f ∘ ULift.moduleEquiv`. -/
noncomputable def uliftLinearMap (f : X →ₗ[R] Y) :
    ULift.{v'', v} X →ₗ[R] ULift.{v'', v'} Y :=
  (ULift.moduleEquiv (R := R) (M := Y)).symm.toLinearMap.comp
    (f.comp (ULift.moduleEquiv (R := R) (M := X)).toLinearMap)

lemma uliftLinearMap_apply (f : X →ₗ[R] Y) (x : ULift.{v'', v} X) :
    uliftLinearMap f x =
      (ULift.moduleEquiv (R := R) (M := Y)).symm
        (f ((ULift.moduleEquiv (R := R) (M := X)) x)) :=
  rfl

lemma uliftLinearMap_zero : uliftLinearMap (0 : X →ₗ[R] Y) = 0 := by
  ext x
  simp only [uliftLinearMap_apply, map_zero, LinearMap.zero_apply]

lemma uliftLinearMap_injective (f : X →ₗ[R] Y) (hf : Function.Injective f) :
    Function.Injective (uliftLinearMap f) := by
  intro x y h
  have h2 : (ULift.moduleEquiv (R := R) (M := Y)) (uliftLinearMap f x) =
      (ULift.moduleEquiv (R := R) (M := Y)) (uliftLinearMap f y) := by rw [h]
  rw [uliftLinearMap_apply, LinearEquiv.apply_symm_apply, uliftLinearMap_apply,
    LinearEquiv.apply_symm_apply] at h2
  exact (ULift.moduleEquiv (R := R) (M := X)).injective (hf h2)

lemma uliftLinearMap_surjective (f : X →ₗ[R] Y) (hf : Function.Surjective f) :
    Function.Surjective (uliftLinearMap f) := by
  intro y
  obtain ⟨x, hx⟩ := hf ((ULift.moduleEquiv (R := R) (M := Y)) y)
  refine ⟨(ULift.moduleEquiv (R := R) (M := X)).symm x, ?_⟩
  rw [uliftLinearMap_apply, LinearEquiv.apply_symm_apply, hx]
  exact (ULift.moduleEquiv (R := R) (M := Y)).symm_apply_apply y

lemma uliftLinearMap_eq_zero_iff {Z : Type*} [AddCommGroup Z] [Module R Z]
    (g : Y →ₗ[R] Z) (y : ULift.{v'', v'} Y) :
    uliftLinearMap g y = 0 ↔ g ((ULift.moduleEquiv (R := R) (M := Y)) y) = 0 := by
  constructor
  · intro h
    have hh := congrArg (ULift.moduleEquiv (R := R) (M := Z)) h
    rwa [uliftLinearMap_apply, LinearEquiv.apply_symm_apply, map_zero] at hh
  · intro h
    apply (ULift.moduleEquiv (R := R) (M := Z)).injective
    rw [map_zero, uliftLinearMap_apply, LinearEquiv.apply_symm_apply]
    exact h

lemma uliftLinearMap_exact (f : X →ₗ[R] Y) {Z : Type*} [AddCommGroup Z] [Module R Z]
    (g : Y →ₗ[R] Z) (h : Function.Exact f g) :
    Function.Exact (uliftLinearMap f) (uliftLinearMap g) := by
  intro z
  rw [uliftLinearMap_eq_zero_iff]
  constructor
  · intro hz
    obtain ⟨x, hx⟩ := (h ((ULift.moduleEquiv (R := R) (M := Y)) z)).mp hz
    refine ⟨(ULift.moduleEquiv (R := R) (M := X)).symm x, ?_⟩
    apply (ULift.moduleEquiv (R := R) (M := Y)).injective
    simp only [uliftLinearMap_apply, LinearEquiv.apply_symm_apply, hx]
  · rintro ⟨x, rfl⟩
    simp only [uliftLinearMap_apply, LinearEquiv.apply_symm_apply]
    exact h.apply_apply_eq_zero _

lemma uliftLinearMap_comp (f : X →ₗ[R] Y) {Z : Type*} [AddCommGroup Z] [Module R Z]
    (g : Y →ₗ[R] Z) :
    (uliftLinearMap g).comp (uliftLinearMap f) = uliftLinearMap (g.comp f) := by
  ext x
  simp only [LinearMap.comp_apply, uliftLinearMap_apply, LinearEquiv.apply_symm_apply]

variable {X' : Type v} [AddCommGroup X'] [Module R X']
variable {Y' : Type v} [AddCommGroup Y'] [Module R Y']

/-- `uliftFunctor.map` of a linear map is the `ULift` of that linear map. -/
lemma uliftFunctor_map_ofHom (f : X' →ₗ[R] Y') :
    (ModuleCat.uliftFunctor.{v'', v} R).map (ModuleCat.ofHom f) =
      ModuleCat.ofHom (uliftLinearMap f) := rfl

/-- `uliftFunctor` preserves homology. -/
noncomputable def uliftFunctor_homologyIso (C : CochainComplex (ModuleCat.{v} R) ℕ) (i : ℕ) :
    ((ModuleCat.uliftFunctor.{v'', v} R).mapHomologicalComplex (ComplexShape.up ℕ) |>.obj C).homology i
      ≅ (ModuleCat.uliftFunctor.{v'', v} R).obj (C.homology i) := by
  haveI : (ModuleCat.uliftFunctor.{v'', v} R).PreservesHomology := inferInstance
  have hsc : ((ModuleCat.uliftFunctor.{v'', v} R).mapHomologicalComplex
      (ComplexShape.up ℕ) |>.obj C).sc i =
      (C.sc i).map (ModuleCat.uliftFunctor.{v'', v} R) := rfl
  dsimp only [HomologicalComplex.homology]
  rw [hsc]
  exact ShortComplex.mapHomologyIso _ _

/-- Finiteness is preserved and reflected by `uliftFunctor`. -/
theorem moduleFinite_uliftFunctor_obj {X : ModuleCat.{v} R} :
    Module.Finite R ((ModuleCat.uliftFunctor.{v'', v} R).obj X) ↔ Module.Finite R X :=
  Module.Finite.equiv_iff (ULift.moduleEquiv (R := R) (M := ↥X))

end Ulift

variable {A : Type uA} [CommRing A] {n : ℕ}

/-- The chart Čech complex of `ℳ`, with every degreewise module transported to a larger
universe by `ULift`. -/
noncomputable abbrev chartCechULift.{u1, u2, u3} {A : Type u1} [CommRing A] {n : ℕ}
    {M : Type u2} [AddCommGroup M] [Module A M]
    [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] :
    CochainComplex (ModuleCat.{max u1 (max u2 u3)} A) ℕ :=
  CochainComplex.of
    (fun i => ModuleCat.of A (ULift.{u3, max u1 u2}
      (CechTerm (A := A) (n := n) (M := M) ℳ i)))
    (fun i => ModuleCat.ofHom (uliftLinearMap (cechDiff (A := A) (n := n) (M := M) ℳ i)))
    (fun i => by
      rw [← ModuleCat.ofHom_comp, uliftLinearMap_comp, cechDiff_comp, uliftLinearMap_zero,
        ModuleCat.ofHom_zero])

@[simp] lemma chartCechULift_X {M : Type w} [AddCommGroup M] [Module A M]
    [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] (i : ℕ) :
    (chartCechULift.{uA, w, v''} (A := A) (n := n) ℳ).X i =
      ModuleCat.of A (ULift.{v'', max uA w}
        (CechTerm (A := A) (n := n) (M := M) ℳ i)) := rfl

@[simp] lemma chartCechULift_d {M : Type w} [AddCommGroup M] [Module A M]
    [Module (Poly A n) M] [IsScalarTower A (Poly A n) M]
    (ℳ : ℕ → Submodule A M) [SetLike.GradedSMul (homSub A n) ℳ] (i : ℕ) :
    (chartCechULift.{uA, w, v''} (A := A) (n := n) ℳ).d i (i + 1) =
      ModuleCat.ofHom (uliftLinearMap (cechDiff (A := A) (n := n) (M := M) ℳ i)) := by
  simp only [chartCechULift, CochainComplex.of_d]

end Work.DSCOH

