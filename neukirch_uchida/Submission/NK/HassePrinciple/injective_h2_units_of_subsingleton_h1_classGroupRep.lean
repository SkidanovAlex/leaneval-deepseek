/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The edge map `H²(Γ, Lˣ) → H²(Γ, 𝕀_L)` is injective when `H¹(Γ, C_L) = 0`

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 2, §12.4).

Let `L/K` be a finite Galois extension of number fields with group `Γ = Gal(L/K)`.  The sequence
of `CoeffInt`-linear `Γ`-representations

  `0 ⟶ Lˣ --ideleIncl--> 𝕀_L --classGroupMap--> C_L ⟶ 0`

(principal idèles, idèles, idèles modulo principal idèles) is short exact.  The long exact
cohomology sequence attached to it reads

  `H¹(Γ, C_L) --δ--> H²(Γ, Lˣ) --H²(ideleIncl)--> H²(Γ, 𝕀_L)`,

so that `H²(ideleIncl)` has kernel the image of the connecting homomorphism `δ`.  Consequently, if
`H¹(Γ, C_L) = 0`, then `H²(Γ, Lˣ) → H²(Γ, 𝕀_L)` is injective.

This is the algebraic form of the *relative Hasse–Brauer–Noether theorem*: with Shapiro's lemma for
the idèles, `H²(Γ, 𝕀_L) ≅ ∏_w H²(Γ_w, L_wˣ)`, so the injectivity of this edge map is exactly the
statement that `H²(Γ, Lˣ) = Br(L/K)` embeds into the product of the local Brauer groups
(README §12.3, item (e)).  The hypothesis `H¹(Γ, C_L) = 0` holds, in particular, for `p`-group
level groups by `NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_of_isPGroup`.

## Contents

* `NK.HassePrinciple.ideleShortComplex` — the short complex `Lˣ ⟶ 𝕀_L ⟶ C_L` of
  `CoeffInt`-linear representations;
* `NK.HassePrinciple.ideleShortComplex_shortExact` — it is short exact;
* `NK.HassePrinciple.injective_h2_units_of_subsingleton_h1_classGroupRep` — the injectivity of
  the edge map on `H²`.

## Implementation note

The coefficient ring is `CoeffInt = ULift ℤ`, whose generic `ULift.module` instance competes with
the module structure stored in a representation `A : Rep CoeffInt Γ`; as in
`Submission/Work/HassePrinciple/kummerMap_injective_of_pdivisible.lean` we give `Rep.hV1` and
`Rep.hV2` a higher local instance priority so that the `Rep`-machinery
(`forget₂ (Rep k G) (ModuleCat k)` and the reflection of exactness
`Functor.reflects_exact_of_faithful`) applies.
-/

import Mathlib
import Submission.NK.HassePrinciple.IdelesLevel

open CategoryTheory Representation
open NK.GlobalCFT

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

section IdelesShortExact

/- `ULift.module` competes with the module structure stored in a representation (see the module
docstring); prefer the structure instances, as intended. -/
attribute [local instance 10000] Rep.hV2 Rep.hV1

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The diagonal embedding `Kˣ → 𝕀_K` is injective**: an element of `Kˣ` is determined by its
images in the local fields at the places of `K`. -/
lemma principalIdele_injective (K : Type u) [Field K] [NumberField K] :
    Function.Injective (Idele.principalIdele K) := by
  intro x y h
  obtain ⟨v⟩ := (inferInstance : Nonempty (Place K))
  have hv : (Idele.principalIdele K x) v = (Idele.principalIdele K y) v := by rw [h]
  rw [Idele.principalIdele_apply, Idele.principalIdele_apply] at hv
  exact Units.map_injective (RingHom.injective (algebraMap K (Place.localField K v))) hv

/-- **The principal idèles `Lˣ ↪ 𝕀_L` are injective**, i.e. `ideleIncl` is a monomorphism of
representations. -/
lemma ideleIncl_injective (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : Function.Injective (ideleIncl K L).hom := by
  intro x y h
  change Additive.ofMul (Idele.principalIdele L (Additive.toMul x)) =
    Additive.ofMul (Idele.principalIdele L (Additive.toMul y)) at h
  exact Additive.toMul.injective (principalIdele_injective L (Additive.ofMul.injective h))

/-- **The quotient `𝕀_L ↠ C_L` is surjective**, i.e. `classGroupMap` is an epimorphism of
representations. -/
lemma classGroupMap_surjective (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : Function.Surjective (classGroupMap K L).hom := by
  intro q
  obtain ⟨x, hx⟩ := IdeleClassGroup.mk_surjective L (Additive.toMul q)
  refine ⟨Additive.ofMul x, ?_⟩
  rw [classGroupMap_apply, hx]
  exact ofMul_toMul q

/-- **The kernel of `𝕀_L ↠ C_L` is the image of `Lˣ`**: this is the exactness of the idèle
sequence `Lˣ ⟶ 𝕀_L ⟶ C_L` in the middle. -/
lemma exists_ideleIncl_eq_of_classGroupMap_eq_zero
    {x : ((ideleRep K L : Rep.{u, u, u} CoeffInt (L ≃ₐ[K] L))).V}
    (hx : (classGroupMap K L).hom x = 0) :
    ∃ y : ((unitsRep K L : Rep.{u, u, u} CoeffInt (L ≃ₐ[K] L))).V,
      (ideleIncl K L).hom y = x := by
  let x' : Additive (Idele L) := x
  have hx' : (classGroupMap K L).hom x' = 0 := hx
  have hx1 : IdeleClassGroup.mk L x'.toMul = 1 := by
    have h := hx'
    change Additive.ofMul (IdeleClassGroup.mk L x'.toMul) = 0 at h
    simpa using congrArg Additive.toMul h
  obtain ⟨k, hk⟩ := Idele.mem_principalSubgroup.mp ((QuotientGroup.eq_one_iff x'.toMul).mp hx1)
  refine ⟨Additive.ofMul k, ?_⟩
  change Additive.ofMul (Idele.principalIdele L k) = x'
  rw [hk]
  exact ofMul_toMul x'

/-- **The idèle short complex** `Lˣ --ideleIncl--> 𝕀_L --classGroupMap--> C_L` of
`CoeffInt`-linear `Gal(L/K)`-representations. -/
noncomputable def ideleShortComplex (K L : Type u) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] : ShortComplex (Rep.{u, u, u} CoeffInt (L ≃ₐ[K] L)) :=
  ShortComplex.mk (ideleIncl K L) (classGroupMap K L) (ideleIncl_comp_classGroupMap K L)

/-- **The idèle sequence is short exact**: `0 ⟶ Lˣ ⟶ 𝕀_L ⟶ C_L ⟶ 0`. -/
lemma ideleShortComplex_shortExact (K L : Type u) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] : (ideleShortComplex K L).ShortExact where
  exact := (forget₂ (Rep.{u, u, u} CoeffInt (L ≃ₐ[K] L)) (ModuleCat.{u} CoeffInt))
    |>.reflects_exact_of_faithful (ideleShortComplex K L)
      ((ShortComplex.moduleCat_exact_iff _).2 fun _ hx =>
        exists_ideleIncl_eq_of_classGroupMap_eq_zero (K := K) (L := L) hx)
  mono_f := (Rep.mono_iff_injective _).2 (ideleIncl_injective K L)
  epi_g := (Rep.epi_iff_surjective _).2 (classGroupMap_surjective K L)

end IdelesShortExact

/-- **Injectivity of the edge map `H²(Gal(L/K), Lˣ) → H²(Gal(L/K), 𝕀_L)` when
`H¹(Gal(L/K), C_L) = 0`.**

This is the algebraic half of the relative Hasse–Brauer–Noether theorem: the long exact cohomology
sequence of `0 → Lˣ → 𝕀_L → C_L → 0` exhibits the kernel of `H²(ideleIncl)` as the image of the
connecting homomorphism `δ : H¹(Gal(L/K), C_L) → H²(Gal(L/K), Lˣ)`, and `H¹(Gal(L/K), C_L) = 0`
makes that image trivial. -/
theorem injective_h2_units_of_subsingleton_h1_classGroupRep {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (h1 : Subsingleton (groupCohomology (NK.HassePrinciple.classGroupRep K L) 1)) :
    Function.Injective (fun x => ((groupCohomology.functor NK.HassePrinciple.CoeffInt
      (L ≃ₐ[K] L) 2).map (NK.HassePrinciple.ideleIncl K L)).hom x) := by
  have hij : 1 + 1 = 2 := rfl
  have hS : (ideleShortComplex K L).ShortExact := ideleShortComplex_shortExact K L
  -- Exactness of `H¹(Γ, C_L) --δ--> H²(Γ, Lˣ) --H²(ideleIncl)--> H²(Γ, 𝕀_L)`.
  have hEx := ShortComplex.Exact.moduleCat_range_eq_ker
    (groupCohomology.mapShortComplex₁_exact (k := CoeffInt) (G := L ≃ₐ[K] L) hS hij)
  have hsub : Subsingleton ↑(groupCohomology.mapShortComplex₁ hS hij).X₁ := h1
  -- `H¹(Γ, C_L) = 0`, so the image of the connecting map is trivial.
  have hfrange : LinearMap.range (groupCohomology.mapShortComplex₁ hS hij).f.hom = ⊥ :=
    (Submodule.eq_bot_iff _).mpr fun y hy => by
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hy
      rw [← hz, show z = 0 from hsub.elim z 0, map_zero]
  have hkg : LinearMap.ker (groupCohomology.mapShortComplex₁ hS hij).g.hom = ⊥ := by
    rw [← hEx, hfrange]
  intro a b hab
  have hmem : a - b ∈ LinearMap.ker
      ((groupCohomology.functor CoeffInt (L ≃ₐ[K] L) 2).map (ideleIncl K L)).hom := by
    rw [LinearMap.mem_ker]
    have hab' : ((groupCohomology.functor CoeffInt (L ≃ₐ[K] L) 2).map (ideleIncl K L)).hom a
        = ((groupCohomology.functor CoeffInt (L ≃ₐ[K] L) 2).map (ideleIncl K L)).hom b := hab
    rw [map_sub, hab', sub_self]
  have h0 : a - b = 0 := by
    rw [show LinearMap.ker
          ((groupCohomology.functor CoeffInt (L ≃ₐ[K] L) 2).map (ideleIncl K L)).hom
        = LinearMap.ker (groupCohomology.mapShortComplex₁ hS hij).g.hom from rfl, hkg] at hmem
    exact (Submodule.mem_bot CoeffInt).mp hmem
  exact sub_eq_zero.mp h0

end NK.HassePrinciple
