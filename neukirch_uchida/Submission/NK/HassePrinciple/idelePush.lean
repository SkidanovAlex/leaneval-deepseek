/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Brick 1 (first half): the push-forward of idèles, and the transition map of the idèle level system

Umbrella development: `Submission/Work/HassePrinciple/` (the limit passage, README §13.5).

`NK.HassePrinciple.IdelePushSpec K L` (`IdelesColimit.lean`) pins, for a finite extension `L/K` of
number fields, the data of the push-forward of idèles `𝕀_K →* 𝕀_L`: a place `u w` of `K` below each
place `w` of `L`, and a monoid homomorphism whose `w`-component is the `(u w)`-component of the
input pushed along the local unit embedding at `w`.

This file discharges that specification from the two ingredients already present in
`NK.GlobalCFT.Inclusion`:

* `globalCFT_exists_placeUnder` — a place of `K` below a given place of `L`;
* `globalCFT_ideleInclusion_exists` — the restricted-product construction of the push-forward with
  exactly this componentwise formula (cofinite support and multiplicativity included).

These are the transition maps of the idèle level system `L ↦ IdeleLevelH2 V L`, and hence the first
brick of the colimit idèle group `𝕀_{LE}` and of the limit Hasse–Brauer–Noether result for the
infinite base `E = K'^U`.
-/

import Submission.NK.HassePrinciple.IdelesColimit
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists

open CategoryTheory Representation
open NK.GlobalCFT
open scoped NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NK.HassePrinciple

/-- **The push-forward of idèles along a finite extension of number fields**, i.e. the specification
`NK.HassePrinciple.IdelePushSpec K L` of the transition map of the idèle level system. -/
theorem idelePush {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : IdelePushSpec K L := by
  classical
  choose u hu using fun w : Place L =>
    NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w
  obtain ⟨φ, hφ⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists (K := K) (L := L) u hu
  exact ⟨φ, u, hu, hφ⟩

/-! ## The canonical push-forward and its place choice

Fixing the data of `NK.HassePrinciple.IdelePushSpec` once and for all makes the transition map of
the idèle level system expressible as a definition rather than as chosen data: the push-forward
`idelePushHom`, the place choice `idelePushPlace` with `idelePushPlace_liesOver`, and the
computation rule `idelePushHom_apply`. -/

/-- **The canonical push-forward of idèles along a finite extension of number fields.** -/
noncomputable def idelePushHom (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : 𝕀[K] →* 𝕀[L] :=
  Classical.choose (idelePush (K := K) (L := L))

/-- **The canonical choice of a place of `K` below a place of `L`.** -/
noncomputable def idelePushPlace (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Place L → Place K :=
  Classical.choose (Classical.choose_spec (idelePush (K := K) (L := L)))

/-- The chosen place does lie below. -/
theorem idelePushPlace_liesOver (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (w : Place L) :
    Place.LiesOver w (idelePushPlace K L w) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (idelePush (K := K) (L := L)))) w

/-- **The computation rule for the canonical push-forward.** -/
theorem idelePushHom_apply (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (x : 𝕀[K]) (w : Place L) :
    idelePushHom K L x w
      = Place.localAlgebraMapUnits w (idelePushPlace K L w) (idelePushPlace_liesOver K L w)
          (x (idelePushPlace K L w)) :=
  Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (idelePush (K := K) (L := L)))) x w


/-! ## The level-to-level push-forward (brick 1b's coefficient map)

To feed the idèle level system, the push-forward is needed between two *levels*
`L ≤ L'` of `FiniteGaloisIntermediateField K K'`.  This requires an `Algebra ↥L ↥L'` structure, which
Mathlib does not provide as an instance for intermediate fields; it is supplied here from
`IntermediateField.inclusion` (whose `↥E →ₐ[K] ↥F` is turned into a `RingHom` and then into an algebra
structure).  With it, the place-level statement `IdelePushSpecLevel` — and its proof, by the same
three lines as `idelePush` — are available for the transition map of the level system. -/

/-- **The `K`-algebra structure of a level on a larger level.**  Mathlib has no instance
`Algebra ↥L ↥L'` for intermediate fields; this is the inclusion `↥L →ₐ[K] ↥L'` turned into an algebra
structure, and it is what makes `NK.HassePrinciple.idelePushHom ↥L ↥L'` stateable. -/
noncomputable def levelAlgebra {K K' : Type} [Field K] [Field K'] [Algebra K K']
    (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') : Algebra ↥L ↥L' :=
  ((IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff L L').mp h)).toRingHom).toAlgebra


/-- **The `K`-module structure of a level over a smaller level is finite.**  With the algebra
structure `levelAlgebra L L' h` (which Mathlib lacks), the tower `K → ↥L → ↥L'` is a scalar tower
(`IsScalarTower.of_algebraMap_eq`, the two algebra maps being the coerced inclusions), so
`↥L'` is finite-dimensional over `↥L` by `Module.Finite.of_restrictScalars_finite`.  This is the
second instance brick 1b needs in order to state `idelePush` between two levels. -/
theorem levelFiniteDimensional {K K' : Type} [Field K] [Field K'] [Algebra K K']
    (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L') :
    letI : Algebra ↥L ↥L' := levelAlgebra L L' h
    FiniteDimensional ↥L ↥L' := by
  letI : Algebra ↥L ↥L' := levelAlgebra L L' h
  haveI : IsScalarTower K ↥L ↥L' := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  exact Module.Finite.of_restrictScalars_finite K ↥L ↥L'




/-- **Brick 1b's coefficient map: the push-forward of idèles between two levels.**  For finite Galois
levels `L ≤ L'` of `K'/K`, a monoid homomorphism `𝕀_↥L →* 𝕀_↥L'` whose `w`-component is the
`(u w)`-component of the input pushed along the local unit embedding at `w`, for a choice of a place
`u w` of `↥L` below each place `w` of `↥L'`.

The algebra structure `Algebra ↥L ↥L'` and the module finiteness are passed as instance arguments
(the caller supplies `NK.HassePrinciple.levelAlgebra L L' h` and
`NK.HassePrinciple.levelFiniteDimensional L L' h`), since Mathlib has neither for intermediate
fields.  The proof is the same three lines as `idelePush`: `globalCFT_exists_placeUnder` supplies the
place below each place and `globalCFT_ideleInclusion_exists` the restricted-product construction. -/
theorem idelePushLevel {K K' : Type} [Field K] [NumberField K] [Field K'] [Algebra K K']
    (L L' : FiniteGaloisIntermediateField K K') (h : L ≤ L')
    [Algebra ↥L ↥L'] [FiniteDimensional ↥L ↥L'] :
    ∃ (φ : 𝕀[↥L] →* 𝕀[↥L']) (u : Place ↥L' → Place ↥L)
      (hu : ∀ w : Place ↥L', Place.LiesOver w (u w)),
      ∀ (x : 𝕀[↥L]) (w : Place ↥L'),
        φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)) := by
  classical
  choose u hu using fun w : Place ↥L' =>
    NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := ↥L) (L := ↥L') w
  obtain ⟨φ, hφ⟩ :=
    NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists (K := ↥L) (L := ↥L') u hu
  exact ⟨φ, u, hu, hφ⟩

end NK.HassePrinciple
