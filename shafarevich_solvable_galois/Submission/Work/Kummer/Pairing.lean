/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Kummer pairing

For `K` a field containing a primitive `n`-th root of unity `ζ` and `L/K` a finite Galois
extension, the Kummer pairing is the map
`Gal(L/K) × (Kˣ ∩ (Lˣ)^n) → μ_n`, `(σ, a) ↦ σ α / α` where `α ^ n = a`.

In this file we package it as a bilinear map

* `kummerCharacterHom : (Kˣ ∩ (Lˣ)^n) →* (Gal(L/K) →* μ_n)`,
* `kummerPairing : ((Kˣ ∩ (Lˣ)^n)/(Kˣ)^n) →* (Gal(L/K) →* μ_n)`,

and prove that the second map is injective (its kernel is exactly `(Kˣ)^n`).
-/
import Mathlib.FieldTheory.KummerExtension
import Submission.Work.Kummer.Defs
import Submission.Work.Kummer.kummerCharacter_mul
import Submission.Work.Kummer.kummerCharacter_eq_one_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Kummer

open IntermediateField

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {n : ℕ} [NeZero n] {ζ : K}

/-- The Kummer pairing as a bilinear map `(Kˣ ∩ (Lˣ)^n) →* (Gal(L/K) →* μ_n)`. -/
noncomputable def kummerCharacterHom (hζ : IsPrimitiveRoot ζ n) :
    kummerSubgroup n K L →* (Gal(L/K) →* rootsOfUnity n K) where
  toFun := kummerCharacter hζ
  map_one' := by
    simpa using kummerCharacter_eq_one_of_mem_nthPower hζ
      (one_mem ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)))
  map_mul' := fun a b => kummerCharacter_mul hζ a b

@[simp]
lemma kummerCharacterHom_apply (hζ : IsPrimitiveRoot ζ n) (a : kummerSubgroup n K L) :
    kummerCharacterHom hζ a = kummerCharacter hζ a := rfl

/-- The Kummer pairing, descended to `(Kˣ ∩ (Lˣ)^n)/(Kˣ)^n`. -/
noncomputable def kummerPairing (hζ : IsPrimitiveRoot ζ n) :
    kummerQuotient n K L →* (Gal(L/K) →* rootsOfUnity n K) :=
  QuotientGroup.lift ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L))
    (kummerCharacterHom hζ) (fun x hx => by
      show kummerCharacterHom hζ x = 1
      exact kummerCharacter_eq_one_of_mem_nthPower hζ hx)

@[simp]
lemma kummerPairing_mk (hζ : IsPrimitiveRoot ζ n) (x : kummerSubgroup n K L) :
    kummerPairing hζ (QuotientGroup.mk' _ x) = kummerCharacter hζ x :=
  QuotientGroup.lift_mk' _ _ x

/-- The Kummer pairing is injective: the kernel of the Kummer character is exactly the subgroup
of `n`-th powers of `K`. -/
theorem kummerPairing_injective (hζ : IsPrimitiveRoot ζ n) [FiniteDimensional K L]
    [IsGalois K L] : Function.Injective (kummerPairing (K := K) (L := L) hζ) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  refine le_antisymm (fun x hx => ?_) bot_le
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective
    ((nthPowerSubgroup n Kˣ).subgroupOf (kummerSubgroup n K L)) x
  rw [MonoidHom.mem_ker, kummerPairing_mk] at hx
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  exact (kummerCharacter_eq_one_iff hζ a).mp hx

end Work.Kummer
