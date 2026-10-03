/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `Rat(U)` and subgroups: restriction of scalars, and the source of an element

[JZLA20, Proposition 4.4] attaches to every `α ∈ Rat(U)` a finitely generated subgroup
`source(α) ≤ U` such that `α ∈ Rat(source(α)) · U`, with the appropriate minimality property.
The map `Rat(source(α)) → Rat(U)` used there is the universal morphism of rational
`source(α)`-semirings obtained from the *restriction of scalars* of the `U`-biset structure of
`Rat(U)` along the inclusion `source(α) ↪ U`; that restriction is defined in this file.

It is the only ingredient of the *statement* of Proposition 4.4 that is not already provided by
`Rat/RTerm.lean` (`RatU U`, `RatU.lift`).
-/
import Mathlib
import Submission.Work.ORHughesFree.Rat.RTerm

set_option autoImplicit false

namespace Work.ORHughesFree

namespace RatU

variable {U : Type} [Group U]

/-- **Restriction of scalars** of the rational `U`-semiring `Rat(U)` along a subgroup `V ≤ U`:
`Rat(U)` is a rational `V`-semiring with the same rational operation, acting through `V ↪ U`. -/
noncomputable def restrictScalars (V : Subgroup U) : RationalUSemiring ↥V (RatU U) where
  ratOp := (rational (U := U)).ratOp
  ratOp_zero := (rational (U := U)).ratOp_zero
  smul v x := (rational (U := U)).smul (v : U) x
  smulRight x v := (rational (U := U)).smulRight x (v : U)
  smul_eq_mul v r := (rational (U := U)).smul_eq_mul (v : U) r
  smulRight_eq_mul r v := (rational (U := U)).smulRight_eq_mul r (v : U)
  smul_mul u v := (rational (U := U)).smul_mul (u : U) (v : U)
  smul_one_one := (rational (U := U)).smul_one_one
  smulRight_one_one := (rational (U := U)).smulRight_one_one
  smulRight_one v := (rational (U := U)).smulRight_one (v : U)
  rat_smul u v r := (rational (U := U)).rat_smul (u : U) (v : U) r

theorem restrictScalars_ratOp (V : Subgroup U) :
    (restrictScalars V).ratOp = (rational (U := U)).ratOp := rfl

theorem restrictScalars_smul (V : Subgroup U) (v : ↥V) (x : RatU U) :
    (restrictScalars V).smul v x = (rational (U := U)).smul (v : U) x := rfl

theorem restrictScalars_smulRight (V : Subgroup U) (x : RatU U) (v : ↥V) :
    (restrictScalars V).smulRight x v = (rational (U := U)).smulRight x (v : U) := rfl

/-- The **canonical map** `Rat(V) →+* Rat(U)` for a subgroup `V ≤ U`, induced by the universal
property of `Rat(V)` applied to `Rat(U)` with its restricted rational `V`-semiring structure. -/
noncomputable def ofSubgroup (V : Subgroup U) : RatU ↥V →+* RatU U :=
  lift (RatU U) (restrictScalars V)

/-- The canonical map `Rat(V) →+* Rat(U)` is the unique morphism of rational `V`-semirings. -/
theorem ofSubgroup_isHom (V : Subgroup U) :
    IsRationalUSemiringHom (rational (U := ↥V)) (restrictScalars V) (ofSubgroup V) :=
  lift_isHom (RatU U) (restrictScalars V)

end RatU

end Work.ORHughesFree
