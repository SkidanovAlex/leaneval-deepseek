/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (one-relator coherence project)

# The `*`-involution on an Ore localization

Let `R` be a `*`-ring and `S ≤ R` a `star`-stable left Ore submonoid
(`hS : ∀ s : S, star (s : R) ∈ S`).  Then the Ore localization `OreLocalization S R`
carries an anti-linear involution extending `star` on `R`:
`st (s⁻¹ * r) = star r * (star s)⁻¹` in the fractional notation of the localization.

Mathlib has no such construction, so we build it here.  The idea is that a map which is
additive and anti-multiplicative is the same thing as a *ring* homomorphism into the opposite
ring.  Writing `f r = op (star r)` and `fS s = op (star s)` (viewing the images in the
localization, where `star s` is a unit because `S` is `star`-stable), the universal property
`OreLocalization.universalHom` produces a ring homomorphism
`starU : OreLocalization S R →+* (OreLocalization S R)ᵐᵒᵖ`.  Composing with `unop` gives the
desired anti-involution.  Additivity, anti-multiplicativity, the value on numerators and the
involution property all follow from `OreLocalization.universalHom_unique`.
-/
import Mathlib
import Submission.Work.ORVonNeumann.GroupAlgebraStar

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.ORVonNeumann.Ore

open OreLocalization

variable {R : Type*} [Ring R] [StarRing R] {S : Submonoid R} [OreSet S]

/-- The endomorphism of the submonoid `S` of denominators induced by `star`, using the
hypothesis `hS` that `S` is stable under `star`. -/
def starSub (hS : ∀ s : S, star (s : R) ∈ S) (s : S) : S :=
  ⟨star (s : R), hS s⟩

theorem starSub_coe (hS : ∀ s : S, star (s : R) ∈ S) (s : S) :
    ((starSub hS s : S) : R) = star (s : R) := rfl

theorem starSub_one (hS : ∀ s : S, star (s : R) ∈ S) : starSub hS 1 = 1 :=
  Subtype.ext (by simp [starSub])

/-- `star` reverses the multiplication, so `starSub` reverses it as well. -/
theorem starSub_mul (hS : ∀ s : S, star (s : R) ∈ S) (s t : S) :
    starSub hS (s * t) = starSub hS t * starSub hS s :=
  Subtype.ext (by simp [starSub, star_mul])

theorem starSub_invol (hS : ∀ s : S, star (s : R) ∈ S) (s : S) :
    starSub hS (starSub hS s) = s :=
  Subtype.ext (by simp [starSub])

/-- The value of the unit `OreLocalization.numeratorUnit s` in the localization. -/
theorem coe_numeratorUnit (s : S) :
    (↑(numeratorUnit s) : OreLocalization S R) = (s : R) /ₒ 1 := rfl

/-- The canonical monoid homomorphism from the denominators to the units of the localization. -/
noncomputable def numUnitHom : S →* (OreLocalization S R)ˣ where
  toFun s := numeratorUnit s
  map_one' := by
    ext
    rw [coe_numeratorUnit, Units.val_one]
    exact OreLocalization.one_def.symm
  map_mul' s t := by
    ext
    rw [coe_numeratorUnit, Units.val_mul, coe_numeratorUnit, coe_numeratorUnit,
      Submonoid.coe_mul, OreLocalization.mul_div_one]

/-- The image of the denominators in the units of the opposite ring.  Since `star` is
anti-multiplicative, the composite `s ↦ op (star s)` is multiplicative. -/
noncomputable def fS (hS : ∀ s : S, star (s : R) ∈ S) :
    S →* ((OreLocalization S R)ᵐᵒᵖ)ˣ where
  toFun s := Units.opEquiv.symm (MulOpposite.op (numeratorUnit (starSub hS s)))
  map_one' := by
    ext
    rw [Units.coe_opEquiv_symm, MulOpposite.unop_op, starSub_one hS, Units.val_one]
    show MulOpposite.op (↑(numeratorUnit (1 : S)) : OreLocalization S R) =
      MulOpposite.op (1 : OreLocalization S R)
    congr 1
    exact OreLocalization.one_def.symm
  map_mul' s t := by
    ext
    simp only [Units.coe_opEquiv_symm, MulOpposite.unop_op, Units.val_mul, coe_numeratorUnit]
    rw [← MulOpposite.op_mul, starSub_mul hS s t]
    apply congrArg MulOpposite.op
    rw [Submonoid.coe_mul, ← OreLocalization.mul_div_one (p := (starSub hS t : R))
      (r := (starSub hS s : R)) (s := (1 : S))]

/-- The ring homomorphism `R →+* (R[S⁻¹])ᵐᵒᵖ`, `r ↦ op (star r)`. -/
noncomputable def starHom (hS : ∀ s : S, star (s : R) ∈ S) :
    R →+* (OreLocalization S R)ᵐᵒᵖ where
  toFun r := MulOpposite.op (OreLocalization.numeratorRingHom (star r))
  map_one' := by rw [star_one, map_one, MulOpposite.op_one]
  map_zero' := by rw [star_zero, map_zero, MulOpposite.op_zero]
  map_add' r r' := by rw [star_add, map_add, MulOpposite.op_add]
  map_mul' r r' := by rw [star_mul, map_mul, MulOpposite.op_mul]

theorem starHom_hf (hS : ∀ s : S, star (s : R) ∈ S) (s : S) :
    (starHom hS (s : R)) = (fS hS s).val := by
  change MulOpposite.op (OreLocalization.numeratorRingHom (star (s : R))) =
    (↑(Units.opEquiv.symm (MulOpposite.op (numeratorUnit (starSub hS s)))) :
      (OreLocalization S R)ᵐᵒᵖ)
  rw [Units.coe_opEquiv_symm, MulOpposite.unop_op, coe_numeratorUnit,
    OreLocalization.numeratorRingHom_apply]
  rfl

/-- The anti-linear involution of the Ore localization, as a ring homomorphism into the
opposite ring. -/
noncomputable def starU (hS : ∀ s : S, star (s : R) ∈ S) :
    OreLocalization S R →+* (OreLocalization S R)ᵐᵒᵖ :=
  OreLocalization.universalHom (starHom hS) (fS hS) (starHom_hf hS)

/-- The anti-linear involution of the Ore localization. -/
noncomputable def starOre (hS : ∀ s : S, star (s : R) ∈ S) (x : OreLocalization S R) :
    OreLocalization S R :=
  MulOpposite.unop (starU hS x)

theorem starOre_zero (hS : ∀ s : S, star (s : R) ∈ S) : starOre hS 0 = 0 := by
  simp [starOre, starU]

theorem starOre_one (hS : ∀ s : S, star (s : R) ∈ S) : starOre hS 1 = 1 := by
  simp [starOre, starU]

theorem starOre_add (hS : ∀ s : S, star (s : R) ∈ S) (x y : OreLocalization S R) :
    starOre hS (x + y) = starOre hS x + starOre hS y := by
  simp [starOre, starU]

theorem starOre_mul (hS : ∀ s : S, star (s : R) ∈ S) (x y : OreLocalization S R) :
    starOre hS (x * y) = starOre hS y * starOre hS x := by
  simp [starOre, starU, MulOpposite.unop_mul]

theorem starOre_num (hS : ∀ s : S, star (s : R) ∈ S) (r : R) :
    starOre hS (OreLocalization.numeratorRingHom r) =
      OreLocalization.numeratorRingHom (star r) := by
  have h : starU hS (OreLocalization.numeratorRingHom r) = starHom hS r :=
    OreLocalization.universalHom_commutes (starHom hS) (fS hS) (starHom_hf hS)
  show MulOpposite.unop (starU hS (OreLocalization.numeratorRingHom r)) = _
  rw [h]
  rfl

/-- The anti-linear involution of the Ore localization is an involution. -/
theorem starOre_invol (hS : ∀ s : S, star (s : R) ∈ S) (x : OreLocalization S R) :
    starOre hS (starOre hS x) = x := by
  -- `starOre ∘ starOre` is a ring homomorphism fixing all numerators, hence it is the identity
  -- by the universal property of the Ore localization.
  let φ : OreLocalization S R →+* OreLocalization S R :=
  { toFun := fun x => starOre hS (starOre hS x)
    map_one' := by simp [starOre_one hS]
    map_zero' := by simp [starOre_zero hS]
    map_add' := by intro a b; simp [starOre_add hS]
    map_mul' := by intro a b; simp [starOre_mul hS] }
  have hf' : ∀ s : S, OreLocalization.numeratorRingHom (s : R) = (numUnitHom s).val :=
    fun s => rfl
  have h1 : φ = OreLocalization.universalHom
      (OreLocalization.numeratorRingHom (S := S)) (numUnitHom (S := S)) hf' :=
    OreLocalization.universalHom_unique (OreLocalization.numeratorRingHom (S := S))
      (numUnitHom (S := S)) hf' φ (by
        intro r
        change starOre hS (starOre hS (OreLocalization.numeratorRingHom r)) =
          OreLocalization.numeratorRingHom r
        rw [starOre_num hS, starOre_num hS, star_star])
  have h2 : (RingHom.id (OreLocalization S R)) = OreLocalization.universalHom
      (OreLocalization.numeratorRingHom (S := S)) (numUnitHom (S := S)) hf' :=
    OreLocalization.universalHom_unique (OreLocalization.numeratorRingHom (S := S))
      (numUnitHom (S := S)) hf' (RingHom.id _) (by intro r; simp)
  have h3 : φ = RingHom.id (OreLocalization S R) := h1.trans h2.symm
  have h4 := DFunLike.congr_fun h3 x
  simpa [φ] using h4

theorem star_oreLocalization {R : Type*} [Ring R] [StarRing R] {S : Submonoid R} [OreLocalization.OreSet S] (hS : ∀ s : S, star (s : R) ∈ S) : ∃ st : OreLocalization S R → OreLocalization S R, st 0 = 0 ∧ st 1 = 1 ∧ (∀ x y, st (x + y) = st x + st y) ∧ (∀ x y, st (x * y) = st y * st x) ∧ (∀ x, st (st x) = x) ∧ (∀ r : R, st (OreLocalization.numeratorRingHom r) = OreLocalization.numeratorRingHom (star r)) :=
  ⟨starOre hS, starOre_zero hS, starOre_one hS, starOre_add hS, starOre_mul hS,
    starOre_invol hS, starOre_num hS⟩

end Work.ORVonNeumann.Ore
