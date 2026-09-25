import Submission.NK.Reconstruct.NumFieldIn

/-!
# The compositum of two finite number-field levels

`NK.Reconstruct.NumFieldIn ℚ Ω` is a finite number-field level of `Ω/ℚ` (`NumFieldIn.lean`).  For
Shimizu's Lemma 4f.4 in the general form (for arbitrary number fields as base fields, see
`Submission/Work/Reconstruct/lemma4f4_gen.lean`) one needs the compositum `K₁K₂` of two such levels,
again as a finite number-field level: this is the middle field to which the identity
`σ̄ ∘ π_{L/K₁} = π_{L/K₂}` has to be descended.

## The instance diamond, and how it is avoided

Writing `numberField := NumberField.mk` for the compositum does *not* work: `NumberField ↥S` unfolds
to `FiniteDimensional ℚ ↥S`, and instance search resolves the `ℚ`-module structure of `↥S` to the
one coming from `DivisionRing.toRatAlgebra`, whereas `IntermediateField.finiteDimensional_sup`
provides the finiteness for the `IntermediateField.module'` structure; the two are propositionally
but not definitionally equal.  The way out is the same one used for `NumFieldIn.inf`: exhibit the
compositum as a *subfield of a known number field*, `↥S ≅ {x : ↥E // (x : Ω) ∈ S}` for an
intermediate field `E ⊇ S` which is a number field
(`NK.Reconstruct.numberField_of_le`, via `NumberField.of_subfield` and
`NumberField.of_ringEquiv`).

## Contents

* `NK.Reconstruct.numberField_of_le` — a subfield of a number field is a number field;
* **`NK.Reconstruct.NumFieldIn.supOf`** — the compositum, given an ambient number field `E`
  containing it, with `NumFieldIn.supOf_L`, `NumFieldIn.le_supOf_left`,
  `NumFieldIn.le_supOf_right` and `NumFieldIn.supOf_le`.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, Lemma 4f.4.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

attribute [local instance] NumFieldIn.finite NumFieldIn.numberField

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω]

open scoped Pointwise

/-- **A subfield of a number field is a number field.**  For intermediate fields `S ≤ E` of `Ω/ℚ`
with `E` a number field, `↥S` is a number field: `↥S` is ring-isomorphic to the subfield
`{x : ↥E // (x : Ω) ∈ S}` of `↥E`, to which `NumberField.of_subfield` applies. -/
theorem numberField_of_le {S E : IntermediateField ℚ Ω} (h : S ≤ E) [NumberField ↥E] :
    NumberField ↥S := by
  let E' : Subfield ↥E := Subfield.comap (algebraMap ↥E Ω) S.toSubfield
  haveI : NumberField ↥E' := NumberField.of_subfield (K := ↥E) E'
  refine NumberField.of_ringEquiv (K := ↥E') (L := ↥S) ?_
  refine
    { toFun := fun x => ⟨(x.1 : Ω), x.2⟩
      invFun := fun y => ⟨⟨(y.1 : Ω), h y.2⟩, y.2⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl
      map_add' := fun x y => Subtype.ext rfl }

/-- **The compositum of two finite number-field levels over `ℚ`** (Shimizu's `K₁K₂`), exhibited
inside a prescribed ambient number field `E` containing it. -/
noncomputable def NumFieldIn.supOf (K M : NumFieldIn ℚ Ω) (E : IntermediateField ℚ Ω)
    [NumberField ↥E] (h : K.L ⊔ M.L ≤ E) : NumFieldIn ℚ Ω where
  L := K.L ⊔ M.L
  finite := IntermediateField.finiteDimensional_sup K.L M.L
  numberField := numberField_of_le (E := E) h

@[simp] theorem NumFieldIn.supOf_L (K M : NumFieldIn ℚ Ω) (E : IntermediateField ℚ Ω)
    [NumberField ↥E] (h : K.L ⊔ M.L ≤ E) :
    (K.supOf M E h).L = K.L ⊔ M.L := rfl

theorem NumFieldIn.le_supOf_left (K M : NumFieldIn ℚ Ω) (E : IntermediateField ℚ Ω)
    [NumberField ↥E] (h : K.L ⊔ M.L ≤ E) :
    K.L ≤ (K.supOf M E h).L := _root_.le_sup_left

theorem NumFieldIn.le_supOf_right (K M : NumFieldIn ℚ Ω) (E : IntermediateField ℚ Ω)
    [NumberField ↥E] (h : K.L ⊔ M.L ≤ E) :
    M.L ≤ (K.supOf M E h).L := _root_.le_sup_right

theorem NumFieldIn.supOf_le (K M : NumFieldIn ℚ Ω) (E : IntermediateField ℚ Ω)
    [NumberField ↥E] (h : K.L ⊔ M.L ≤ E) :
    (K.supOf M E h).L ≤ E := h

end NK.Reconstruct
