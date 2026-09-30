import Mathlib
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Shared vocabulary for the degree-local integral universal coefficient theorem

This file fixes the coefficient group

* `Work.Pi6.UCT.QZ` — the circle group `ℚ/ℤ`, realised as `AddCircle (1 : ℚ) = ℚ ⧸ ℤ`,

and the elementary API about it that the two clauses of `Work.Pi6.UCT.uctZ` need:

* `Work.Pi6.UCT.natCard_smul` — in a finite additive group, `Nat.card`-multiples vanish;
* `Work.Pi6.UCT.restrict` — the restriction `Hom(Z, ℤ) → Hom(B, ℤ)` along a submodule
  inclusion `B ≤ Z` (the map whose cokernel is `Ext(Z ⧸ B, ℤ)`).

Everything here is Mathlib-only; the universal coefficient theorem itself is proved in the sibling
files (the degree-local Kronecker pairing, the finite local comparison, and the two algebraic
pieces).

NOTE for downstream files: the two `local instance` lines below make the module structure on a
submodule (resp. a quotient by a submodule) of a `ℤ`-module the one induced from the ambient
module.  They are needed so that `↥B →ₗ[ℤ] ℤ` is elaborated with the same module structure
everywhere; please repeat them in files that use this vocabulary.
-/

attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

namespace Work.Pi6.UCT

noncomputable section

/-- The circle group `ℚ/ℤ`. -/
abbrev QZ : Type := AddCircle (1 : ℚ)

/-- In a finite additive group, multiplication by the cardinality is zero. -/
lemma natCard_smul {G : Type*} [AddCommGroup G] [Finite G] (x : G) :
    (Nat.card G) • x = 0 := by
  haveI := Fintype.ofFinite G
  rw [Nat.card_eq_fintype_card]
  simp

/-- In a finite additive group, multiplication by the cardinality is zero (as a `zsmul`). -/
lemma natCard_zsmul {G : Type*} [AddCommGroup G] [Finite G] (x : G) :
    (Nat.card G : ℤ) • x = 0 := by
  rw [Nat.cast_smul_eq_nsmul]
  exact natCard_smul x

/-- The restriction of a `ℤ`-linear functional along the inclusion `B ≤ Z`. -/
def restrict {Z : Type*} [AddCommGroup Z] [Module ℤ Z] (B : Submodule ℤ Z) :
    (Z →ₗ[ℤ] ℤ) →ₗ[ℤ] (B →ₗ[ℤ] ℤ) where
  toFun f := f.comp B.subtype
  map_add' f g := by ext x; rfl
  map_smul' a f := by ext x; rfl

lemma restrict_apply {Z : Type*} [AddCommGroup Z] [Module ℤ Z] (B : Submodule ℤ Z)
    (f : Z →ₗ[ℤ] ℤ) (x : B) : restrict B f x = f x := rfl

end

end Work.Pi6.UCT
