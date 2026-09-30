/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Divisors on a curve

The group of divisors on a curve is the free abelian group on its closed points.  This file
defines it, together with the degree
`deg D = ∑_Q n_Q [κ(Q) : k]`,
which is the push-forward of `D` to `Spec k`.

Everything here is stated over an arbitrary field `k`: degrees are computed with the full
residue field degrees `[κ(Q) : k]`, which for an imperfect `k` may be inseparable.
-/
import Submission.Work.CurveBasics.Place

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The group of divisors on a curve: finite formal integral combinations of closed points. -/
abbrev Div (C : Curve k) : Type u := (Place C) →₀ ℤ

namespace Div

variable {C : Curve k}

/-- A divisor is effective if all its coefficients are nonnegative. -/
def IsEffective (D : Div C) : Prop := ∀ Q, 0 ≤ D Q

/-- The pointwise order on divisors. -/
def le (D E : Div C) : Prop := (E - D).IsEffective

/-- The divisor with a single nonzero coefficient, at one place. -/
def single (Q : Place C) (n : ℤ) : Div C := Finsupp.single Q n

/-- The divisor `[Q]` of a single place. -/
def place (Q : Place C) : Div C := Finsupp.single Q 1

@[simp]
theorem isEffective_zero : IsEffective (0 : Div C) := fun Q => by simp

theorem IsEffective.add {D E : Div C} (hD : D.IsEffective) (hE : E.IsEffective) :
    (D + E).IsEffective := fun Q => by
  have := hD Q; have := hE Q; simp only [Finsupp.add_apply]; linarith

theorem isEffective_iff {D : Div C} : D.IsEffective ↔ ∀ Q, 0 ≤ D Q := Iff.rfl

theorem le_iff {D E : Div C} : le D E ↔ ∀ Q, D Q ≤ E Q := by
  simp [le, IsEffective, Finsupp.sub_apply]

theorem le_refl (D : Div C) : le D D := fun Q => by simp

theorem isEffective_iff_le_zero {D : Div C} : D.IsEffective ↔ le 0 D := by
  simp [le]

end Div

/-- The degree of a divisor as an additive homomorphism `Div C →+ ℤ`. -/
noncomputable def degHom (C : Curve k) : Div C →+ ℤ where
  toFun D := D.sum fun Q n => n * (C.hom.residueDegree Q.point : ℤ)
  map_zero' := Finsupp.sum_zero_index
  map_add' D E := by
    show (D + E).sum (fun Q n => n * (C.hom.residueDegree Q.point : ℤ)) =
      D.sum (fun Q n => n * (C.hom.residueDegree Q.point : ℤ)) +
        E.sum (fun Q n => n * (C.hom.residueDegree Q.point : ℤ))
    rw [Finsupp.sum_add_index' (fun a => by ring) (fun a b₁ b₂ => by ring)]

/-- The degree of a divisor: `deg D = ∑_Q n_Q [κ(Q) : k]`. -/
noncomputable def deg (C : Curve k) (D : Div C) : ℤ := C.degHom D

@[simp]
theorem deg_zero (C : Curve k) : C.deg 0 = 0 := map_zero _

theorem deg_add (C : Curve k) (D E : Div C) : C.deg (D + E) = C.deg D + C.deg E :=
  map_add _ _ _

theorem deg_neg (C : Curve k) (D : Div C) : C.deg (-D) = -C.deg D := map_neg _ _

theorem deg_sub (C : Curve k) (D E : Div C) : C.deg (D - E) = C.deg D - C.deg E :=
  map_sub _ _ _

theorem deg_nsmul (C : Curve k) (n : ℕ) (D : Div C) : C.deg (n • D) = n • C.deg D :=
  map_nsmul _ _ _

theorem deg_zsmul (C : Curve k) (n : ℤ) (D : Div C) : C.deg (n • D) = n • C.deg D :=
  map_zsmul _ _ _

theorem deg_sum (C : Curve k) {ι : Type*} (s : Finset ι) (D : ι → Div C) :
    C.deg (∑ i ∈ s, D i) = ∑ i ∈ s, C.deg (D i) :=
  map_sum _ _ _

theorem deg_single (C : Curve k) (Q : Place C) (n : ℤ) :
    C.deg (Div.single Q n) = n * (C.hom.residueDegree Q.point : ℤ) := by
  show (Div.single Q n).sum (fun Q n => n * (C.hom.residueDegree Q.point : ℤ)) =
    n * (C.hom.residueDegree Q.point : ℤ)
  rw [Div.single, Finsupp.sum_single_index (by ring)]

/-- The degree of a place, viewed as a divisor. -/
theorem deg_place (C : Curve k) (Q : Place C) :
    C.deg (Div.place Q) = (C.hom.residueDegree Q.point : ℤ) := by
  change C.deg (Div.single Q 1) = (C.hom.residueDegree Q.point : ℤ)
  rw [deg_single, one_mul]

end

end Curve

end Work.CurveBasics
