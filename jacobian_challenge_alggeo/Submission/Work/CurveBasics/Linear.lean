/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Riemann-Roch space `L(D)`

For a divisor `D` on a curve `C`, the Riemann-Roch space is
`L(D) = {h : K(C) | div h + D ≥ 0} ∪ {0}`, a `k`-subspace of the function field.
-/
import Submission.Work.CurveBasics.Order
import Submission.Work.CurveBasics.Place.isDiscreteValuationRing
import Submission.Work.CurveBasics.Order.div_algebraMap_eq_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The Riemann-Roch space `L(D) = {h | div h + D ≥ 0} ∪ {0}`. -/
def L (C : Curve k) (D : Div C) : Submodule k C.functionField where
  carrier := {h | h = 0 ∨ (C.div h + D).IsEffective}
  zero_mem' := Or.inl rfl
  add_mem' := by
    haveI (Q : Place C) : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
      Place.isDiscreteValuationRing Q
    intro h g hh hg
    rcases hh with h0 | hh
    · subst h0; simpa using hg
    rcases hg with g0 | hg
    · subst g0; exact Or.inr (by simpa using hh)
    by_cases hsum : h + g = 0
    · exact Or.inl hsum
    refine Or.inr fun Q => ?_
    have h1 : -D Q ≤ Scheme.ord h Q.point := (C.isEffective_div_add_iff).mp hh Q
    have h2 : -D Q ≤ Scheme.ord g Q.point := (C.isEffective_div_add_iff).mp hg Q
    have h3 := Scheme.ord_add (x := Q.point) (f := h) (g := g) hsum
    have h4 : -D Q ≤ min (Scheme.ord h Q.point) (Scheme.ord g Q.point) := le_min h1 h2
    simp only [Finsupp.add_apply, div_apply]
    linarith
  smul_mem' := by
    intro c h hh
    by_cases h0 : h = 0
    · subst h0; simp
    rcases hh with hh0 | hh
    · exact absurd hh0 h0
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    refine Or.inr ?_
    have hne : algebraMap k C.functionField c ≠ 0 := by
      simpa using ((algebraMap k C.functionField).injective.ne_iff).mpr hc
    have hd : C.div (c • h) = C.div h := by
      rw [Algebra.smul_def, C.div_mul hne h0,
        Work.CurveBasics.Order.div_algebraMap_eq_zero C c, zero_add]
    rwa [hd]

theorem mem_L_iff (C : Curve k) {D : Div C} {h : C.functionField} :
    h ∈ C.L D ↔ h = 0 ∨ (C.div h + D).IsEffective := Iff.rfl

/-- The dimension `l(D) = dim_k L(D)` of the Riemann-Roch space. -/
noncomputable def l (C : Curve k) (D : Div C) : ℕ := Module.finrank k (C.L D)

theorem zero_mem_L (C : Curve k) (D : Div C) : (0 : C.functionField) ∈ C.L D :=
  Submodule.zero_mem _

theorem L_mono (C : Curve k) {D E : Div C} (h : Div.le D E) : C.L D ≤ C.L E := by
  intro x hx
  rw [mem_L_iff] at hx ⊢
  rcases hx with h0 | hx
  · exact Or.inl h0
  refine Or.inr fun Q => ?_
  have h1 : -D Q ≤ Scheme.ord x Q.point := (C.isEffective_div_add_iff).mp hx Q
  have h2 : D Q ≤ E Q := Div.le_iff.mp h Q
  simp only [Finsupp.add_apply, div_apply]
  linarith

/-- Constants are in every Riemann-Roch space of an effective divisor. -/
theorem algebraMap_mem_L (C : Curve k) {D : Div C} (hD : D.IsEffective) (c : k) :
    algebraMap k C.functionField c ∈ C.L D := by
  rw [mem_L_iff]
  by_cases hc : c = 0
  · subst hc; exact Or.inl (map_zero _)
  · refine Or.inr fun Q => ?_
    rw [Work.CurveBasics.Order.div_algebraMap_eq_zero C c, zero_add]
    exact hD Q

end

end Curve

end Work.CurveBasics
