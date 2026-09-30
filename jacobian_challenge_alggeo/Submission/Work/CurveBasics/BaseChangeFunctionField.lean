/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The map of function fields induced by a base change

For a curve `C` over `k` and a field extension `F/k`, the projection `C_F ⟶ C` induces an
injective field homomorphism `K(C) ⟶ K(C_F)`.  This is the map along which divisors,
order of vanishing and Riemann-Roch spaces are compared.
-/
import Submission.Work.CurveBasics.BaseChange
import Submission.Work.CurveBasics.Order

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

/-- The projection `C_F ⟶ C` maps the generic point of `C_F` to the generic point of `C`. -/
theorem baseChangeFst_genericPoint (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    baseChangeFst C F (genericPoint (baseChangeLeft C F)) = genericPoint C.left := by
  have hcont : Continuous (baseChangeFst C F) := (baseChangeFst C F).continuous
  have hsurj : Function.Surjective (baseChangeFst C F) := (baseChangeFst C F).surjective
  -- the generic point of `C_F` maps to a generic point of `C`
  have hcl : closure ({(baseChangeFst C F) (genericPoint (baseChangeLeft C F))} :
      Set C.left) = Set.univ := by
    have h1 : closure ({genericPoint (baseChangeLeft C F)} :
        Set (baseChangeLeft C F)) = Set.univ := genericPoint_spec _
    rw [← Set.image_singleton]
    have h2 : (baseChangeFst C F) '' closure ({genericPoint (baseChangeLeft C F)} :
        Set (baseChangeLeft C F)) ⊆
        closure ((baseChangeFst C F) '' {genericPoint (baseChangeLeft C F)}) :=
      image_closure_subset_closure_image hcont
    rw [h1, Set.image_univ, Set.range_eq_univ.mpr hsurj] at h2
    exact Set.eq_univ_of_univ_subset h2
  exact T0Space.t0 (inseparable_iff_specializes_and.mpr
    ⟨by rw [specializes_iff_mem_closure, hcl]; trivial,
     by rw [specializes_iff_mem_closure, genericPoint_spec]; trivial⟩)

/-- The field homomorphism `K(C) ⟶ K(C_F)` induced by the projection `C_F ⟶ C`. -/
def functionFieldMap (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    C.functionField ⟶ (C.baseChange F).functionField :=
  C.left.presheaf.stalkSpecializes
      (by rw [baseChangeFst_genericPoint C F]; exact specializes_rfl) ≫
    (baseChangeFst C F).stalkMap (genericPoint (baseChangeLeft C F))

theorem functionFieldMap_injective (C : Curve k) (F : Type u) [Field F] [Algebra k F] :
    Function.Injective (functionFieldMap C F).hom := by
  intro a b hab
  by_contra hne
  have h1 : a - b ≠ 0 := sub_ne_zero.mpr hne
  have h2 : (functionFieldMap C F).hom (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  have h3 : (1 : (C.baseChange F).functionField) = 0 := by
    have hm := map_mul (functionFieldMap C F).hom (a - b) (a - b)⁻¹
    rw [mul_inv_cancel₀ h1, map_one, h2, zero_mul] at hm
    exact hm
  exact one_ne_zero h3

/-- The preimage in `C_F` of an open subset of `C`. -/
abbrev bcOpens (C : Curve k) (F : Type u) [Field F] [Algebra k F] (W : C.left.Opens) :
    (C.baseChange F).left.Opens := (baseChangeFst C F) ⁻¹ᵁ W

instance bcOpens_nonempty (C : Curve k) (F : Type u) [Field F] [Algebra k F]
    (W : C.left.Opens) [Nonempty W] : Nonempty (C.bcOpens F W) := by
  obtain ⟨w, hw⟩ := ‹Nonempty W›
  obtain ⟨x, hx⟩ := (baseChangeFst C F).surjective w
  exact ⟨⟨x, by show (baseChangeFst C F) x ∈ W; rw [hx]; exact hw⟩⟩

/-- `f` is regular at every place of the open set `W`. -/
def RegularOn (C : Curve k) (W : C.left.Opens) (f : C.functionField) : Prop :=
  ∀ Q : C.Place, Q.point ∈ W → 0 ≤ C.ordAt f Q

/-- The pole divisor of a rational function. -/
noncomputable def poleDivisor (C : Curve k) (x : C.functionField) : C.Div :=
  Finsupp.ofSupportFinite (fun Q => max 0 (-(C.ordAt x Q)))
    ((C.finite_support_ordAt x).subset (fun Q hQ => by
      simp only [Function.mem_support] at hQ ⊢
      intro h
      exact hQ (by rw [h]; simp)))

end

end Curve

end Work.CurveBasics
