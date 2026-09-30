/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The base change of the divisor of a rational function

For a smooth, proper, geometrically irreducible curve `C` over a field `k` and a field
extension `F/k`, the pullback of divisors `C.divMap F : Div C →+ Div C_F` (whose coefficient at
a place `Q'` of `C_F` is `e(Q'/Q) · D(Q)`, where `Q` is the place of `C` below `Q'`) sends the
principal divisor of `h ∈ K(C)^*` to the principal divisor of the image of `h` in `K(C_F)`:

`C.divMap F (C.div h) = (C.baseChange F).div ((C.functionFieldMap F).hom h)`.

This is the statement that the induced map of function fields `φ : K(C) → K(C_F)` is compatible
with orders of vanishing:

* at a place `Q'` of `C_F` lying over a place `Q` of `C`, the order of vanishing at `Q'` of
  `φ h` is the ramification index `e(Q'/Q) = ord_{Q'}(φ ϖ_Q)` times the order of `h` at `Q`;
  this is proved by writing `h = ϖ_Q ^ n · g` with `g` (and `g⁻¹`) regular at `Q` and using that
  `φ` carries the local ring `O_{C,Q}` into the local ring `O_{C_F,Q'}`;
* at a place `Q'` of `C_F` lying over the *generic* point of `C` (i.e. a closed point of the
  generic fibre), the element `φ h` is regular at `Q'` for *both* `h` and `h⁻¹`, hence a unit,
  and its order of vanishing is `0`.
-/
import Mathlib
import Submission.Work.CurveBasics.BaseChangeDivisor
import Submission.Work.CurveBasics.BaseChange.divMap_isEffective
import Submission.Work.CurveBasics.BaseChange.mem_range_germ_iff
import Submission.Work.CurveBasics.Order.ord_lem
import Submission.Work.CurveBasics.Order.div_inv
import Submission.Work.CurveBasics.Place.ord_uniformizer

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

universe v

namespace Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type v} [Field k]

/-- The order of vanishing of a `ℤ`-power of a rational function at a place. -/
theorem ordAt_zpow (C : Curve k) {f : C.functionField} (hf : f ≠ 0) (m : ℤ) (Q : C.Place) :
    C.ordAt (f ^ m) Q = m * C.ordAt f Q := by
  have hz : Order.coheight Q.point = 1 := Q.eq_coheight_one
  haveI : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Q.instIsDiscreteValuationRing
  rw [Curve.ordAt, Scheme.ord_eq_iff hz (zpow_ne_zero m hf)]
  show Ring.ordFrac (C.left.presheaf.stalk Q.point) (f ^ m)
      = Multiplicative.ofAdd (m * Scheme.ord f Q.point)
  have h2 : Ring.ordFrac (C.left.presheaf.stalk Q.point) f
      = WithZero.exp (Scheme.ord f Q.point) := by
    rw [WithZero.exp_eq_coe_ofAdd]
    exact (Scheme.ord_eq_iff hz hf).mp rfl
  rw [map_zpow₀, h2, ← WithZero.exp_zsmul m (Scheme.ord f Q.point), WithZero.exp_eq_coe_ofAdd]
  simp

end

end Curve

namespace BaseChange

/-- The canonical map from the local ring of an irreducible scheme at its generic point to the
function field is the identity. -/
theorem algebraMap_stalk_genericPoint_self {X : Scheme.{v}} [IrreducibleSpace X]
    (a : X.functionField) :
    (stalkFunctionFieldAlgebra X (genericPoint X)).algebraMap a = a := by
  rw [show (stalkFunctionFieldAlgebra X (genericPoint X)).algebraMap
      = (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom from rfl]
  rw [show ((genericPoint_spec X).specializes trivial
      : Specializes (genericPoint X) (genericPoint X))
      = specializes_refl (genericPoint X) from Subsingleton.elim _ _]
  have hst := congrArg
    (fun f : X.presheaf.stalk (genericPoint X) ⟶ X.presheaf.stalk (genericPoint X) => f.hom a)
    (TopCat.Presheaf.stalkSpecializes_refl X.presheaf (genericPoint X))
  simpa using hst

open Work.CurveBasics in
/-- A rational function is regular at the generic point of the curve: the local ring there is
the whole function field. -/
theorem mem_range_algebraMap_genericPoint {k : Type v} [Field k] {C : Curve k} {z : C.left}
    (h : z = genericPoint C.left) (a : C.functionField) :
    a ∈ (algebraMap (C.left.presheaf.stalk z) C.functionField).range := by
  subst h
  exact ⟨a, algebraMap_stalk_genericPoint_self a⟩

open Work.CurveBasics in
/-- **Regularity transfer.**  If a rational function `g` on `C` is regular at the image in `C`
of a place `Q'` of `C_F`, then its image in `K(C_F)` is regular at `Q'`. -/
theorem ordAt_nonneg_of_mem_range {k : Type v} [Field k] {C : Curve k} (F : Type v) [Field F]
    [Algebra k F] (Q' : (C.baseChange F).Place) {g : C.functionField}
    (hg : g ∈ (algebraMap (C.left.presheaf.stalk ((C.baseChangeFst F) Q'.point))
      C.functionField).range) :
    0 ≤ (C.baseChange F).ordAt ((C.functionFieldMap F).hom g) Q' := by
  obtain ⟨a, rfl⟩ := hg
  rw [functionFieldMap_algebraMap_stalk C F Q'.point a]
  exact (mem_range_algebraMap_stalk_iff (C.baseChange F) Q' _).mp
    ⟨(C.baseChangeFst F).stalkMap Q'.point a, rfl⟩

open Work.CurveBasics in
/-- **The ramification formula.**  At a place `Q'` of `C_F` lying over a place `Q` of `C`, the
order of vanishing of the image of `h ∈ K(C)^*` is the ramification index times the order of
vanishing of `h` at `Q`. -/
theorem ordAt_functionFieldMap_eq {k : Type v} [Field k] {C : Curve k} (F : Type v) [Field F]
    [Algebra k F] (Q' : (C.baseChange F).Place)
    (hc : IsClosed ({(C.baseChangeFst F) Q'.point} : Set C.left)) {f : C.functionField}
    (hf : f ≠ 0) :
    (C.baseChange F).ordAt ((C.functionFieldMap F).hom f) Q' =
      C.ramIdx F Q' * C.ordAt f (C.under F Q' hc) := by
  let π : C.functionField := (C.under F Q' hc).uniformizer
  let n : ℤ := C.ordAt f (C.under F Q' hc)
  let g : C.functionField := f * π ^ (-n)
  have hπord : C.ordAt π (C.under F Q' hc) = 1 := Place.ord_uniformizer _
  have hπne : π ≠ 0 := by
    intro hzero
    have h1 : Scheme.ord (0 : C.functionField) (C.under F Q' hc).point = 1 := by
      rw [← hzero]
      exact hπord
    rw [congrFun Scheme.ord_zero (C.under F Q' hc).point] at h1
    exact zero_ne_one h1
  have hng : C.ordAt (π ^ n) (C.under F Q' hc) = n := by
    rw [Curve.ordAt_zpow C hπne n (C.under F Q' hc), hπord, mul_one]
  have hgne : g ≠ 0 := mul_ne_zero hf (zpow_ne_zero (-n) hπne)
  have hgord : C.ordAt g (C.under F Q' hc) = 0 := by
    have h := Curve.ordAt_mul C hf (zpow_ne_zero (-n) hπne) (C.under F Q' hc)
    rw [Curve.ordAt_zpow C hπne (-n) (C.under F Q' hc), hπord, mul_one] at h
    rw [show C.ordAt f (C.under F Q' hc) = n from rfl] at h
    rw [show g = f * π ^ (-n) from rfl, h]
    ring
  -- `g` and `g⁻¹` are both regular at `Q`, so `φ g` is a unit at `Q'`
  have hgmem : g ∈ (algebraMap (C.left.presheaf.stalk (C.under F Q' hc).point)
      C.functionField).range :=
    (mem_range_algebraMap_stalk_iff C (C.under F Q' hc) g).mpr (le_of_eq hgord.symm)
  have hgmem' : g⁻¹ ∈ (algebraMap (C.left.presheaf.stalk (C.under F Q' hc).point)
      C.functionField).range := by
    refine (mem_range_algebraMap_stalk_iff C (C.under F Q' hc) g⁻¹).mpr ?_
    have h1 : Scheme.ord g⁻¹ (C.under F Q' hc).point
        = -Scheme.ord g (C.under F Q' hc).point :=
      Order.ordAt_inv C hgne (C.under F Q' hc)
    have h2 : Scheme.ord g (C.under F Q' hc).point = 0 := hgord
    show 0 ≤ Scheme.ord g⁻¹ (C.under F Q' hc).point
    rw [h1, h2, neg_zero]
  have hφg_ne : (C.functionFieldMap F).hom g ≠ 0 := fun h =>
    hgne (Curve.functionFieldMap_injective C F (by rw [h, map_zero]))
  have hφg_ord : (C.baseChange F).ordAt ((C.functionFieldMap F).hom g) Q' = 0 := by
    have h1 : 0 ≤ (C.baseChange F).ordAt ((C.functionFieldMap F).hom g) Q' :=
      ordAt_nonneg_of_mem_range (C := C) F Q' hgmem
    have h2 : 0 ≤ (C.baseChange F).ordAt ((C.functionFieldMap F).hom g⁻¹) Q' :=
      ordAt_nonneg_of_mem_range (C := C) F Q' hgmem'
    have h3 : (C.baseChange F).ordAt ((C.functionFieldMap F).hom g⁻¹) Q'
        = -(C.baseChange F).ordAt ((C.functionFieldMap F).hom g) Q' := by
      rw [map_inv₀]
      exact Order.ordAt_inv (C.baseChange F) hφg_ne Q'
    linarith
  -- the ramification index is the order of vanishing of the image of a uniformizer
  have hramIdx : C.ramIdx F Q' = (C.baseChange F).ordAt ((C.functionFieldMap F).hom π) Q' := by
    show C.ramIdx F Q' = Scheme.ord
      ((C.functionFieldMap F).hom ((C.under F Q' hc).uniformizer)) Q'.point
    rw [Curve.ramIdx, dif_pos hc]
  have hφπ_ne : (C.functionFieldMap F).hom π ≠ 0 := fun h =>
    hπne (Curve.functionFieldMap_injective C F (by rw [h, map_zero]))
  have hf_decomp : f = π ^ n * g := by
    rw [show g = f * π ^ (-n) from rfl]
    rw [mul_comm (π ^ n) (f * π ^ (-n)), mul_assoc, ← zpow_add₀ hπne]
    simp
  have hφf : (C.functionFieldMap F).hom f
      = ((C.functionFieldMap F).hom π) ^ n * (C.functionFieldMap F).hom g := by
    rw [hf_decomp, map_mul, map_zpow₀]
  calc (C.baseChange F).ordAt ((C.functionFieldMap F).hom f) Q'
      = (C.baseChange F).ordAt
          (((C.functionFieldMap F).hom π) ^ n * (C.functionFieldMap F).hom g) Q' := by
        rw [hφf]
    _ = (C.baseChange F).ordAt (((C.functionFieldMap F).hom π) ^ n) Q'
          + (C.baseChange F).ordAt ((C.functionFieldMap F).hom g) Q' :=
        Curve.ordAt_mul (C.baseChange F) (zpow_ne_zero n hφπ_ne) hφg_ne Q'
    _ = n * (C.baseChange F).ordAt ((C.functionFieldMap F).hom π) Q' + 0 := by
        rw [Curve.ordAt_zpow (C.baseChange F) hφπ_ne n Q', hφg_ord]
    _ = C.ramIdx F Q' * C.ordAt f (C.under F Q' hc) := by
        rw [hramIdx, show C.ordAt f (C.under F Q' hc) = n from rfl]
        ring

universe u in
open Work.CurveBasics in
theorem divMap_div {k : Type u} [Field k] {C : Curve k} (F : Type u) [Field F] [Algebra k F]
    {f : C.functionField} (hf : f ≠ 0) :
    C.divMap F (C.div f) = (C.baseChange F).div ((C.functionFieldMap F).hom f) := by
  ext Q'
  rw [Curve.divMap_apply, Curve.div_apply]
  by_cases hc : IsClosed ({(C.baseChangeFst F) Q'.point} : Set C.left)
  · rw [Curve.divMapCoeff, dif_pos hc, Curve.div_apply]
    show C.ordAt f (C.under F Q' hc) * C.ramIdx F Q'
      = (C.baseChange F).ordAt ((C.functionFieldMap F).hom f) Q'
    rw [ordAt_functionFieldMap_eq (C := C) F Q' hc hf]
    ring
  · rw [Curve.divMapCoeff, dif_neg hc]
    show 0 = (C.baseChange F).ordAt ((C.functionFieldMap F).hom f) Q'
    have hgen : (C.baseChangeFst F) Q'.point = genericPoint C.left := by
      rcases C.eq_genericPoint_or_isClosed ((C.baseChangeFst F) Q'.point) with h | h
      · exact h
      · exact absurd h hc
    have hmem : f ∈ (algebraMap (C.left.presheaf.stalk ((C.baseChangeFst F) Q'.point))
        C.functionField).range :=
      mem_range_algebraMap_genericPoint hgen f
    have hmem' : f⁻¹ ∈ (algebraMap (C.left.presheaf.stalk ((C.baseChangeFst F) Q'.point))
        C.functionField).range :=
      mem_range_algebraMap_genericPoint hgen f⁻¹
    have hφf_ne : (C.functionFieldMap F).hom f ≠ 0 := fun h =>
      hf (Curve.functionFieldMap_injective C F (by rw [h, map_zero]))
    have h1 : 0 ≤ (C.baseChange F).ordAt ((C.functionFieldMap F).hom f) Q' :=
      ordAt_nonneg_of_mem_range (C := C) F Q' hmem
    have h2 : 0 ≤ (C.baseChange F).ordAt ((C.functionFieldMap F).hom f⁻¹) Q' :=
      ordAt_nonneg_of_mem_range (C := C) F Q' hmem'
    have h3 : (C.baseChange F).ordAt ((C.functionFieldMap F).hom f⁻¹) Q'
        = -(C.baseChange F).ordAt ((C.functionFieldMap F).hom f) Q' := by
      rw [map_inv₀]
      exact Order.ordAt_inv (C.baseChange F) hφf_ne Q'
    have hzero : (C.baseChange F).ordAt ((C.functionFieldMap F).hom f) Q' = 0 := by linarith
    rw [hzero]

end BaseChange

end Work.CurveBasics
