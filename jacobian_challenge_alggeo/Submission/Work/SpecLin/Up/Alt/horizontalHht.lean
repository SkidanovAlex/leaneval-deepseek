/-
# Namespace mirror of `Work.SpecLin.Alt.horizontalHht`

This file is an exact copy of `Submission/Work/SpecLin/Alt/horizontalHht.lean` (module `Work.SpecLin.Alt.horizontalHht`), changed in exactly three ways:

* a `namespace Up` / `end Up` pair is inserted immediately inside the file's own namespace, so
  that every declaration `Work.SpecLin.<Area>.<x>` of the original appears here as
  `Work.SpecLin.<Area>.Up.<x>` (this avoids a name clash with the original, which cannot be
  removed: the original is part of the shared library);
* references to declarations *of the mirrored modules* are rewritten accordingly (full and
  area-relative forms), and imports of those modules point at their mirrors;
* an import of `Core/linEquiv_of_sections_of_chart.lean` (the module that *states* the
  affine-chart theorem) is replaced by an import of the upstream vocabulary module
  `Core/chartVocab.lean`, which declares the same chart algebra under the same names.

The point of the mirror is to break the import cycle
`vocabulary -> statement -> ... -> proof modules -> vocabulary`: the proof modules used to take
their vocabulary from the module that states the theorem, and this made a proof of that theorem
unreachable.  The mathematics is unchanged: the mirror is a verbatim copy of verified code.

The statements of the mirrored theorems mention only names that are *upstream* of the mirror, so
`Work.SpecLin.Core.Up.chartSpecialisation` (module
`Submission.Work.SpecLin.Up.Core.chartSpecialisation`) has literally the statement of
`Work.SpecLin.Core.linEquiv_of_sections_of_chart`, which is proved from it.
-/
/-
# The horizontal half of the crux hypothesis `IsUnitAt u q`

For the element `u := h'·(Π g_m)/(Π f_m)` of the proof of `Work.SpecLin.Alt.chartCoreDiv`, the
hypotheses of the crux `Alt.refinedHartogs` ask that `u` be a unit both at the fibre prime `P`
and at every height-one prime `q ≤ N` of the relative chart ring `B = Γ(C,W) ⊗_K R`.

The vertical case (`q ≤ P`) is `Alt.Up.isUnitAt_of_le_chartFibrePrime` (proved).  This file proves
the *horizontal* case (`q ∩ R = 0`, i.e. `q` a closed point of the generic fibre) from the
*order data*:

* the orders of the local equations at the point `Q` of `C_F` attached to `q`
  (`ord_Q(φ f_m) = [I_m ≤ q]`), which is the isolated input `(OD)` of
  `Alt/NOTES_chartCoreDiv.md` §3;
* the order of `h'` at `Q`, which is `Alt.Up.ordAt_of_div_eq_sum_ptDiv` (the hypothesis
  `div h' = Σ[s_m^F] − Σ[t_m^F]` read in the chart);
* the membership dictionary at `q` (`Alt.Up.exists_chartTensorPoint`),

the conclusion being that `u` and `u⁻¹` lie in `B_q`, in the `∃ a b` form of the dictionary.
-/
import Mathlib
import Submission.Work.SpecLin.Up.Alt.chartReading

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct Classical

namespace Work.SpecLin.Alt
namespace Up

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}

/-- **The horizontal half of `hht`.**  With the order data at the point `Q` of the generic fibre
attached to the height-one prime `q ≤ N`, the element `h'·(Π g_m)/(Π f_m)` and its inverse lie in
`B_q`, i.e. are given by fractions with denominator not in `q`. -/
theorem inLocalization_horizontal_of_ord {n : ℕ}
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (s t : Fin n → Work.SpecLin.CurvePt C R)
    (hs : ∀ m, Set.range ((s m).left).base ⊆ (W : Set C.left))
    (ht : ∀ m, Set.range ((t m).left).base ⊆ (W : Set C.left))
    (q : Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W))
    (Q : (C.baseChange (FractionRing R)).Place)
    (hQdict : ∀ x : (C.baseChange (FractionRing R)).functionField,
      (∃ a b : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W, b ∉ q ∧
          x * chartTensorMap (K := K) (C := C) R W hW b
            = chartTensorMap (K := K) (C := C) R W hW a)
        ↔ 0 ≤ (C.baseChange (FractionRing R)).ordAt x Q)
    (h' : (C.baseChange (FractionRing R)).functionField) (hh' : h' ≠ 0)
    (f g : Fin n → Work.SpecLin.Core.chartTensor (K := K) (C := C) R W)
    (hfne : ∀ m, chartTensorMap (K := K) (C := C) R W hW (f m) ≠ 0)
    (hgne : ∀ m, chartTensorMap (K := K) (C := C) R W hW (g m) ≠ 0)
    (hford : ∀ m, (C.baseChange (FractionRing R)).ordAt
        (chartTensorMap (K := K) (C := C) R W hW (f m)) Q
      = if (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
            (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m))) ≤ q
          then 1 else 0)
    (hgord : ∀ m, (C.baseChange (FractionRing R)).ordAt
        (chartTensorMap (K := K) (C := C) R W hW (g m)) Q
      = if (Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
            (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m))) ≤ q
          then 1 else 0)
    (hord : (C.baseChange (FractionRing R)).ordAt h' Q
      = ((Finset.univ.filter fun m : Fin n =>
            Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
              (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) ≤ q).card : ℤ)
        - ((Finset.univ.filter fun m : Fin n =>
            Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
              (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) ≤ q).card : ℤ)) :
    (∃ c d : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W, d ∉ q ∧
        (h' * (∏ m, chartTensorMap (K := K) (C := C) R W hW (g m))
            / (∏ m, chartTensorMap (K := K) (C := C) R W hW (f m)))
          * chartTensorMap (K := K) (C := C) R W hW d
        = chartTensorMap (K := K) (C := C) R W hW c)
    ∧ (∃ c d : Work.SpecLin.Core.chartTensor (K := K) (C := C) R W, d ∉ q ∧
        (h' * (∏ m, chartTensorMap (K := K) (C := C) R W hW (g m))
            / (∏ m, chartTensorMap (K := K) (C := C) R W hW (f m)))⁻¹
          * chartTensorMap (K := K) (C := C) R W hW d
        = chartTensorMap (K := K) (C := C) R W hW c) := by
  classical
  set F : (Fin n → (C.baseChange (FractionRing R)).functionField) :=
    fun m => chartTensorMap (K := K) (C := C) R W hW (f m) with hF
  set G : (Fin n → (C.baseChange (FractionRing R)).functionField) :=
    fun m => chartTensorMap (K := K) (C := C) R W hW (g m) with hG
  set I : Fin n → Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W) :=
    fun m => Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
      (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (s m) (hs m)) with hI
  set J : Fin n → Ideal (Work.SpecLin.Core.chartTensor (K := K) (C := C) R W) :=
    fun m => Work.SpecLin.Core.sectionPrime (K := K) (C := C) R W
      (Work.SpecLin.Core.Up.rgMap (K := K) (C := C) R W hW (t m) (ht m)) with hJ
  have hfne' : ∀ m, F m ≠ 0 := hfne
  have hgne' : ∀ m, G m ≠ 0 := hgne
  have hprod_f : (∏ m, F m) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun m _ => hfne' m)
  have hprod_g : (∏ m, G m) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun m _ => hgne' m)
  have hu0 : h' * (∏ m, G m) / (∏ m, F m) ≠ 0 :=
    div_ne_zero (mul_ne_zero hh' hprod_g) hprod_f
  -- the order of `u`
  have hsplit : ∀ (x y u : (C.baseChange (FractionRing R)).functionField)
      (hx : x ≠ 0) (hy : y ≠ 0) (hu : u ≠ 0),
      (C.baseChange (FractionRing R)).ordAt (x * y / u) Q
        = (C.baseChange (FractionRing R)).ordAt x Q
          + (C.baseChange (FractionRing R)).ordAt y Q
          - (C.baseChange (FractionRing R)).ordAt u Q := by
    intro x y u hx hy hu
    rw [show (C.baseChange (FractionRing R)).ordAt (x * y / u) Q
        = (C.baseChange (FractionRing R)).div (x * y / u) Q from
          (Work.CurveBasics.Curve.div_apply _ _ _).symm,
      Work.SpecLin.div_div _ (mul_ne_zero hx hy) hu, Finsupp.sub_apply,
      Work.CurveBasics.Curve.div_mul _ hx hy, Finsupp.add_apply,
      Work.CurveBasics.Curve.div_apply, Work.CurveBasics.Curve.div_apply,
      Work.CurveBasics.Curve.div_apply]
  have hsum : (C.baseChange (FractionRing R)).ordAt
        (h' * (∏ m, G m) / (∏ m, F m)) Q
      = (C.baseChange (FractionRing R)).ordAt h' Q
        + (∑ m, (C.baseChange (FractionRing R)).ordAt (G m) Q)
        - (∑ m, (C.baseChange (FractionRing R)).ordAt (F m) Q) := by
    rw [hsplit h' (∏ m, G m) (∏ m, F m) hh' hprod_g hprod_f,
      ordAt_prod _ _ _ (fun m _ => hgne' m) Q,
      ordAt_prod _ _ _ (fun m _ => hfne' m) Q]
  have hord0 : (C.baseChange (FractionRing R)).ordAt
      (h' * (∏ m, G m) / (∏ m, F m)) Q = 0 := by
    rw [hsum, hord,
      Finset.sum_congr rfl (fun m _ => hgord m),
      Finset.sum_congr rfl (fun m _ => hford m)]
    rw [Finset.card_filter, Finset.card_filter]
    push_cast
    ring
  constructor
  · exact (hQdict _).mpr (le_of_eq hord0.symm)
  · have hinv : (C.baseChange (FractionRing R)).ordAt
        (h' * (∏ m, G m) / (∏ m, F m))⁻¹ Q = 0 := by
      have hord0' : Scheme.ord (h' * (∏ m, G m) / (∏ m, F m)) Q.point = 0 := hord0
      rw [show (C.baseChange (FractionRing R)).ordAt
            (h' * (∏ m, G m) / (∏ m, F m))⁻¹ Q
          = Scheme.ord (h' * (∏ m, G m) / (∏ m, F m))⁻¹ Q.point from rfl,
        Work.CurveBasics.Order.ordAt_inv _ hu0 Q, hord0']
      ring
    exact (hQdict _).mpr (le_of_eq hinv.symm)

end Up
end Work.SpecLin.Alt

