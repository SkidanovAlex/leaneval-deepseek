/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The divisor of the ideal of a place

Let `C` be a curve over a field `F`, let `V ⊆ C` be a nonempty affine open with `Γ(C,V)` a
Dedekind domain, and let `z` be a place of `C` lying in `V`.  Writing `m_z = placeIdeal C V z hz`
for the maximal ideal of `Γ(C,V)` cut out by `z`, this file computes the divisor attached to the
ideal `m_z`:

`divisorOfIdeal C V hV (placeIdeal C V z hz) = [z]`.

Here `divisorOfIdeal C V hV J = Σ_w (placeOrder C V J w hw) [w]` is the divisor of an ideal
(`Submission/Work/SymQuot/DivOf/DivisorOfIdeal.lean`) and `[z] = Curve.Div.place z`.

The proof is the pointwise computation of the multiplicity of a place ideal: passing through the
bijection `heightOneEquiv` between the places of `V` and the height-one primes of `Γ(C,V)`
(`Submission/Work/SymQuot/DivOf/heightOneSpectrum_equiv_place.lean`), the multiplicity of `m_z`
at a place `w` is the `Associates.count` of one height-one prime in another, which is `1` when
`w = z` (`Associates.count_self`) and `0` otherwise (`Associates.count_eq_zero_of_ne`).
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.DivisorOfIdeal
import Submission.Work.SymQuot.DivOf.placeIdeal_isMaximal
import Submission.Work.SymQuot.DivOf.heightOneSpectrum_equiv_place

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.DivOf

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open Work.CurveBasics

/-- **The `Associates.count` of one height-one prime in another**: the multiplicity of the prime
`v` in the factorization of the prime `w` is `1` if `v = w` and `0` otherwise.  This assembles
`Associates.count_self` and `Associates.count_eq_zero_of_ne` into a single `if`. -/
theorem count_mk_asIdeal_eq_ite {R : Type u} [CommRing R] [IsDedekindDomain R]
    (v w : IsDedekindDomain.HeightOneSpectrum R) :
    (Associates.mk w.asIdeal).count (Associates.mk v.asIdeal).factors = if w = v then 1 else 0 := by
  by_cases h : w = v
  · rw [h, ite_eq_left rfl]
    exact Associates.count_self v.associates_irreducible
  · rw [ite_eq_right h]
    refine Associates.count_eq_zero_of_ne w.associates_irreducible v.associates_irreducible ?_
    intro hcon
    rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq,
      ← IsDedekindDomain.HeightOneSpectrum.ext_iff] at hcon
    exact h hcon

/-- **The order of the place ideal of `z` at a place `w` of the affine open**: it is `1` at `z`
and `0` away from `z`.  Both the ideal and the evaluation point are matched through the bijection
`heightOneEquiv` between the places of `V` and the height-one primes of `Γ(C,V)`, which makes the
statement independent of the chosen membership proofs. -/
theorem placeOrder_placeIdeal_ite {F : Type u} [Field F] {C : Curve F}
    (V : C.left.Opens) [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (z : C.Place) (hz : z.point ∈ V) (w : C.Place) (hw : w.point ∈ V) :
    placeOrder C V (placeIdeal C V z hz) w hw = if w = z then 1 else 0 := by
  let v := heightOneEquiv C V hV ⟨z, hz⟩
  let u := heightOneEquiv C V hV ⟨w, hw⟩
  have hv : placeIdeal C V z hz = v.asIdeal :=
    (heightOneEquiv_apply C V hV ⟨z, hz⟩).symm
  have hu : placeIdeal C V w hw = u.asIdeal :=
    (heightOneEquiv_apply C V hV ⟨w, hw⟩).symm
  rw [placeOrder, hu, hv, count_mk_asIdeal_eq_ite]
  have huv_iff : u = v ↔ w = z := by
    show heightOneEquiv C V hV ⟨w, hw⟩ = heightOneEquiv C V hV ⟨z, hz⟩ ↔ w = z
    rw [(heightOneEquiv C V hV).injective.eq_iff, Subtype.ext_iff]
  by_cases h : w = z
  · rw [ite_eq_left h, ite_eq_left (huv_iff.mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun huv => h (huv_iff.mp huv))]

theorem divisorOfIdeal_placeIdeal {F : Type u} [Field F] {C : Curve F}
    (V : C.left.Opens) [Nonempty V] (hV : IsAffineOpen V) [IsDedekindDomain Γ(C.left, V)]
    (z : C.Place) (hz : z.point ∈ V) :
    divisorOfIdeal C V hV (placeIdeal C V z hz) = Curve.Div.place z := by
  ext w
  rw [divisorOfIdeal_apply, Curve.Div.place, Finsupp.single_apply]
  by_cases hw : w.point ∈ V
  · rw [dite_eq_left hw, placeOrder_placeIdeal_ite (C := C) V hV z hz w hw]
    by_cases h : w = z
    · rw [ite_eq_left h, ite_eq_left h.symm]
      norm_num
    · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm)]
      norm_num
  · rw [dite_eq_right hw]
    rw [ite_eq_right (fun h : z = w => hw (h ▸ hz))]

end Work.SymQuot.DivOf
