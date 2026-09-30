import Mathlib
import Submission.Work.CurveBasics.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SymQuot.DivOf

open Work.CurveBasics

/-!
# Injectivity of the base-change map on divisors

For a base-change square `S : Curve.BCSquare C C'` (i.e. `C' = C ×_k Spec F` for a field
extension `F/k`, presented as an abstract cartesian square), the pullback of divisors
`S.divMap : C.Div →+ C'.Div` is injective.

The mathematical content is that above every place `Q` of `C` there is a place `Q'` of `C'`
with positive ramification index, so that the coefficient of `S.divMap D` at `Q'` is
`e(Q'/Q) · D Q` and detects the vanishing of `D Q`.  The two ingredients are
`exists_place_above` (a place above a place, since the projection is surjective and points of a
curve that are not the generic point are closed) and `one_le_ramIdx` (the ramification index is
at least one, since the image of a uniformizer at `Q` lies in the maximal ideal at `Q'`).

The two ingredients are stated `private` here; public versions are being proved separately
under `Submission/Work/SymQuot/DivOf/one_le_ramIdx.lean` and
`Submission/Work/SymQuot/DivOf/exists_place_above.lean`.
-/

section

variable {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
variable {C : Curve k} {C' : Curve F}

/-- **The field map of a base-change square is induced by the map on local rings.**

For a point `y` of `C'`, the map `S.fieldMap : K(C) ⟶ K(C')` sends the image of an element of
the local ring `𝒪_{C, S.π y}` (inside `K(C)`) to the image of its push-forward under
`S.π.stalkMap y` (inside `K(C')`).  This is `fieldMap_stalkMap_aux` of
`Submission/Work/CurveBasics/Curve/BCSquare/ordAt_fieldMap.lean` (where it is private). -/
private theorem fieldMap_stalkMap (S : Curve.BCSquare C C') (y : C'.left)
    (a : C.left.presheaf.stalk (S.π y)) :
    S.fieldMap.hom (algebraMap (C.left.presheaf.stalk (S.π y)) (↑C.functionField) a) =
      algebraMap (C'.left.presheaf.stalk y) (↑C'.functionField) ((S.π.stalkMap y).hom a) := by
  let Φ : (↑C.functionField) →+* (↑C'.functionField) := S.fieldMap.hom
  change Φ (algebraMap (C.left.presheaf.stalk (S.π y)) (↑C.functionField) a) =
      algebraMap (C'.left.presheaf.stalk y) (↑C'.functionField) ((S.π.stalkMap y).hom a)
  obtain ⟨U, hxU, hUaff, r, hr⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis C.left.isBasis_affineOpens C.left.presheaf _ a
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  haveI hbc : Nonempty (S.preimage U) := S.instNonemptyPreimage U
  have hA : algebraMap (C.left.presheaf.stalk (S.π y)) (↑C.functionField)
      (C.left.presheaf.germ U (S.π y) hxU r) = C.germToFunctionField U r :=
    Scheme.algebraMap_germ_eq_germToFunctionField (X := C.left) hxU r
  have hΦ : Φ (C.germToFunctionField U r) =
      Scheme.germToFunctionField (X := C'.left) (U := S.preimage U) (h := hbc)
        (S.π.app U r) := by
    rw [show Φ = S.fieldMap.hom from rfl, Work.CurveBasics.Curve.BCSquare.fieldMap]
    erw [ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
      Scheme.Hom.germ_stalkMap_apply]
  have hψ : ((S.π.stalkMap y).hom)
      (C.left.presheaf.germ U (S.π y) hxU r) =
      C'.left.presheaf.germ (S.preimage U) y hxU (S.π.app U r) :=
    Scheme.Hom.germ_stalkMap_apply S.π U y hxU r
  have hβ : algebraMap (C'.left.presheaf.stalk y) (↑C'.functionField)
      (C'.left.presheaf.germ (S.preimage U) y hxU (S.π.app U r)) =
      Scheme.germToFunctionField (X := C'.left) (U := S.preimage U) (h := hbc)
        (S.π.app U r) :=
    @Scheme.algebraMap_germ_eq_germToFunctionField C'.left _ (S.preimage U) hbc y hxU
      (S.π.app U r)
  rw [← hr, hA, hψ]
  exact hΦ.trans hβ.symm

/-- In the value group `ℤᵐ⁰`, an element is `< 1` if and only if it is `≤ exp (-1)`. -/
private lemma lt_one_iff_le_exp_neg_one {y : WithZero (Multiplicative ℤ)} :
    y < 1 ↔ y ≤ WithZero.exp (-1) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · conv_lhs => rw [← WithZero.exp_log hy]
    conv_rhs => rw [← WithZero.exp_log hy]
    rw [← WithZero.exp_zero (M := ℤ), WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

/-- **The ramification index of a place of `C'` over a place of `C` is at least one.**

`S.ramIdx Q'` is `C'.ordAt (S.fieldMap.hom u) Q'` where `u` is the uniformizer at the place
`Q = S.under Q' h` below `Q'`.  Writing `u` as the image of a generator `g` of the maximal ideal
of `O_{C,Q}`, the field map sends it to the image in `K(C')` of `(S.π.stalkMap Q'.point) g`,
which lies in the maximal ideal of `O_{C',Q'}` because the stalk map is a local homomorphism.
For an element of the maximal ideal the associated valuation is `< 1`, and `Scheme.ord` is minus
its logarithm, so the order of vanishing is at least `1`. -/
theorem one_le_ramIdx (S : Curve.BCSquare C C') (Q' : C'.Place)
    (h : IsClosed ({S.π Q'.point} : Set C.left)) : 1 ≤ S.ramIdx Q' := by
  haveI hDVR : IsDiscreteValuationRing (C.left.presheaf.stalk (S.π Q'.point)) :=
    (S.under Q' h).instIsDiscreteValuationRing
  haveI hDVR' : IsDiscreteValuationRing (C'.left.presheaf.stalk Q'.point) :=
    Q'.instIsDiscreteValuationRing
  -- a generator of the maximal ideal of the local ring at `Q`, and its image in the local ring
  -- at `Q'`
  set g : C.left.presheaf.stalk (S.π Q'.point) :=
    Submodule.IsPrincipal.generator
      (IsLocalRing.maximalIdeal (C.left.presheaf.stalk (S.π Q'.point))) with hgdef
  set c : C'.left.presheaf.stalk Q'.point := (S.π.stalkMap Q'.point).hom g with hcdef
  have hg : g ∈ IsLocalRing.maximalIdeal (C.left.presheaf.stalk (S.π Q'.point)) :=
    Submodule.IsPrincipal.generator_mem _
  have hc : c ∈ IsLocalRing.maximalIdeal (C'.left.presheaf.stalk Q'.point) :=
    map_nonunit _ g hg
  -- the image of the uniformizer at `Q` is the image of `c`
  have hb : S.fieldMap.hom (S.under Q' h).uniformizer =
      algebraMap (C'.left.presheaf.stalk Q'.point) (↑C'.functionField) c := by
    have h1 : (S.under Q' h).uniformizer =
        algebraMap (C.left.presheaf.stalk (S.π Q'.point)) (↑C.functionField) g := rfl
    rw [h1, hcdef]
    exact fieldMap_stalkMap S Q'.point g
  -- the uniformizer, and hence its image, is nonzero
  have hu0 : (S.under Q' h).uniformizer ≠ 0 := by
    intro h0
    have h1 : C.ordAt (S.under Q' h).uniformizer (S.under Q' h) = 1 := Place.ord_uniformizer _
    have h2 : C.ordAt (S.under Q' h).uniformizer (S.under Q' h) = 0 := by
      rw [h0]
      exact congrFun AlgebraicGeometry.Scheme.ord_zero (S.under Q' h).point
    rw [h2] at h1
    exact zero_ne_one h1
  have hbc0 : algebraMap (C'.left.presheaf.stalk Q'.point) (↑C'.functionField) c ≠ 0 := by
    intro h0
    have h1 : S.fieldMap.hom (S.under Q' h).uniformizer = 0 := by rw [hb, h0]
    exact hu0 (S.fieldMap.hom.injective (by rw [h1, map_zero]))
  -- the associated valuation of the image is `< 1`
  have hval : Q'.valuation
      (algebraMap (C'.left.presheaf.stalk Q'.point) (↑C'.functionField) c) < 1 := by
    change (IsDiscreteValuationRing.maximalIdeal (C'.left.presheaf.stalk Q'.point)).valuation
      (↑C'.functionField) (algebraMap (C'.left.presheaf.stalk Q'.point) (↑C'.functionField) c) < 1
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem
      (IsDiscreteValuationRing.maximalIdeal (C'.left.presheaf.stalk Q'.point)) c).mpr hc
  -- rewrite `ramIdx` as minus the logarithm of that valuation
  rw [Curve.BCSquare.ramIdx, dite_eq_left h, hb]
  have hord : C'.ordAt (algebraMap (C'.left.presheaf.stalk Q'.point) (↑C'.functionField) c) Q'
      = -(Q'.valuation
        (algebraMap (C'.left.presheaf.stalk Q'.point) (↑C'.functionField) c)).log :=
    Curve.Place.ord_eq_neg_log_valuation C' Q' _
  rw [hord]
  have hlog : (Q'.valuation
      (algebraMap (C'.left.presheaf.stalk Q'.point) (↑C'.functionField) c)).log ≤ -1 := by
    rw [WithZero.log_le_iff_le_exp ((Valuation.ne_zero_iff Q'.valuation).mpr hbc0)]
    exact lt_one_iff_le_exp_neg_one.mp hval
  linarith

/-- **Every place of `C` has a place of `C'` above it.**  The projection `S.π` is surjective, so
take a preimage `z` of `Q.point`; since `S.π` maps the generic point to the generic point and
`Q.point` is not the generic point, `z` is not the generic point of `C'`, hence has coheight one
and is closed. -/
private theorem exists_place_above (S : Curve.BCSquare C C') (Q : C.Place) :
    ∃ Q' : C'.Place, S.π Q'.point = Q.point := by
  obtain ⟨z, hz⟩ := S.π.surjective Q.point
  have hzgen : z ≠ genericPoint C'.left := by
    intro h0
    have h1 : S.π z = genericPoint C.left := by rw [h0, S.π_genericPoint]
    have h2 : Q.point = genericPoint C.left := by rw [← hz, h1]
    have h3 : Order.coheight Q.point = 1 := Q.eq_coheight_one
    rw [h2, Curve.coheight_genericPoint C] at h3
    exact one_ne_zero h3.symm
  have hco : Order.coheight z = 1 := by
    have hle : Order.coheight z ≤ 1 := C'.coheight_le_one z
    rcases (Order.le_one_iff (α := ℕ∞)).mp hle with h | h
    · exact absurd (C'.eq_genericPoint_of_coheight_eq_zero h) hzgen
    · exact h
  exact ⟨⟨z, Point.isClosed_of_coheight_eq_one C' hco⟩, hz⟩

end

theorem divMap_injective {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Work.CurveBasics.Curve k} {C' : Work.CurveBasics.Curve F}
    (S : Work.CurveBasics.Curve.BCSquare C C') :
    Function.Injective S.divMap := by
  intro D E hDE
  have key : ∀ D₀ : C.Div, S.divMap D₀ = 0 → D₀ = 0 := by
    intro D₀ hD
    ext Q
    rw [Finsupp.zero_apply]
    by_contra hQ
    -- a place of `C'` above `Q`, at which the coefficient detects `D₀ Q`
    obtain ⟨Q', hQ'⟩ := exists_place_above S Q
    have hcl : IsClosed ({S.π Q'.point} : Set C.left) := by
      rw [hQ']; exact Q.isClosed
    have hcoeff : S.divMap D₀ Q' = D₀ Q * S.ramIdx Q' := by
      rw [Curve.BCSquare.divMap_apply, Curve.BCSquare.divMapCoeff, dite_eq_left hcl,
        show S.under Q' hcl = Q from Subtype.ext hQ']
    have hzero : S.divMap D₀ Q' = 0 := by rw [hD, Finsupp.zero_apply]
    have hram : S.ramIdx Q' ≠ 0 := by
      have h1 := one_le_ramIdx S Q' hcl
      omega
    rw [hcoeff] at hzero
    exact hQ (mul_eq_zero.mp hzero |>.resolve_right hram)
  exact sub_eq_zero.mp (key (D - E) (by rw [map_sub, hDE, sub_self]))

end Work.SymQuot.DivOf
