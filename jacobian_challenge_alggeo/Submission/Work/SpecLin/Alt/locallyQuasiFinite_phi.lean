import Mathlib
import Submission.Work.SpecLin.Alt.CurveAffine
import Submission.Work.CurveBasics.All
import Submission.Work.SpecLin.Chart.Regular
import Submission.Work.SpecLin.Chart.RegularOpensMap
import Submission.Work.SpecLin.Chart.RegularOpensAffineAux
import Submission.Work.SpecLin.Chart.locallyQuasiFinite_regularOpensMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SpecLin.Alt

open Work.CurveBasics


/-! ## Small ring-theoretic helpers -/

theorem mvPolynomial_eval₂Hom_comp {R S T : Type*} [CommSemiring R] [CommSemiring S]
    [CommSemiring T] {σ : Type*} (f : R →+* S) (g : σ → S) (k : S →+* T) :
    k.comp (MvPolynomial.eval₂Hom f g) = MvPolynomial.eval₂Hom (k.comp f) (k ∘ g) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [MvPolynomial.eval₂Hom_comp_C]
  · simp

theorem polynomial_eval₂RingHom_comp_uniqueAlgEquiv {R : Type*} [CommSemiring R]
    {A : Type*} [CommSemiring A] {σ : Type*} [Unique σ] (f : R →+* A) (y : A) :
    (Polynomial.eval₂RingHom f y).comp
        (↑(MvPolynomial.uniqueAlgEquiv R σ) : MvPolynomial σ R →+* Polynomial R) =
      MvPolynomial.eval₂Hom f (fun _ : σ => y) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [MvPolynomial.eval₂Hom_comp_C, Polynomial.eval₂RingHom_comp_C]
  · simp

/-! ## The coordinate target `Γ(𝔸¹_K) ≅ K[X]` -/

noncomputable def a1Coeff (K : Type u) [Field K] :
    MvPolynomial PUnit.{u+1} K →+* Γ(A1 K, ⊤) :=
  MvPolynomial.eval₂Hom (Chart.structureRingHom (K := K) (A1 K))
    (AffineSpace.coord (Spec (CommRingCat.of K)))

theorem ΓSpecIso_inv_comp_specIso_hom_appTop (K : Type u) [Field K] :
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial PUnit.{u+1} K))).inv ≫
        (AffineSpace.SpecIso PUnit.{u+1} (CommRingCat.of K)).hom.appTop =
      CommRingCat.ofHom (a1Coeff K) := by
  rw [AffineSpace.SpecIso_hom_appTop]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

theorem structureRingHom_comp_phi {K : Type u} [Field K] (C : Curve K) (x : C.functionField)
    (s : Γ(C.left, Chart.regularOpens C x)) :
    ((phi (Chart.regularOpens C x) s).appTop).hom.comp (Chart.structureRingHom (K := K) (A1 K)) =
      Chart.structureRingHom (K := K) (Chart.regularOpens C x).toScheme := by
  have key : (A1Over K).appTop ≫ (phi (Chart.regularOpens C x) s).appTop =
      (structHom C (Chart.regularOpens C x)).appTop := by
    rw [← Scheme.Hom.comp_appTop, phi_over]
  have h1 : ((phi (Chart.regularOpens C x) s).appTop).hom.comp (A1Over K).appTop.hom =
      (structHom C (Chart.regularOpens C x)).appTop.hom := congrArg CommRingCat.Hom.hom key
  rw [show Chart.structureRingHom (K := K) (A1 K) =
        (A1Over K).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom from rfl,
    show Chart.structureRingHom (K := K) (Chart.regularOpens C x).toScheme =
        (structHom C (Chart.regularOpens C x)).appTop.hom.comp
          (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom from rfl,
    ← RingHom.comp_assoc, h1]

/-! ## The `MvPolynomial`-targeted coordinate morphism -/

noncomputable def mvCoeff {K : Type u} [Field K] (C : Curve K) (x : C.functionField)
    (s : Γ(C.left, Chart.regularOpens C x)) :
    MvPolynomial PUnit.{u+1} K →+* Γ((Chart.regularOpens C x).toScheme, ⊤) :=
  MvPolynomial.eval₂Hom (Chart.structureRingHom (K := K) (Chart.regularOpens C x).toScheme)
    (fun _ => (phi (Chart.regularOpens C x) s).appTop
      (AffineSpace.coord (Spec (CommRingCat.of K)) PUnit.unit))

noncomputable def gMv {K : Type u} [Field K] (C : Curve K) (x : C.functionField)
    (s : Γ(C.left, Chart.regularOpens C x)) :
    (Chart.regularOpens C x).toScheme ⟶
      Spec (CommRingCat.of (MvPolynomial PUnit.{u+1} K)) :=
  (Chart.regularOpens C x).toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (mvCoeff C x s))

/-- The first factor of the change of coordinates `𝔸¹_K ⟶ Spec K[X̄]`. -/
noncomputable def a1ToMvPoly (K : Type u) [Field K] :
    A1 K ⟶ Spec (CommRingCat.of (MvPolynomial PUnit.{u+1} K)) :=
  (AffineSpace.SpecIso PUnit.{u+1} (CommRingCat.of K)).hom

theorem ΓSpecIso_inv_comp_gMv_appTop {K : Type u} [Field K] (C : Curve K) (x : C.functionField)
    (s : Γ(C.left, Chart.regularOpens C x)) :
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial PUnit.{u+1} K))).inv ≫ (gMv C x s).appTop =
      CommRingCat.ofHom (mvCoeff C x s) := by
  rw [gMv, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality]
  simp

/-! ## The `MvPolynomial`-to-`Polynomial` change of coordinates -/

noncomputable def mvPolyIso (K : Type u) [Field K] :
    Spec (CommRingCat.of (MvPolynomial PUnit.{u+1} K)) ≅
      Spec (CommRingCat.of (Polynomial K)) :=
  Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso
    (((MvPolynomial.uniqueAlgEquiv K PUnit.{u+1}).toRingEquiv.symm :
      Polynomial K ≃+* MvPolynomial PUnit.{u+1} K))).op

theorem mvPolyIso_inv_eq (K : Type u) [Field K] :
    (mvPolyIso K).inv = Spec.map (CommRingCat.ofHom
      (↑(MvPolynomial.uniqueAlgEquiv K PUnit.{u+1}) :
        MvPolynomial PUnit.{u+1} K →+* Polynomial K)) := by
  simp only [mvPolyIso, Functor.mapIso_inv, Scheme.Spec.mapIso_inv]
  rfl

theorem mvPolyIso_inv_appTop (K : Type u) [Field K] :
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial PUnit.{u+1} K))).inv ≫
        (mvPolyIso K).inv.appTop =
      CommRingCat.ofHom
          (↑(MvPolynomial.uniqueAlgEquiv K PUnit.{u+1}) :
            MvPolynomial PUnit.{u+1} K →+* Polynomial K) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv := by
  rw [mvPolyIso_inv_eq]
  exact (Scheme.ΓSpecIso_inv_naturality _).symm

/-! ## Reduction of `appTop` equalities for affine `Spec K[X]`-targets -/

theorem eq_of_ΓSpecIso_inv_comp_appTop_eq {K : Type u} [Field K] {X : Scheme.{u}}
    {f g : X ⟶ Spec (CommRingCat.of (MvPolynomial PUnit.{u+1} K))}
    (h : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial PUnit.{u+1} K))).inv ≫ f.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial PUnit.{u+1} K))).inv ≫ g.appTop) :
    f = g := by
  apply AlgebraicGeometry.ext_of_isAffine
  have h2 := congrArg (fun t => (Scheme.ΓSpecIso
    (CommRingCat.of (MvPolynomial PUnit.{u+1} K))).hom ≫ t) h
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h2

/-! ## The two transfers -/

theorem a1Coeff_comp_phi_appTop_ringHom {K : Type u} [Field K] (C : Curve K)
    (x : C.functionField) (s : Γ(C.left, Chart.regularOpens C x)) :
    ((phi (Chart.regularOpens C x) s).appTop).hom.comp (a1Coeff K) = mvCoeff C x s := by
  rw [a1Coeff]
  unfold mvCoeff
  rw [mvPolynomial_eval₂Hom_comp]
  have h2 := structureRingHom_comp_phi C x s
  have h3 : ((phi (Chart.regularOpens C x) s).appTop).hom ∘
      (AffineSpace.coord (Spec (CommRingCat.of K))) =
      (fun _ => (phi (Chart.regularOpens C x) s).appTop
        (AffineSpace.coord (Spec (CommRingCat.of K)) PUnit.unit)) := by
    funext i
    exact congrArg _ (Subsingleton.elim i PUnit.unit)
  rw [h2, h3]

theorem a1Coeff_comp_phi_appTop {K : Type u} [Field K] (C : Curve K) (x : C.functionField)
    (s : Γ(C.left, Chart.regularOpens C x)) :
    CommRingCat.ofHom (a1Coeff K) ≫ (phi (Chart.regularOpens C x) s).appTop =
      CommRingCat.ofHom (mvCoeff C x s) := by
  rw [← CommRingCat.ofHom_hom ((phi (Chart.regularOpens C x) s).appTop), ← CommRingCat.ofHom_comp]
  congr 1
  exact a1Coeff_comp_phi_appTop_ringHom C x s

theorem phi_comp_specIso_eq_gMv {K : Type u} [Field K] (C : Curve K) (x : C.functionField)
    (s : Γ(C.left, Chart.regularOpens C x)) :
    phi (Chart.regularOpens C x) s ≫ a1ToMvPoly K = gMv C x s := by
  unfold a1ToMvPoly
  apply eq_of_ΓSpecIso_inv_comp_appTop_eq (K := K)
  rw [Scheme.Hom.comp_appTop, ΓSpecIso_inv_comp_gMv_appTop]
  rw [show (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial PUnit.{u+1} K))).inv ≫
      ((AffineSpace.SpecIso PUnit.{u+1} (CommRingCat.of K)).hom.appTop ≫
        (phi (Chart.regularOpens C x) s).appTop) =
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial PUnit.{u+1} K))).inv ≫
        (AffineSpace.SpecIso PUnit.{u+1} (CommRingCat.of K)).hom.appTop) ≫
        (phi (Chart.regularOpens C x) s).appTop from (Category.assoc _ _ _).symm]
  rw [ΓSpecIso_inv_comp_specIso_hom_appTop, a1Coeff_comp_phi_appTop]

theorem gMv_eq_regularOpensMap_comp {K : Type u} [Field K] (C : Curve K) (x : C.functionField)
    (s : Γ(C.left, Chart.regularOpens C x)) [Nonempty (Chart.regularOpens C x)]
    (hs : (C.germToFunctionField (Chart.regularOpens C x)).hom s = x) :
    gMv C x s = Chart.regularOpensMap C x ≫ (mvPolyIso K).inv := by
  apply eq_of_ΓSpecIso_inv_comp_appTop_eq (K := K)
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, mvPolyIso_inv_appTop, Category.assoc,
    Chart.ΓSpecIso_inv_comp_regularOpensMap_appTop, ΓSpecIso_inv_comp_gMv_appTop]
  have hco : (phi (Chart.regularOpens C x) s).appTop
      (AffineSpace.coord (Spec (CommRingCat.of K)) PUnit.unit) =
      Chart.regularOpensTopSection C x := by
    rw [phi_appTop_coord, show s = Chart.regularOpensSection C x from
      Scheme.germToFunctionField_injective C.left (Chart.regularOpens C x)
        (by rw [hs, Chart.germToFunctionField_regularOpensSection])]
    rfl
  rw [← CommRingCat.ofHom_comp]
  congr 1
  rw [show Chart.regularOpensCoeff C x =
      Polynomial.eval₂RingHom (Chart.structureRingHom (K := K) (Chart.regularOpens C x).toScheme)
        (Chart.regularOpensTopSection C x) from rfl]
  rw [polynomial_eval₂RingHom_comp_uniqueAlgEquiv]
  unfold mvCoeff
  congr 1
  funext i
  exact hco

/-! ## The composite `𝔸¹_K ⟶ Spec K[X]` -/

noncomputable def a1ToPoly (K : Type u) [Field K] :
    A1 K ⟶ Spec (CommRingCat.of (Polynomial K)) :=
  a1ToMvPoly K ≫ (mvPolyIso K).hom

/-- **`phi` has finite fibres** (it is locally quasi-finite).

`C` a smooth proper geometrically irreducible curve over a field `K`, `x ∈ K(C)` transcendental,
`s` a section over `W = Work.SpecLin.Alt.regularOpens C x` whose germ is `x`, and
`Work.SpecLin.Alt.phi W s : W ⟶ 𝔸¹_K` the morphism over `Spec K` with coordinate function `s`
(see `Submission/Work/SpecLin/Alt/CurveAffine.lean`, which also proves that `phi W s` is of
finite type and quasi-compact, and gives `phi_appTop_coord`).  Then `phi W s` is locally
quasi-finite.

Route.  `locallyQuasiFinite_iff_finite_preimage_singleton` reduces to: every fibre
`(phi W s) ⁻¹' {y}` is finite.  Fix `y` and `w` with `phi W s w = y`.  The naturality of the
evaluation map in the residue field (`Scheme.Hom.Γevaluation_naturality_apply`) applied to the
coordinate `co := AffineSpace.coord (Spec (CommRingCat.of K)) PUnit.unit`, together with
`Work.SpecLin.Alt.phi_appTop_coord` and injectivity of the residue-field map of a morphism of
fields, gives for every global section `a` of `A1 K`:
`(A1 K).Γevaluation ((phi W s) w) a = 0 ↔ (W.toScheme).Γevaluation w ((phi W s).appTop a) = 0`.

* If `(A1 K).Γevaluation y` has nonzero kernel, say `0 ≠ a` with `Γevaluation y a = 0`, then for
  `w ∈ (phi W s) ⁻¹' {y}` one has `Γevaluation w ((phi W s).appTop a) = 0`.  The point `w` is not
  the generic point of `C` (evaluation at the generic point of an integral scheme is injective,
  while `(phi W s).appTop` is injective because `x` is transcendental), hence `w` is a closed
  point (`Curve.eq_genericPoint_or_isClosed`) and the fibre is contained in
  `{Q : C.Place | 0 < C.ordAt (aeval x a) Q}`, which is finite (`Curve.finite_support_ordAt`).
  (`Scheme.evaluation`, `Scheme.germ_residue` and `IsLocalRing.residue_eq_zero_iff` translate
  `Γevaluation w b = 0`, for a closed `w`, into `0 < ord_w b`.)
* If `(A1 K).Γevaluation y` is injective, then no closed point of `C` is in the fibre: for a
  closed `w` the residue field `κ(w)` is finite over `K` (`Curve.Place.degree_eq_finrank`,
  `Curve.Place.residueDegree_pos`), so the composite `Γ(A1 K, ⊤) → κ(w)` is not injective,
  giving `0 ≠ a` with `Γevaluation ((phi W s) w) a = 0` — contradicting injectivity at
  `y = (phi W s) w`.  So the fibre consists of non-closed points, i.e. it is contained in
  `{genericPoint C.left}`.

It may help to transport along `AffineSpace.isoOfIsAffine` to identify the points of `A1 K` with
primes of `MvPolynomial PUnit K`, and to note that for an affine `X = Spec R` the kernel of
`X.Γevaluation x` is the prime of `x`. -/
theorem locallyQuasiFinite_phi {K : Type*} [Field K] {C : Work.CurveBasics.Curve K}
    {x : C.functionField} (hx : Transcendental K x)
    (s : C.left.presheaf.obj (Opposite.op (Work.SpecLin.Alt.regularOpens C x)))
    [Nonempty (Work.SpecLin.Alt.regularOpens C x)]
    (hs : (C.germToFunctionField (Work.SpecLin.Alt.regularOpens C x)).hom s = x) :
    AlgebraicGeometry.LocallyQuasiFinite
      (Work.SpecLin.Alt.phi (Work.SpecLin.Alt.regularOpens C x) s) := by
  have hmain : LocallyQuasiFinite (Chart.regularOpensMap C x) :=
    Chart.locallyQuasiFinite_regularOpensMap C x hx
  have hB : gMv C x s = Chart.regularOpensMap C x ≫ (mvPolyIso K).inv :=
    gMv_eq_regularOpensMap_comp C x s hs
  have hA : phi (Chart.regularOpens C x) s ≫ a1ToMvPoly K = gMv C x s :=
    phi_comp_specIso_eq_gMv C x s
  have hcomb : phi (Chart.regularOpens C x) s ≫ a1ToPoly K = Chart.regularOpensMap C x := by
    rw [a1ToPoly, ← Category.assoc, hA, hB, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  haveI : LocallyQuasiFinite (phi (Chart.regularOpens C x) s ≫ a1ToPoly K) := by
    rw [hcomb]
    exact hmain
  exact LocallyQuasiFinite.of_comp (phi (Chart.regularOpens C x) s) (a1ToPoly K)

end Work.SpecLin.Alt
