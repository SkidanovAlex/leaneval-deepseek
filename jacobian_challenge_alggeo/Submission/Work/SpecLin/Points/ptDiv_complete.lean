import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.SpecLin.Points

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

/-! ## Auxiliary lemmas

The geometric content of `ptDiv_complete` is that a closed point of `C_F` whose residue field
is `F` (i.e. a place of residue degree one) is the image of a section of `C_F ⟶ Spec F`, hence
comes from an `F`-point of `C`.  The lemmas below establish:

* `fromSpecResidueField_comp_hom`: the map `Spec κ(z) ⟶ Spec k` of a point of a curve over `k`
  is induced by the canonical `k`-algebra structure of the residue field;
* `exists_retraction`: a place of residue degree one has residue field the base field;
* `effective_deg_one_eq_single`: an effective divisor of degree one is a single place of degree
  one;
* `exists_ptPlace_eq`: a place of `C_F` of residue degree one over `F` is the `ptPlace` of an
  `F`-point of `C`. -/

/-- The structure map `Spec κ(z) ⟶ Spec k` of the residue field of a point `z` of a curve over
`k` is induced by the canonical `k`-algebra structure on `κ(z)`. -/
private theorem fromSpecResidueField_comp_hom {k : Type u} [Field k]
    {C₀ : Work.CurveBasics.Curve k} (z : C₀.left) :
    C₀.left.fromSpecResidueField z ≫ C₀.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (C₀.left.residueField z))) := by
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField C₀.hom z]
  rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (CommRingCat.of k) (C₀.hom z)]
  rw [← Spec.map_comp]
  rw [← Spec.map_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  rw [CommRingCat.hom_comp]
  rw [CommRingCat.hom_comp]
  have hB := congrArg CommRingCat.Hom.hom
    (Scheme.Spec.algebraMap_residueFieldIso_inv (CommRingCat.of k) (C₀.hom z))
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at hB
  rw [hB]
  rfl

/-- The residue field of a place of degree one of a curve over `k` is `k` itself: the structure
map `k ⟶ κ(Q)` admits a retraction. -/
private theorem exists_retraction {k : Type u} [Field k] {C₀ : Work.CurveBasics.Curve k}
    (Q : C₀.Place) (hQ : C₀.hom.residueDegree Q.point = 1) :
    ∃ ψ : C₀.left.residueField Q.point →+* k,
      ψ.comp (algebraMap k (C₀.left.residueField Q.point)) = RingHom.id k := by
  have hfin : Module.finrank k (C₀.left.residueField Q.point) = 1 := by
    rw [← Work.CurveBasics.Place.degree_eq_finrank (C := C₀) Q]
    exact hQ
  have hfd : FiniteDimensional k (C₀.left.residueField Q.point) :=
    FiniteDimensional.of_finrank_pos (by rw [hfin]; norm_num)
  have hinj : Function.Injective (algebraMap k (C₀.left.residueField Q.point)) := by
    intro a b hab
    by_contra hne
    have hsub : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h0 : algebraMap k (C₀.left.residueField Q.point) (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    have h1 : (1 : C₀.left.residueField Q.point) = 0 := by
      calc (1 : C₀.left.residueField Q.point)
          = algebraMap k _ ((a - b)⁻¹ * (a - b)) := by rw [inv_mul_cancel₀ hsub, map_one]
        _ = algebraMap k _ ((a - b)⁻¹) * algebraMap k _ (a - b) := by rw [map_mul]
        _ = 0 := by rw [h0, mul_zero]
    exact one_ne_zero h1
  have hsurj : Function.Surjective (algebraMap k (C₀.left.residueField Q.point)) := by
    have hrange : (Algebra.linearMap k (C₀.left.residueField Q.point)).range = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 : Module.finrank k ↥(Algebra.linearMap k (C₀.left.residueField Q.point)).range
          = Module.finrank k k :=
        ((LinearEquiv.ofInjective (Algebra.linearMap k (C₀.left.residueField Q.point))
          hinj).finrank_eq).symm
      rw [h1, Module.finrank_self, hfin]
    intro x
    obtain ⟨y, hy⟩ := LinearMap.range_eq_top.mp hrange x
    exact ⟨y, by rw [← hy, Algebra.linearMap_apply]⟩
  let e : k ≃+* C₀.left.residueField Q.point :=
    RingEquiv.ofBijective (algebraMap k (C₀.left.residueField Q.point)) ⟨hinj, hsurj⟩
  refine ⟨↑e.symm, ?_⟩
  have hcoe : (↑e : k →+* C₀.left.residueField Q.point) = algebraMap k _ :=
    RingHom.ext fun x => rfl
  have hsymm := RingEquiv.symm_comp e
  rwa [hcoe] at hsymm

/-- An effective divisor of degree one on a curve over a field is the divisor of a single place
of degree one. -/
private theorem effective_deg_one_eq_single {k : Type u} [Field k]
    {C₀ : Work.CurveBasics.Curve k} {D : C₀.Div} (hD : D.IsEffective) (hdeg : C₀.deg D = 1) :
    ∃ Q : C₀.Place, D = Finsupp.single Q 1 ∧ C₀.hom.residueDegree Q.point = 1 := by
  have hne : D ≠ 0 := by
    intro h0
    rw [h0, Work.CurveBasics.Curve.deg_zero] at hdeg
    exact one_ne_zero hdeg.symm
  obtain ⟨Q₀, hQ₀mem⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hQ₀ne : D Q₀ ≠ 0 := Finsupp.mem_support_iff.mp hQ₀mem
  have hQ₀pos : 1 ≤ D Q₀ := by have := hD Q₀; omega
  have hEeff : (D - Work.CurveBasics.Curve.Div.single Q₀ (1 : ℤ)).IsEffective := by
    intro Q
    by_cases h : Q = Q₀
    · subst h
      rw [Work.CurveBasics.Curve.Div.single, Finsupp.sub_apply, Finsupp.single_eq_same]
      omega
    · rw [Work.CurveBasics.Curve.Div.single, Finsupp.sub_apply,
        Finsupp.single_eq_of_ne h, sub_zero]
      exact hD Q
  have hEdegnonneg : 0 ≤ C₀.deg (D - Work.CurveBasics.Curve.Div.single Q₀ (1 : ℤ)) :=
    Work.CurveBasics.Divisor.deg_nonneg hEeff
  have hEdegle : C₀.deg (D - Work.CurveBasics.Curve.Div.single Q₀ (1 : ℤ)) ≤ 0 := by
    rw [Work.CurveBasics.Curve.deg_sub, hdeg, Work.CurveBasics.Curve.deg_single]
    have hd : 1 ≤ (C₀.hom.residueDegree Q₀.point : ℤ) := by
      exact_mod_cast Work.CurveBasics.Place.residueDegree_pos Q₀
    linarith
  have hEdeg : C₀.deg (D - Work.CurveBasics.Curve.Div.single Q₀ (1 : ℤ)) = 0 :=
    le_antisymm hEdegle hEdegnonneg
  have hE : D - Work.CurveBasics.Curve.Div.single Q₀ (1 : ℤ) = 0 :=
    (Work.CurveBasics.Divisor.deg_eq_zero_iff hEeff).mp hEdeg
  have hDsingle : D = Work.CurveBasics.Curve.Div.single Q₀ (1 : ℤ) := sub_eq_zero.mp hE
  refine ⟨Q₀, hDsingle, ?_⟩
  have h1 : (C₀.hom.residueDegree Q₀.point : ℤ) = 1 := by
    have h2 : C₀.deg D = (C₀.hom.residueDegree Q₀.point : ℤ) := by
      rw [hDsingle, Work.CurveBasics.Curve.deg_single, one_mul]
    rw [hdeg] at h2
    exact h2.symm
  exact_mod_cast h1

/-- A place of `C_F` of residue degree one over `F` is the `ptPlace` of an `F`-point of `C`:
its residue field is `F`, so it is the image of a section of `C_F ⟶ Spec F`, which composed
with the projection `C_F ⟶ C` is an `F`-point of `C`. -/
private theorem exists_ptPlace_eq {k : Type u} [Field k] {C₀ : Work.CurveBasics.Curve k}
    {L : Type u} [Field L] [Algebra k L] (Q : (C₀.baseChange L).Place)
    (hQ : (C₀.baseChange L).hom.residueDegree Q.point = 1) :
    ∃ p : Work.SpecLin.CurveFPt C₀ L, Work.SpecLin.ptPlace p = Q := by
  obtain ⟨ψ, hψ⟩ := exists_retraction (C₀ := C₀.baseChange L) Q hQ
  have hkey : (C₀.baseChange L).left.fromSpecResidueField Q.point ≫ (C₀.baseChange L).hom =
      Spec.map (CommRingCat.ofHom
        (algebraMap L ((C₀.baseChange L).left.residueField Q.point))) :=
    fromSpecResidueField_comp_hom (C₀ := C₀.baseChange L) Q.point
  let σ : Spec (CommRingCat.of L) ⟶ (C₀.baseChange L).left :=
    Spec.map (CommRingCat.ofHom ψ) ≫ (C₀.baseChange L).left.fromSpecResidueField Q.point
  have hσhom : σ ≫ (C₀.baseChange L).hom = 𝟙 (Spec (CommRingCat.of L)) := by
    show (Spec.map (CommRingCat.ofHom ψ) ≫
      (C₀.baseChange L).left.fromSpecResidueField Q.point) ≫ (C₀.baseChange L).hom = _
    rw [Category.assoc, hkey, ← Spec.map_comp, ← CommRingCat.ofHom_comp (algebraMap L _) ψ, hψ]
    simp
  have hσpoint : σ (IsLocalRing.closedPoint L) = Q.point := by
    show (Spec.map (CommRingCat.ofHom ψ) ≫
      (C₀.baseChange L).left.fromSpecResidueField Q.point) (IsLocalRing.closedPoint L) = Q.point
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply Q.point _
  have hfst : Work.CurveBasics.Curve.baseChangeFst C₀ L ≫ C₀.hom
      = (C₀.baseChange L).hom ≫ Work.CurveBasics.Curve.specMap k L := by
    rw [Work.CurveBasics.Curve.baseChangeFst, Work.CurveBasics.Curve.baseChange_hom]
    simp only [Work.CurveBasics.Curve.baseChangeHom, Work.CurveBasics.Curve.baseChangeOver,
      Over.pullback_obj_hom]
    exact pullback.condition
  have hover : (σ ≫ Work.CurveBasics.Curve.baseChangeFst C₀ L) ≫ C₀.hom
      = (specOf (K := k) L).hom := by
    rw [Category.assoc, hfst, ← Category.assoc, hσhom, Category.id_comp]
    rfl
  let p : Work.SpecLin.CurveFPt C₀ L :=
    Over.homMk (σ ≫ Work.CurveBasics.Curve.baseChangeFst C₀ L) hover
  have hptLeft : Work.SpecLin.ptLeft p = σ := by
    have h1 : Work.SpecLin.ptLeft p ≫ Work.CurveBasics.Curve.baseChangeFst C₀ L
        = σ ≫ Work.CurveBasics.Curve.baseChangeFst C₀ L := by
      rw [Work.SpecLin.ptLeft_fst]
      rfl
    have h2 : Work.SpecLin.ptLeft p ≫ (C₀.baseChange L).hom
        = σ ≫ (C₀.baseChange L).hom := by
      rw [ptLeft_comp_hom, hσhom]
    exact pullback.hom_ext h1 h2
  refine ⟨p, ?_⟩
  apply Subtype.ext
  show Work.SpecLin.ptToPoint p = Q.point
  rw [Work.SpecLin.ptToPoint, hptLeft]
  exact hσpoint

/-- Every effective divisor of degree one on `C_F` is the point divisor of an `F`-point of `C`.

Indeed an effective divisor of degree one is a single closed point `z` of `C_F` with residue
degree `[κ(z):F] = 1`, hence `κ(z) = F`; such a point is a section of `C_F ⟶ Spec F`, whose
composite with the projection `C_F ⟶ C` is an `F`-point `p` of `C` with `ptLeft p` the section,
i.e. `ptDiv p = D`.  This is the `ptDiv_complete` dictionary required to instantiate the
interface `Work.SpecLin.SymGeom` from area `SY`'s symmetric powers.

Route: from `hD` and `hdeg`, the Finsupp `D` has a single nonzero coefficient, namely `1` at one
place `Q` with `[κ(Q):F] = 1`; `κ(Q) ≅ F` as `F`-algebras, so the canonical `Spec F ⟶ C_F`
factoring through `Spec κ(Q)` is a section of `C_F ⟶ Spec F`; composing with
`Work.CurveBasics.Curve.baseChangeFst` gives an `F`-point `p` of `C` with
`Work.SpecLin.ptLeft p` equal to that section (pullback `hom_ext`), hence `ptPlace p = Q`. -/
theorem ptDiv_complete {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {F : Type u}
    [Field F] [Algebra K F] (D : Work.SpecLin.Dv C F) (hD : D.IsEffective)
    (hdeg : (C.baseChange F).deg D = 1) :
    ∃ p : Work.SpecLin.CurveFPt C F, Work.SpecLin.ptDiv p = D := by
  obtain ⟨Q, hQeq, hQdeg⟩ :=
    effective_deg_one_eq_single (C₀ := C.baseChange F) hD hdeg
  obtain ⟨p, hp⟩ := exists_ptPlace_eq (C₀ := C) (L := F) Q hQdeg
  refine ⟨p, ?_⟩
  rw [Work.SpecLin.ptDiv, hp, hQeq]
  rfl

end Work.SpecLin.Points
