/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dictionary lemmas for the affine-chart proof of specialisation of linear equivalence

These are the first, provable steps of the "dictionary" between the curve-theoretic
objects (`Work.SpecLin.ptDiv`, `Scheme.ord`, the places of `C_F` / `C_κ`) and the
affine-chart algebra (`A = Γ(C,W)`, `B = A ⊗_K R`, `P = m_R·B`, the section primes
`I_m = ker(B → R)`) which the remaining part of the chart proof of
`Work.SpecLin.Alt.chartCore` needs.  They are collected here because they are independent
of that proof and useful on their own.
-/
import Mathlib
import Submission.Work.SpecLin.Conventions
import Submission.Work.SpecLin.Points.Setup
import Submission.Work.SpecLin.Points.Basic
import Submission.Work.SpecLin.Setup.Basic
import Submission.Work.CurveBasics.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SpecLin.Alt

variable {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}

/-- The projection to `C` of the point of `C_F` determined by an `F`-point `p` is the image of
the closed point of `Spec F` under `p`.  (`ptLeft p` is a section of the separated morphism
`C_F ⟶ Spec F`, see `Work.SpecLin.Points.ptLeft_fst`.) -/
theorem baseChangeFst_ptToPoint {F : Type u} [Field F] [Algebra K F]
    (p : Work.SpecLin.CurveFPt C F) :
    Work.CurveBasics.Curve.baseChangeFst C F (Work.SpecLin.ptToPoint p)
      = p.left.base (IsLocalRing.closedPoint F) := by
  rw [Work.SpecLin.ptToPoint]
  exact congrArg (fun (f : Spec (CommRingCat.of F) ⟶ C.left) =>
      f (IsLocalRing.closedPoint F)) (Work.SpecLin.ptLeft_fst p)

open Work.CurveBasics in
/-- The generic fibre `genPt R ≫ s` of an `R`-point `s` of `C` whose image lies in the affine
open `W` lies in the affine chart `W_F = bcOpens F W` of the generic fibre `C_F`.

This is the first half of the chart dictionary for the generic fibre: it lets one speak of the
prime of `Γ(C_F, W_F) ≅ Γ(C,W) ⊗_K F` determined by the `F`-point. -/
theorem ptToPoint_genPt_mem (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range s.left.base ⊆ (W : Set C.left)) :
    Work.SpecLin.ptToPoint
        (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) s)
      ∈ C.bcOpens (FractionRing R) W := by
  rw [Curve.bcOpens]
  show Curve.baseChangeFst C (FractionRing R) _ ∈ (W : Set C.left)
  rw [show Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) s
      = Work.SpecLin.genPt R ≫ s from rfl]
  rw [baseChangeFst_ptToPoint]
  exact hs (Set.mem_range_self _)

open Work.CurveBasics in
/-- The special fibre `closedPt R ≫ s` of an `R`-point `s` of `C` whose image lies in the
affine open `W` lies in the affine chart `W_κ = bcOpens κ W` of the special fibre `C_κ`.

This is the first half of the chart dictionary for the special fibre. -/
theorem ptToPoint_closedPt_mem (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [Algebra K R] (W : C.left.Opens) (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range s.left.base ⊆ (W : Set C.left)) :
    Work.SpecLin.ptToPoint
        (Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) s)
      ∈ C.bcOpens (IsLocalRing.ResidueField R) W := by
  rw [Curve.bcOpens]
  show Curve.baseChangeFst C (IsLocalRing.ResidueField R) _ ∈ (W : Set C.left)
  rw [show Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (IsLocalRing.ResidueField R)) s
      = Work.SpecLin.closedPt R ≫ s from by
        rw [Work.SpecLin.closedPt_eq_specOfMap]; rfl]
  rw [baseChangeFst_ptToPoint]
  exact hs (Set.mem_range_self _)

open Scheme in
/-- `Scheme.Hom.appLE` with both open sets `⊤` is `Scheme.Hom.appTop`. -/
lemma Scheme.Hom.appLE_top_eq_appTop {X Y : Scheme} (f : X ⟶ Y)
    (e : ⊤ ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    f.appLE ⊤ (⊤ : X.Opens) e = f.appTop := by
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top]

/-- **Pullback of a section of the affine chart.**  For an affine open `W ⊆ C` with
`hW : IsAffineOpen W`, a field `F/K` and a `K`-algebra map `ψ : Γ(C,W) →ₐ[K] F`, let
`p := specOfMap ψ ≫ hW.fromSpec : Spec F ⟶ C` be the corresponding `F`-point of `C`.  Then the
pullback of the chart sections `Γ(C,W)` along the section of degree zero, transported to
global sections of `Spec F`, is exactly `ψ`:

`hW.fromSpec.app W ≫ (specOfMap ψ).left.appLE (hW.fromSpec ⁻¹ᵁ W) ⊤ _ ≫ (ΓSpecIso F).hom
  = ofHom ψ`.

This is the first half of the chart dictionary: it says that *evaluating a chart section at the
point `p`* agrees with the algebra map `ψ` that defines `p`.  Together with the identification of
the prime of `Γ(C_F, W_F)` at `ptToPoint p` with `ker ψ` it converts the curve-theoretic
statement `div h = Σ ptDiv (genPt R ≫ s_m) − …` into the chart-algebra statement
`ord_I(h) = #{m : I = I_m} − #{m : I = J_m}`. -/
theorem pullback_section {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {F : Type u}
    [Field F] [Algebra K F] (W : C.left.Opens) (hW : IsAffineOpen W)
    (ψ : Γ(C.left, W) →ₐ[K] F) :
    hW.fromSpec.app W
      ≫ (Work.SpecLin.specOfMap (K := K) ψ).left.appLE (hW.fromSpec ⁻¹ᵁ W) ⊤
          (by rw [IsAffineOpen.fromSpec_preimage_self, Scheme.Hom.preimage_top])
      ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom = CommRingCat.ofHom ψ.toRingHom := by
  rw [IsAffineOpen.fromSpec_app_self]
  simp only [Category.assoc]
  rw [Scheme.Hom.map_appLE_assoc, Scheme.Hom.appLE_top_eq_appTop,
    show Over.Hom.left (Work.SpecLin.specOfMap (K := K) ψ)
        = Spec.map (CommRingCat.ofHom ψ.toRingHom) from rfl,
    Scheme.ΓSpecIso_naturality]
  exact Iso.inv_hom_id_assoc (Scheme.ΓSpecIso Γ(C.left, W)) (CommRingCat.ofHom ψ.toRingHom)

/-- **Pullback of a section of the affine chart, composite form.**  With `p := specOfMap ψ ≫
hW.fromSpec` written as a composite, the pullback of the chart sections along `p`, transported to
global sections of `Spec F`, is `ψ`.  This is the form used when `p` is already known to factor
through the chart (e.g. `p = genPt R ≫ s` for an `R`-point `s` whose image lies in `W`). -/
theorem appLE_comp_fromSpec {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {F : Type u}
    [Field F] [Algebra K F] (W : C.left.Opens) (hW : IsAffineOpen W)
    (ψ : Γ(C.left, W) →ₐ[K] F) :
    ((Work.SpecLin.specOfMap (K := K) ψ).left ≫ hW.fromSpec).appLE W ⊤
        (by rw [Scheme.Hom.comp_preimage, IsAffineOpen.fromSpec_preimage_self,
            Scheme.Hom.preimage_top])
      ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom = CommRingCat.ofHom ψ.toRingHom := by
  rw [Scheme.Hom.comp_appLE]
  exact pullback_section (K := K) (C := C) W hW ψ

/-- `Scheme.Hom.appLE` is compatible with the morphism: for `h : f = g` the pullbacks agree. -/
lemma Scheme.Hom.appLE_congr_hom {X Y : Scheme} {f g : X ⟶ Y} (h : f = g) {U : Y.Opens}
    {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

/-- **Evaluation of chart sections at a point factoring through the chart.**  If the `F`-point
`p` factors through the affine chart `W` via `ψ : Γ(C,W) →ₐ[K] F` (`p.left = specOfMap ψ ≫
hW.fromSpec`), then the pullback of the chart sections along `p`, transported to global sections
of `Spec F`, is `ψ`.  This is `appLE_comp_fromSpec` in the `p.left` form in which it is applied to
`p = genPt R ≫ s`. -/
theorem appLE_pt_left {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {F : Type u}
    [Field F] [Algebra K F] (W : C.left.Opens) (hW : IsAffineOpen W)
    (ψ : Γ(C.left, W) →ₐ[K] F) (p : Work.SpecLin.CurveFPt C F)
    (hp : p.left = (Work.SpecLin.specOfMap (K := K) ψ).left ≫ hW.fromSpec)
    (e : ⊤ ≤ p.left ⁻¹ᵁ W) :
    p.left.appLE W ⊤ e ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom =
      CommRingCat.ofHom ψ.toRingHom := by
  rw [Scheme.Hom.appLE_congr_hom hp]
  exact appLE_comp_fromSpec (K := K) (C := C) W hW ψ

/-- **Membership in the chart.**  If an `F`-point `p` of `C` factors through the affine open
`W ⊆ C`, then `ptToPoint p` lies in the affine chart `bcOpens F W` of `C_F`.  This generalises
`ptToPoint_genPt_mem` / `ptToPoint_closedPt_mem` to an arbitrary factorisation and supplies the
`e`-hypothesis of `appLE_pt_left`. -/
theorem ptToPoint_mem_of_factors {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {F : Type u}
    [Field F] [Algebra K F] (W : C.left.Opens) (hW : IsAffineOpen W)
    (ψ : Γ(C.left, W) →ₐ[K] F) (p : Work.SpecLin.CurveFPt C F)
    (hp : p.left = (Work.SpecLin.specOfMap (K := K) ψ).left ≫ hW.fromSpec) :
    Work.SpecLin.ptToPoint p ∈ C.bcOpens F W := by
  show Work.CurveBasics.Curve.baseChangeFst C F (Work.SpecLin.ptToPoint p) ∈ (W : Set C.left)
  rw [baseChangeFst_ptToPoint, hp]
  exact (IsAffineOpen.range_fromSpec hW).le (Set.mem_range_self
    ((Over.Hom.left (Work.SpecLin.specOfMap (K := K) ψ)) (IsLocalRing.closedPoint F)))

end Work.SpecLin.Alt
