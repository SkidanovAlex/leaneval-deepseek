/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area SpecLin — shared conventions (points, divisors, linear equivalence)

This file fixes the *conventions* used by area `PR` (`Submission/Work/SpecLin`) of the
Jacobian drive, mirroring section 2 of `NOTES_LEAD_jacobian_GC.md`:

* `Work.SpecLin.Sch K` — the category of `K`-schemes (`Over (Spec K)`);
* `Work.SpecLin.specOf R` — `Spec R` as a `K`-scheme, for a `K`-algebra `R`;
* `Work.SpecLin.RPt X R` — the `R`-valued points of `X`; `FPt` is the case of a field;
* `Work.SpecLin.RPt.map` — extension of scalars on points;
* `Work.SpecLin.genPt R`, `Work.SpecLin.closedPt R` — the generic and the closed point of
  `Spec R`, as maps `Spec (FractionRing R) ⟶ Spec R` and
  `Spec (IsLocalRing.ResidueField R) ⟶ Spec R`;
* `Work.SpecLin.Dv C F` — divisors on `C_F = C.baseChange F`;
* `Work.SpecLin.LinEquiv C D D'` — linear equivalence of divisors over a field.

These are *definitions only*: they are the vocabulary in which `specLin` and the whole of
area `PR` are stated.  When area `GB` (`Submission/Work/GCBasics`) delivers the same
conventions in namespace `Work.GC`, the two are definitionally equal and either can be
used; nothing here is a mathematical result that would need to be re-derived.
-/
import Mathlib
import Submission.Work.CurveBasics.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SpecLin

variable {K : Type u} [Field K]

/-- The category of schemes over a field `K`, i.e. `Over (Spec K)`. -/
noncomputable abbrev Sch (K : Type u) [Field K] : Type (u + 1) :=
  Over (Spec (CommRingCat.of K))

/-- `Spec R` as a scheme over `K`, for a `K`-algebra `R`. -/
noncomputable abbrev specOf (R : Type u) [CommRing R] [Algebra K R] : Sch K :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K R)))

/-- The morphism `Spec R' ⟶ Spec R` induced by a ring map which is compatible with the
structure maps to `Spec K`. -/
noncomputable def specOfMapHom {R R' : Type u} [CommRing R] [CommRing R'] [Algebra K R]
    [Algebra K R'] (f : R →+* R')
    (hf : ∀ k : K, f (algebraMap K R k) = algebraMap K R' k) :
    specOf (K := K) R' ⟶ specOf (K := K) R :=
  Over.homMk (Spec.map (CommRingCat.ofHom f)) (by
    have h : f.comp (algebraMap K R) = algebraMap K R' := RingHom.ext hf
    show Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom (algebraMap K R)) =
      Spec.map (CommRingCat.ofHom (algebraMap K R'))
    rw [← Spec.map_comp (CommRingCat.ofHom (algebraMap K R)) (CommRingCat.ofHom f),
      ← CommRingCat.ofHom_comp (algebraMap K R) f, h])

/-- The morphism `Spec R' ⟶ Spec R` induced by a `K`-algebra homomorphism. -/
noncomputable def specOfMap {R R' : Type u} [CommRing R] [CommRing R'] [Algebra K R]
    [Algebra K R'] (e : R →ₐ[K] R') : specOf (K := K) R' ⟶ specOf (K := K) R :=
  specOfMapHom e.toRingHom e.commutes

@[simp]
theorem specOfMap_id {R : Type u} [CommRing R] [Algebra K R] :
    specOfMap (K := K) (AlgHom.id K R) = 𝟙 (specOf (K := K) R) := by
  apply Over.OverMorphism.ext
  simp [specOfMap, specOfMapHom]

theorem specOfMap_comp {R R' R'' : Type u} [CommRing R] [CommRing R'] [CommRing R'']
    [Algebra K R] [Algebra K R'] [Algebra K R''] (e : R →ₐ[K] R') (e' : R' →ₐ[K] R'') :
    specOfMap (K := K) (e'.comp e) =
      specOfMap (K := K) e' ≫ specOfMap (K := K) e := by
  apply Over.OverMorphism.ext
  simp only [specOfMap, specOfMapHom, Over.homMk_left, Over.comp_left]
  rw [show (e'.comp e).toRingHom = e'.toRingHom.comp e.toRingHom from rfl,
    CommRingCat.ofHom_comp, Spec.map_comp]

/-- `R`-valued points of a `K`-scheme `X`: morphisms `Spec R ⟶ X` over `Spec K`. -/
abbrev RPt (X : Sch K) (R : Type u) [CommRing R] [Algebra K R] : Type u :=
  specOf (K := K) R ⟶ X

/-- `F`-valued points of a `K`-scheme `X`, for a field `F` over `K`. -/
abbrev FPt (X : Sch K) (F : Type u) [Field F] [Algebra K F] : Type u :=
  RPt X F

/-- Extension of scalars on `R`-valued points, along a `K`-algebra map `R →ₐ[K] R'`. -/
noncomputable def RPt.map {X : Sch K} {R R' : Type u} [CommRing R] [CommRing R']
    [Algebra K R] [Algebra K R'] (e : R →ₐ[K] R') (p : RPt X R) : RPt X R' :=
  specOfMap (K := K) e ≫ p

@[simp]
theorem RPt.map_id {X : Sch K} {R : Type u} [CommRing R] [Algebra K R] (p : RPt X R) :
    RPt.map (AlgHom.id K R) p = p := by
  simp [RPt.map]

@[simp]
theorem RPt.map_comp {X : Sch K} {R R' R'' : Type u} [CommRing R] [CommRing R'']
    [CommRing R'] [Algebra K R] [Algebra K R'] [Algebra K R'']
    (e : R →ₐ[K] R') (e' : R' →ₐ[K] R'') (p : RPt X R) :
    RPt.map (e'.comp e) p = RPt.map e' (RPt.map e p) := by
  simp only [RPt.map, specOfMap_comp, Category.assoc]

/-- The generic point of `Spec R`, as a morphism over `K`. -/
noncomputable def genPt (R : Type u) [CommRing R] [IsDomain R] [Algebra K R] :
    specOf (K := K) (FractionRing R) ⟶ specOf (K := K) R :=
  specOfMapHom (K := K) (algebraMap R (FractionRing R))
    (fun k => (IsScalarTower.algebraMap_apply K R (FractionRing R) k).symm)

/-- The closed point of `Spec R`, for a local ring `R`, as a morphism over `K`. -/
noncomputable def closedPt (R : Type u) [CommRing R] [IsLocalRing R] [Algebra K R] :
    specOf (K := K) (IsLocalRing.ResidueField R) ⟶ specOf (K := K) R :=
  specOfMapHom (K := K) (algebraMap R (IsLocalRing.ResidueField R))
    (fun k => (IsScalarTower.algebraMap_apply K R (IsLocalRing.ResidueField R) k).symm)

/-- An `R`-valued point of `X` (for `R` local) "lands in" an open subscheme `U` if the
closed point of `Spec R` is mapped into `U`. -/
def LandsIn {X : Sch K} {R : Type u} [CommRing R] [IsLocalRing R] [Algebra K R]
    (p : RPt X R) (U : X.left.Opens) : Prop :=
  p.left.base (IsLocalRing.closedPoint R) ∈ U

/-- Divisor group of the curve `C_F`, where `C_F = C.baseChange F`. -/
abbrev Dv (C : Work.CurveBasics.Curve K) (F : Type u) [Field F] [Algebra K F] : Type u :=
  (C.baseChange F).Div

/-- Two divisors on `C_F` are linearly equivalent if they differ by a principal divisor. -/
def LinEquiv (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F]
    (D D' : Dv C F) : Prop :=
  ∃ h : (C.baseChange F).functionField, h ≠ 0 ∧ (C.baseChange F).div h = D - D'

/-- The principal divisor of `1`. -/
@[simp]
theorem div_one (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F] :
    (C.baseChange F).div 1 = 0 := by
  ext Q
  rw [Work.CurveBasics.Curve.div_apply, Finsupp.zero_apply]
  exact Work.CurveBasics.Order.ord_one _ Q

theorem linEquiv_refl (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F]
    (D : Dv C F) : LinEquiv C D D :=
  ⟨1, one_ne_zero, by rw [div_one, sub_self]⟩

/-- The principal divisor of a quotient of rational functions. -/
theorem div_div (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F]
    {f g : (C.baseChange F).functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    (C.baseChange F).div (f / g) = (C.baseChange F).div f - (C.baseChange F).div g := by
  rw [div_eq_mul_inv, Work.CurveBasics.Curve.div_mul _ hf (inv_ne_zero hg),
    Work.CurveBasics.Order.div_inv (C.baseChange F) hg]
  abel

theorem LinEquiv.symm (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F]
    {D D' : Dv C F} (h : LinEquiv C D D') : LinEquiv C D' D := by
  obtain ⟨f, hf, hdiv⟩ := h
  refine ⟨f⁻¹, inv_ne_zero hf, ?_⟩
  rw [Work.CurveBasics.Order.div_inv _ hf, hdiv]
  abel

theorem LinEquiv.trans (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F]
    {D D' D'' : Dv C F} (h : LinEquiv C D D') (h' : LinEquiv C D' D'') :
    LinEquiv C D D'' := by
  obtain ⟨f, hf, hdiv⟩ := h
  obtain ⟨g, hg, hdiv'⟩ := h'
  refine ⟨f * g, mul_ne_zero hf hg, ?_⟩
  rw [Work.CurveBasics.Curve.div_mul _ hf hg, hdiv, hdiv']
  abel

theorem linEquiv_iff_sub (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F]
    (D D' : Dv C F) : LinEquiv C D D' ↔ LinEquiv C (D - D') 0 := by
  constructor <;> rintro ⟨f, hf, hdiv⟩
  · exact ⟨f, hf, by rw [hdiv]; abel⟩
  · exact ⟨f, hf, by rw [hdiv]; abel⟩

theorem LinEquiv.sub (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F]
    {A A' B B' : Dv C F} (h : LinEquiv C A A') (h' : LinEquiv C B B') :
    LinEquiv C (A - B) (A' - B') := by
  obtain ⟨f, hf, hdiv⟩ := h
  obtain ⟨g, hg, hdiv'⟩ := h'
  refine ⟨f / g, div_ne_zero hf hg, ?_⟩
  rw [div_div C hf hg, hdiv, hdiv']
  abel

theorem LinEquiv.add (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F]
    {A A' B B' : Dv C F} (h : LinEquiv C A A') (h' : LinEquiv C B B') :
    LinEquiv C (A + B) (A' + B') := by
  obtain ⟨f, hf, hdiv⟩ := h
  obtain ⟨g, hg, hdiv'⟩ := h'
  refine ⟨f * g, mul_ne_zero hf hg, ?_⟩
  rw [Work.CurveBasics.Curve.div_mul _ hf hg, hdiv, hdiv']
  abel

theorem LinEquiv.neg (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F]
    {A A' : Dv C F} (h : LinEquiv C A A') : LinEquiv C (-A) (-A') := by
  simpa using LinEquiv.sub C (linEquiv_refl C (0 : Dv C F)) h

theorem linEquiv_zero_iff (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F]
    (D : Dv C F) :
    LinEquiv C D 0 ↔ ∃ f : (C.baseChange F).functionField, f ≠ 0 ∧
      (C.baseChange F).div f = D := by
  constructor <;> rintro ⟨f, hf, hdiv⟩
  · exact ⟨f, hf, by rw [hdiv]; simp⟩
  · exact ⟨f, hf, by rw [hdiv]; simp⟩

theorem linEquiv_of_eq (C : Work.CurveBasics.Curve K) {F : Type u} [Field F] [Algebra K F]
    {D D' : Dv C F} (h : D = D') : LinEquiv C D D' :=
  h ▸ linEquiv_refl C D

end Work.SpecLin
