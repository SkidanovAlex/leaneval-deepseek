/-
# Namespace mirror of `Work.SpecLin.Core.mem_primeIdealOf_ptToPoint_iff`

This file is an exact copy of `Submission/Work/SpecLin/Core/mem_primeIdealOf_ptToPoint_iff.lean` (module `Work.SpecLin.Core.mem_primeIdealOf_ptToPoint_iff`), changed in exactly three ways:

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
import Mathlib
import Submission.Work.SpecLin.Up.Core.ordChart
import Submission.Work.SpecLin.Core.sectionPrime_genFibre_eq_ker
import Submission.Work.SpecLin.Core.primeIdealOf_fromSpec_eq_comap
import Submission.Work.SpecLin.Up.Core.linEquiv_of_sections
import Submission.Work.CurveBasics.All
import Submission.Work.SpecLin.Alt.chartDictionary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.SpecLin.Core
namespace Up

/-- **(D1c-geom, general form)** The prime of a point of an affine open chart which is the
image under `fromSpec` of a point of `Spec` of a ring map, with an arbitrary proof that the
point lies in the open set.  This is `Work.SpecLin.Core.primeIdealOf_fromSpec_eq_comap` with the
membership proof as a hypothesis, in the form in which it is applied below. -/
theorem primeIdealOf_fromSpec_eq_comap' {X : AlgebraicGeometry.Scheme} (U : X.Opens)
    (hU : AlgebraicGeometry.IsAffineOpen U) {k : Type u} [Field k]
    (ψ : X.presheaf.obj (Opposite.op U) →+* k) (z : AlgebraicGeometry.Spec (CommRingCat.of k))
    (hz : hU.fromSpec (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) z) ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) z), hz⟩
      = PrimeSpectrum.comap ψ z := by
  simp only [AlgebraicGeometry.IsAffineOpen.primeIdealOf]
  have h : (⟨hU.fromSpec (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) z), hz⟩ : ↑U)
      = hU.isoSpec.inv (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) z) := by
    apply Subtype.ext
    rfl
  rw [h, ← Scheme.Hom.comp_apply, hU.isoSpec.inv_hom_id]
  rfl

/-- **(D1c-geom, point form)** If a point `a` of an affine open `U` is the image under
`fromSpec` of the point of `Spec Γ(X,U)` attached to the ring map `ψ` at `z`, then the prime
ideal of `a` is the prime `comap ψ z`. -/
theorem primeIdealOf_eq_of_fromSpec_eq {X : AlgebraicGeometry.Scheme} {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) {k : Type u} [Field k]
    (ψ : X.presheaf.obj (Opposite.op U) →+* k) (z : AlgebraicGeometry.Spec (CommRingCat.of k))
    {a : X} (ha : a ∈ U)
    (haz : a = hU.fromSpec (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ψ) z)) :
    hU.primeIdealOf ⟨a, ha⟩ = PrimeSpectrum.comap ψ z := by
  subst haz
  exact primeIdealOf_fromSpec_eq_comap' U hU ψ z ha

/-- The closed point of a field is the zero ideal. -/
theorem closedPoint_asIdeal_eq_bot (R : Type u) [Field R] :
    (IsLocalRing.closedPoint R).asIdeal = ⊥ := by
  show IsLocalRing.maximalIdeal R = ⊥
  exact IsLocalRing.maximalIdeal_eq_bot

/-- **(K1-geom)** A chart section vanishes at the point of the section's generic fibre exactly
when its value (the generic fibre of `rgMap`) is zero. -/
theorem mem_primeIdealOf_ptToPoint_iff {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
    (s : Work.SpecLin.CurvePt C R)
    (hs : Set.range (s.left.base) ⊆ (W : Set C.left))
    (hle : C.bcOpens (FractionRing R) W ≤
      (TopologicalSpace.Opens.map (C.baseChangeFst (FractionRing R)).base).obj W)
    (a : C.left.presheaf.obj (Opposite.op W))
    (x : (C.baseChange (FractionRing R)).left)
    (hx : x ∈ C.bcOpens (FractionRing R) W)
    (hx' : x = Work.SpecLin.ptToPoint (Work.SpecLin.RPt.map
      (IsScalarTower.toAlgHom K R (FractionRing R)) s)) :
    (C.baseChangeFst (FractionRing R)).appLE W (C.bcOpens (FractionRing R) W) hle a
      ∈ ((Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (FractionRing R) W hW).primeIdealOf
          ⟨x, hx⟩).asIdeal
    ↔ ((IsScalarTower.toAlgHom K R (FractionRing R)).comp
        (Work.SpecLin.Core.Up.rgMap R W hW s hs)) a = 0 := by
  classical
  -- The generic fibre of `rgMap`, i.e. the algebra map evaluating chart sections at the
  -- generic fibre of the section, and the generic fibre `p := s^F` of the section.
  let ψ : C.left.presheaf.obj (Opposite.op W) →ₐ[K] FractionRing R :=
    (IsScalarTower.toAlgHom K R (FractionRing R)).comp (Work.SpecLin.Core.Up.rgMap R W hW s hs)
  let p : Work.SpecLin.CurveFPt C (FractionRing R) :=
    Work.SpecLin.RPt.map (IsScalarTower.toAlgHom K R (FractionRing R)) s
  -- `p` factors through the affine chart `W` via `ψ`, hence `x` is the image of a point of
  -- `Spec Γ(C,W)` under `fromSpec`.
  have hx'' : x = Work.SpecLin.ptToPoint p := hx'
  have hfac : p.left = (Work.SpecLin.specOfMap (K := K) ψ).left ≫ hW.fromSpec :=
    Work.SpecLin.Core.Up.genPtMap_fac R W hW s hs
  have hfx : C.baseChangeFst (FractionRing R) x
      = p.left.base (IsLocalRing.closedPoint (FractionRing R)) := by
    rw [hx'']
    exact Work.SpecLin.Alt.baseChangeFst_ptToPoint p
  have hpt : C.baseChangeFst (FractionRing R) x
      = hW.fromSpec (Spec.map (CommRingCat.ofHom ψ.toRingHom)
          (IsLocalRing.closedPoint (FractionRing R))) := by
    rw [hfx, hfac]
    rfl
  -- The prime of the image point of `x` in the chart `W ⊆ C` is the kernel of `ψ`.
  have key : hW.primeIdealOf
      (⟨C.baseChangeFst (FractionRing R) x, hle hx⟩ : ↥W)
      = PrimeSpectrum.comap ψ.toRingHom (IsLocalRing.closedPoint (FractionRing R)) :=
    primeIdealOf_eq_of_fromSpec_eq hW ψ.toRingHom _ (hle hx) hpt
  -- The prime of `x` in the chart `W_F ⊆ C_F` pulls back to the prime of `f x` in `W`.
  rw [← Ideal.mem_comap, ← PrimeSpectrum.comap_asIdeal,
    IsAffineOpen.comap_primeIdealOf_appLE W hW (C.bcOpens (FractionRing R) W)
        (Work.CurveBasics.BaseChange.isAffineOpen_bcOpens (FractionRing R) W hW) hle hx]
  -- Rewrite the membership in the chart ring of `C` through the kernel of `ψ`.
  show a ∈ (hW.primeIdealOf
      (⟨C.baseChangeFst (FractionRing R) x, hle hx⟩ : ↥W)).asIdeal
    ↔ ((IsScalarTower.toAlgHom K R (FractionRing R)).comp
        (Work.SpecLin.Core.Up.rgMap R W hW s hs)) a = 0
  rw [key, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, closedPoint_asIdeal_eq_bot, Ideal.mem_bot]
  exact Iff.rfl

end Up
end Work.SpecLin.Core

