/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The affine chart `C ∖ (poles of x)` and its morphism to the affine line

For a smooth, proper, geometrically irreducible curve `C` over a field `K` and a rational
function `x ∈ K(C)`, the open subscheme `W := regularOpens C x` (the complement of the pole set
of `x`) carries the morphism

`phi W s : W ⟶ 𝔸¹_K`,  `W ⟶ Spec K[MvPolynomial PUnit K]`

induced by a section `s ∈ Γ(C, W)` restricting to `x`.  The plan of the proof that `W` is affine
is: `phi W s` is proper (valuative criterion, using that `C` is proper over `K`) and locally
quasi-finite (the fibres are the (finite) zero loci of polynomials in `x`), hence `IsFinite`, hence
`W` is affine because `𝔸¹_K` is.
-/
import Mathlib
import Submission.Work.CurveBasics.All
import Submission.Work.SpecLin.Chart.Regular

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.SpecLin.Alt

/-- The affine line over `Spec K`, indexed by the one-point type `PUnit`. -/
noncomputable abbrev A1 (K : Type u) [Field K] : Scheme.{u} :=
  AffineSpace PUnit.{u+1} (Spec (CommRingCat.of K))

/-- The structure morphism `𝔸¹_K ⟶ Spec K`. -/
noncomputable abbrev A1Over (K : Type u) [Field K] : A1 K ⟶ Spec (CommRingCat.of K) :=
  (AffineSpace PUnit.{u+1} (Spec (CommRingCat.of K))) ↘ (Spec (CommRingCat.of K))

variable {K : Type u} [Field K] (C : Work.CurveBasics.Curve K)

/-- The open subscheme of `C` on which the rational function `x` is regular. -/
noncomputable abbrev regularOpens (x : C.functionField) : C.left.Opens :=
  Work.SpecLin.Chart.regularOpens C x

/-- The structure morphism of an open subscheme `W` of the curve to `Spec K`. -/
noncomputable abbrev structHom (W : C.left.Opens) : W.toScheme ⟶ Spec (CommRingCat.of K) :=
  W.ι ≫ C.hom

variable {C} in
/-- The morphism `W ⟶ 𝔸¹_K` over `Spec K` whose coordinate function is the section `s`. -/
noncomputable def phi (W : C.left.Opens) (s : Γ(C.left, W)) : W.toScheme ⟶ A1 K :=
  AffineSpace.homOfVector (structHom C W) (fun _ => W.topIso.inv s)

/-- `phi` is a morphism over `Spec K`. -/
@[reassoc (attr := simp)]
theorem phi_over {W : C.left.Opens} (s : Γ(C.left, W)) :
    phi W s ≫ A1Over K = structHom C W :=
  AffineSpace.homOfVector_over (structHom C W) _

/-- The coordinate function of `𝔸¹_K` pulls back to the section `s` defining `phi`. -/
@[simp]
theorem phi_appTop_coord {W : C.left.Opens} (s : Γ(C.left, W)) :
    (phi W s).appTop (AffineSpace.coord (Spec (CommRingCat.of K)) PUnit.unit) = W.topIso.inv s :=
  AffineSpace.homOfVector_appTop_coord (structHom C W) _ PUnit.unit

/-- An open subscheme of a curve is a Noetherian scheme. -/
theorem isNoetherian_toScheme (W : C.left.Opens) : IsNoetherian W.toScheme := by
  have h : IsCompact (W : Set C.left) := TopologicalSpace.NoetherianSpace.isCompact _
  haveI : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp h
  exact AlgebraicGeometry.IsNoetherian.mk

/-- `phi` is quasi-compact: its source is an open subscheme of the Noetherian curve. -/
theorem quasiCompact_phi {W : C.left.Opens} (s : Γ(C.left, W)) : QuasiCompact (phi W s) := by
  haveI := isNoetherian_toScheme C W
  infer_instance

/-- `phi` is locally of finite type: the composite with `𝔸¹_K ⟶ Spec K` is the structure
morphism of an open subscheme of a curve, and local finiteness of type cancels. -/
theorem locallyOfFiniteType_phi {W : C.left.Opens} (s : Γ(C.left, W)) :
    LocallyOfFiniteType (phi W s) := by
  have h : LocallyOfFiniteType (phi W s ≫ A1Over K) := by
    rw [phi_over]
    infer_instance
  exact locallyOfFiniteType_of_comp (phi W s) (A1Over K)

/-- `phi` is quasi-separated. -/
theorem quasiSeparated_phi {W : C.left.Opens} (s : Γ(C.left, W)) : QuasiSeparated (phi W s) :=
  inferInstance

end Work.SpecLin.Alt
