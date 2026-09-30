/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The value at a field point of the Brill–Noether determinant (area CH)

`bnDelta C U n s = det (s_j(x_m))²` is the section of `Γ(C^n, U^n)` cutting out the
Brill–Noether chart of §3.5 (`Submission/Work/Charts/ChartCg.lean`).  This file evaluates
it at a field point `p` of `C^n` landing in `U^n`:

  `δ(p) = det (evalSection (coord p m) (s j))²`

i.e. the value of `δ` at `p` is the square of the determinant of the matrix of the values of
the sections `s_j` at the `n` coordinates `coord p m` of `p`.

The proof has three ingredients:

* `evalSectionHom` — the evaluation `evalSection p hp` is a ring homomorphism
  `Γ(X,U) →+* F`, being the composite of the pullback `p.appLE` and the canonical isomorphism
  `Γ(Spec F, ⊤) ≅ F`; consequently it commutes with `det` (`RingHom.map_det`) and with `^2`;
* `evalSection_pullSection` — evaluating a section pulled back along a projection `C^n ⟶ C`
  at `p` is evaluating the original section at the corresponding coordinate of `p`
  (`Scheme.Hom.appLE_comp_appLE`);
* assembling these two gives the stated formula.
-/
import Mathlib
import Submission.Work.Charts.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

/-- **The evaluation of a section at a field point, as a ring homomorphism.**

`evalSection p hp : Γ(X,U) →+* F` sends a section `s` to its pullback along `p`, read in
`F ≅ Γ(Spec F, ⊤)`.  The composite is a ring homomorphism because both `p.appLE` and the
canonical isomorphism `Γ(Spec F, ⊤) ≅ F` are. -/
def evalSectionHom {X : Scheme.{u}} {F : Type u} [Field F] {U : X.Opens}
    (p : Spec (CommRingCat.of F) ⟶ X)
    (hp : p.base (IsLocalRing.closedPoint F) ∈ U) : ↑Γ(X, U) →+* F :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp
    (Scheme.Hom.appLE p U ⊤ (fun x _ => by
      show p x ∈ U
      have hx : x = IsLocalRing.closedPoint F := Subsingleton.elim _ _
      rw [hx]
      exact hp)).hom

/-- `evalSectionHom` is `evalSection` by definition. -/
theorem evalSectionHom_apply {X : Scheme.{u}} {F : Type u} [Field F] {U : X.Opens}
    (p : Spec (CommRingCat.of F) ⟶ X) (hp : p.base (IsLocalRing.closedPoint F) ∈ U)
    (s : ↑Γ(X, U)) : evalSectionHom p hp s = evalSection p hp s := rfl

/-- **Evaluating a pulled-back section at a point of the product.**

For a point `p` of `C^n` landing in `U^n`, the value at `p` of the section of `Γ(C^n, U^n)`
obtained by pulling `s ∈ Γ(C,U)` back along the `m`-th projection is the value of `s` at the
`m`-th coordinate of `p`.

This is functoriality of `Scheme.Hom.appLE` for the composite `Spec F ⟶ C^n ⟶ C`. -/
theorem evalSection_pullSection {K : Type u} [Field K] {C : CurveBasics.Curve K} {n : ℕ}
    {U : C.left.Opens} {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Cprod C n) F) (hp : RPt.LandsIn p (cgOpen C U n))
    (m : Fin n) (s : ↑Γ(C.left, U)) :
    evalSection p.left hp (pullSection C U n m s)
      = evalSection (coord p m).left (coord_landsIn hp m) s := by
  unfold evalSection pullSection
  congr 1
  rw [← CommRingCat.comp_apply]
  rw [Scheme.Hom.appLE_comp_appLE]
  simp only [coord, Over.comp_left]

theorem eval_bnDelta {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] {n : ℕ} [Work.SpecLin.SymGeom C n] (U : C.left.Opens)
    (s : Fin n → (C.left.presheaf.obj (Opposite.op U))) {F : Type u} [Field F] [Algebra K F]
    (p : Work.GCBasics.FPt (Work.Charts.Cprod C n) F)
    (hp : Work.GCBasics.RPt.LandsIn p (Work.Charts.cgOpen C U n)) :
    Work.Charts.evalSection p.left hp (Work.Charts.bnDelta C U n s) =
      (Matrix.det (Matrix.of (fun j m => Work.Charts.evalSection
        (Work.Charts.coord p m).left (Work.Charts.coord_landsIn hp m) (s j)))) ^ 2 := by
  -- `bnDelta = det ^ 2`, and evaluation is multiplicative.
  have h1 : evalSection p.left hp (bnDelta C U n s)
      = (evalSection p.left hp (bnMatrix C U n s).det) ^ 2 := by
    unfold bnDelta
    rw [pow_two, pow_two]
    simp only [evalSection]
    rw [map_mul, map_mul]
  rw [h1]
  -- Evaluation commutes with `det` (`RingHom.map_det`).
  have h2 : evalSection p.left hp ((bnMatrix C U n s).det)
      = ((evalSectionHom p.left hp).mapMatrix (bnMatrix C U n s)).det := by
    rw [← evalSectionHom_apply (p := p.left) (hp := hp), RingHom.map_det]
  rw [h2]
  -- The entries evaluate by `evalSection_pullSection`.
  have h3 : (evalSectionHom p.left hp).mapMatrix (bnMatrix C U n s)
      = Matrix.of (fun j m => evalSection (coord p m).left (coord_landsIn hp m) (s j)) := by
    ext j m
    rw [RingHom.mapMatrix_apply, Matrix.of_apply]
    exact evalSection_pullSection p hp m (s j)
  rw [h3]

end

end Work.Charts
