/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Invariance of the Brill–Noether determinant under a permutation of the factors (area CH)

`bnDelta C U n s = det (s_j(x_m))²` is the section of `Γ(C^n, U^n)` cutting out the
Brill–Noether chart of §3.5 (`Submission/Work/Charts/ChartCg.lean`).  It is a section of the
product `C^n = C × … × C`, and its value at a field point depends on the matrix of the values
of the sections `s_j` at the `n` coordinates of the point.  Permuting the factors of the product
permutes the columns of that matrix, hence multiplies its determinant by the sign of the
permutation — and the **square** of the section is therefore invariant:

  `evalSection (q ≫ permIso σ) (bnDelta C U n s) = evalSection q (bnDelta C U n s)`.

This is the `S_n`-invariance of `δ` used in the `S_g`-descent step of Property 2 of
`Submission/Work/Charts/NOTES.md` §3.5 (see the discussion around line 787): two lifts of a point
of `Sym^n C` differ by a permutation, and `det²` kills the sign of the permutation.

The proof is `eval_bnDelta` at both points, the coordinate formula
`coord (p ≫ permIso σ) m = coord p (σ.symm m)`, `Matrix.det_permute'` and `(sign σ) ^ 2 = 1`.
-/
import Mathlib
import Submission.Work.Charts.Step3Defs
import Submission.Work.Charts.eval_bnDelta
import Submission.Work.SymQuot.ProdOpen

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.Charts

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

noncomputable section

/-- **The coordinates of a permuted point.**  The `m`-th coordinate of `p ≫ permIso σ` is the
`σ.symm m`-th coordinate of `p`: this is the projection formula `permIso_hom_proj` of area `SY`
transported to `K`-points. -/
theorem coord_permIso {K : Type u} [Field K] {C : CurveBasics.Curve K} {n : ℕ}
    {F : Type u} [Field F] [Algebra K F] (p : GCBasics.FPt (Cprod C n) F)
    (σ : Equiv.Perm (Fin n)) (m : Fin n) :
    coord (ptComp p (Work.SymQuot.permIso C.toOver σ).hom) m = coord p (σ.symm m) := by
  simp only [coord, ptComp_apply, Category.assoc]
  rw [Work.SymQuot.Product.permIso_hom_proj]

theorem eval_bnDelta_perm {K : Type u} [Field K] {C : Work.CurveBasics.Curve K} {n : ℕ}
    [Work.SpecLin.DivBase C] [Work.SpecLin.SymGeom C n] (U : C.left.Opens)
    (s : Fin n → (C.left.presheaf.obj (Opposite.op U))) {F : Type u} [Field F] [Algebra K F]
    (q : Work.GCBasics.FPt (Work.Charts.Cprod C n) F)
    (hq : Work.GCBasics.RPt.LandsIn q (Work.Charts.cgOpen C U n))
    (σ : Equiv.Perm (Fin n))
    (hq' : Work.GCBasics.RPt.LandsIn
      (Work.Charts.ptComp q (Work.SymQuot.permIso C.toOver σ).hom)
      (Work.Charts.cgOpen C U n)) :
    Work.Charts.evalSection
        (Work.Charts.ptComp q (Work.SymQuot.permIso C.toOver σ).hom).left hq'
        (Work.Charts.bnDelta C U n s) =
      Work.Charts.evalSection q.left hq (Work.Charts.bnDelta C U n s) := by
  -- Evaluate `bnDelta = det²` at both points.
  rw [eval_bnDelta, eval_bnDelta]
  -- The evaluation matrix at the permuted point is the evaluation matrix at `q` with its
  -- columns permuted by `σ.symm`.
  have hM : (Matrix.of fun j m => evalSection
        (coord (ptComp q (Work.SymQuot.permIso C.toOver σ).hom) m).left
        (coord_landsIn hq' m) (s j))
      = (Matrix.of fun j m => evalSection (coord q m).left
          (coord_landsIn hq m) (s j)).submatrix id σ.symm := by
    ext j m
    simp only [Matrix.of_apply, Matrix.submatrix_apply]
    simp only [coord_permIso]
    rfl
  rw [hM, Matrix.det_permute']
  -- Permuting the columns of a matrix multiplies its determinant by `sign σ`, whose square is
  -- `1`; the square of `δ` therefore does not see the permutation.
  have hsign : (↑↑(Equiv.Perm.sign σ.symm) : F) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h <;> simp [h]
  rw [mul_pow, hsign, one_mul]

end

end Work.Charts
