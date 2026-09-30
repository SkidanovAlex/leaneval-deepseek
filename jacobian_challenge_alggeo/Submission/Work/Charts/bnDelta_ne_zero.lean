/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — the Brill–Noether determinant section is nonzero once one point has invertible
evaluation matrix

This is the first step of the nonemptiness of the Brill–Noether chart of `ChartCg.lean`: if the
determinant `det (s_j(x_m))` is nonzero at *some* field point of `C^g` landing in `U^g`, then the
section `bnDelta = det (s_j(x_m))²` is nonzero in `Γ(C^g, U^g)`.

The point is that `eval_bnDelta` computes the value of `bnDelta` at a field point as the *square*
of that determinant, and a square of a nonzero element of a field is nonzero.
-/
import Submission.Work.Charts.ChartCg
import Submission.Work.Charts.eval_bnDelta

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

/-- **The Brill–Noether determinant section is nonzero** as soon as the determinant of the
evaluation matrix is nonzero at one field point of `C^g` landing in `U^g`. -/
theorem bnDelta_ne_zero {K : Type u} [Field K] {C : Curve K} [Work.SpecLin.DivBase C]
    (R : RochData C) [Work.SpecLin.SymGeom C R.g] (U : C.left.Opens)
    (s : Fin R.g → (C.left.presheaf.obj (Opposite.op U)))
    (hnonvan : ∃ (F : Type u) (_ : Field F) (_ : Algebra K F)
      (p : FPt (Cprod C R.g) F) (hp : RPt.LandsIn p (cgOpen C U R.g)),
      (Matrix.det (Matrix.of (fun j m => evalSection (coord p m).left
        (coord_landsIn hp m) (s j)))) ≠ 0) :
    bnDelta C U R.g s ≠ 0 := by
  obtain ⟨F, hF, hAlg, p, hp, hdet⟩ := hnonvan
  intro hzero
  have h1 : evalSection p.left hp (bnDelta C U R.g s) = 0 := by
    rw [hzero]
    exact map_zero (evalSectionHom p.left hp)
  rw [eval_bnDelta U s p hp] at h1
  exact hdet (sq_eq_zero_iff.mp h1)

end

end Work.Charts
