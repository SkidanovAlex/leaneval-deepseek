/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area BNChart (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.B4)

# Area BNChart, B4 — the Brill–Noether chart over `k`, from the *true* direction of `hcrit`

`Work.Charts.nonempty_BNData_of_basis` builds the Brill–Noether chart `BNData C R` from the
*iff* form of the Brill–Noether criterion

  `det (s_j (x_m)) ≠ 0 ↔ i (divOf (quotMap p)) = 0`.

That iff is **false** when two of the points `x_m` coincide (two equal columns make the
determinant vanish while `i` may well be `0`), so it cannot be instantiated for a concrete
curve.  This file re-issues the construction with the criterion split into the two statements
that are actually used:

* the **true direction** `hcrit` : `det ≠ 0 → i (divOf (quotMap p)) = 0`, used to show that the
  points of the chart are non-special;
* the **existence** of one point with `det ≠ 0`, used to show that the chart is nonempty.

Everything else (the determinant section `bnDelta`, its non-vanishing locus `chartOpen`, the
affine open `Ω ⊆ chartOpen`) is taken verbatim from area `CH`.
-/
import Submission.Work.Charts.nonempty_BNData
import Submission.Work.Charts.ChartCg
import Submission.Work.Charts.bnDelta_ne_zero
import Submission.Work.Charts.chartOpen_ne_bot
import Submission.Work.Charts.iOf_eq_zero_of_landsIn_chartOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

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

namespace Work.BNChart

open Work.CurveBasics Work.GCBasics Work.Charts

noncomputable section

variable {K : Type u} [Field K]

/-- The quotient map `C^n ⟶ Sym^n C` is a closed map. -/
theorem quotMapIsClosedMap (C : Curve K) (n : ℕ) [SpecLin.DivBase C]
    [SpecLin.SymGeom C n] : IsClosedMap (quotMap C n).left.base :=
  Work.Charts.quotMapIsClosedMap (C := C) n

/-- **B4: the Brill–Noether chart exists**, from the true direction of the criterion and the
existence of a point with invertible evaluation matrix.

This is `Work.Charts.nonempty_BNData_of_basis` with `hcrit` replaced by its `.mp` direction and
`hnonspec` replaced by the (slightly stronger, and true) datum `hnonvan` that the determinant is
invertible at one point.  The chart is the affine open `Ω ⊆ chartOpen C g U s` and the section
is the constant `1`, exactly as in the original construction. -/
theorem nonempty_BNData_of_hcrit {C : Curve K} [SpecLin.DivBase C] (R : RochData C)
    [SpecLin.SymGeom C R.g] (U : C.left.Opens) (hU : IsAffineOpen U) (Q : C.Place)
    (h : Fin R.g → (C.baseChange K).functionField)
    (h_mem : ∀ j, 0 ≤ (C.baseChange K).div (h j) + R.W)
    (h_span : (C.baseChange K).L R.W = Submodule.span K (Set.range h))
    (s : Fin R.g → (C.left.presheaf.obj (Opposite.op U)))
    (hcrit : ∀ {F : Type u} [Field F] [Algebra K F]
      (p : FPt (Cprod C R.g) F) (hp : RPt.LandsIn p (cgOpen C U R.g)),
      (Matrix.det (Matrix.of (fun j m => evalSection (coord p m).left
        (coord_landsIn hp m) (s j)))) ≠ 0 →
        iOf C R.W (SpecLin.SymGeom.divOf (ptComp p (quotMap C R.g))) = 0)
    (hnonvan : ∃ (F : Type u) (_ : Field F) (_ : Algebra K F)
      (p : FPt (Cprod C R.g) F) (hp : RPt.LandsIn p (cgOpen C U R.g)),
      (Matrix.det (Matrix.of (fun j m => evalSection (coord p m).left
        (coord_landsIn hp m) (s j)))) ≠ 0)
    (hell_bc : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
      (e : F →ₐ[K] F') (D : Dv C F), ell C (SpecLin.DivBase.bc e D) = ell C D) :
    Nonempty (BNData C R) := by
  have hδ : bnDelta C U R.g s ≠ 0 := bnDelta_ne_zero R U s hnonvan
  have hcb : chartOpen C R.g U s (Work.Charts.quotMapIsClosedMap (C := C) R.g) ≠ ⊥ :=
    chartOpen_ne_bot U s (Work.Charts.quotMapIsClosedMap (C := C) R.g) hδ
  have hci : ∀ {F : Type u} [Field F] [Algebra K F] (p : FPt (Sym C R.g) F),
      RPt.LandsIn p (chartOpen C R.g U s (Work.Charts.quotMapIsClosedMap (C := C) R.g)) →
      iOf C R.W (SpecLin.SymGeom.divOf p) = 0 :=
    fun {F} _ _ p hp =>
      iOf_eq_zero_of_landsIn_chartOpen R U s hell_bc
        (fun {F} _ _ p hp => hcrit p hp) (Work.Charts.quotMapIsClosedMap (C := C) R.g) p hp
  set X := (Sym C R.g).left with hX
  set V : X.Opens := chartOpen C R.g U s (Work.Charts.quotMapIsClosedMap (C := C) R.g) with hV
  obtain ⟨x, hxV⟩ : (V : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun hbot => hcb (TopologicalSpace.Opens.ext (by rw [hbot]; rfl))
  obtain ⟨Ω, hΩmem, hxΩ, hΩV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.2
  obtain ⟨i, hi₁, hi₂⟩ := hΩmem
  have hle : i ≤ V := by
    intro y hy
    exact hΩV (hi₂ ▸ hy)
  have hne : i ≠ ⊥ := by
    intro hbot
    have hxbot : x ∈ (i : Set X) := hi₂ ▸ hxΩ
    rw [hbot] at hxbot
    exact hxbot
  refine ⟨BNData.mk Q U hU h h_mem h_span i hi₁ 1 ?_ ?_⟩
  · intro F _ _ p hp
    rw [Scheme.basicOpen_one] at hp
    exact hci p (hle hp)
  · rw [Scheme.basicOpen_one]
    exact hne

end

end Work.BNChart
