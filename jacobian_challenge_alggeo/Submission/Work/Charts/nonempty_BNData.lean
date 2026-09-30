/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — **the Brill–Noether chart exists**

This file builds an inhabitant of `Work.Charts.BNData C R` — the chart of the Jacobian drive —
following §3.5 of `NOTES_LEAD_jacobian_GC.md` and `ChartCg.lean`: the Brill–Noether determinant
`δ = det (s_j(x_m))²` on the product `C^g`, its non-vanishing locus `bnOpen`, and the chart
`chartOpen = (quotMap '' (bnOpen)ᶜ)ᶜ` of `Sym^g C`; an affine open `Ω ⊆ chartOpen` and the unit
section `1 ∈ Γ(Sym^g C, Ω)` then give

  `chart := Ω`,  `δ := 1`,  `V = D(1) = Ω`,

which is affine, nonempty, and on whose points `i (divOf p) = 0`.

The two mathematical inputs (see `NOTES.md` §0octies) are

* `hcrit` — **the Brill–Noether determinant criterion**: for every field `F ⊇ K` and every
  `F`-point `p` of `C^g` landing in `U^g`, the determinant of the evaluation matrix
  `(s_j(x_m))` is invertible exactly when the degree-`g` divisor `divOf (quotMap p)` is
  non-special.  This is the content of "the sections `s` are the restrictions of a basis of
  `L(W)` and evaluation commutes with base change of the field"; it follows from the
  compatibility `L(W)_{F} = L(W_F)` (the standard fact behind
  `Work.CurveBasics.Curve.divMap_div`), which `Work.SpecLin.DivBase` does not yet axiomatise;
* `hnonspec` — **RR6 with support in `U`**: some split degree-`g` divisor supported in `U` is
  non-special.  This is `Work.Charts.exists_nonspecial_support` (proved), read through the same
  interface identification.

The non-vanishing locus of `δ` is nonempty by `hnonspec` and `hcrit`, and `ℓ = 1` on
`chartOpen` by `hcrit` and the invariance `ell_bc` of `ℓ` under field extension.
-/
import Submission.Work.Charts.Step3Defs
import Submission.Work.Charts.isProper_quotMap
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

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-- The quotient map `C^n ⟶ Sym^n C` is a closed map (it is proper, and proper morphisms are
universally closed).  This is the `hclosed` argument of `Work.Charts.chartOpen`. -/
theorem quotMapIsClosedMap {C : Curve K} (n : ℕ) [Work.SpecLin.DivBase C]
    [Work.SpecLin.SymGeom C n] : IsClosedMap (quotMap C n).left.base := by
  haveI := (isProper_quotMap (C := C) n).toUniversallyClosed
  exact Scheme.Hom.isClosedMap (quotMap C n).left

/-- **The Brill–Noether chart exists.**  Given the chart data of §3.5 — a place `Q`, the affine
open `U` of the curve over which the sections of `L(W)` are regular, the sections
`s : Fin g → Γ(C,U)` cut out by a basis of `L(W)` — together with the determinant criterion
`hcrit`, the existence of a non-special split divisor supported in `U` (`hnonspec`, RR6) and the
invariance `ell_bc` of `ℓ` under base change of the field, there is a Brill–Noether chart
`BNData C R`: an affine open `V ⊆ Sym^g C`, nonempty, on whose points `ℓ = 1`. -/
theorem nonempty_BNData_of_basis {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
    [Work.SpecLin.SymGeom C R.g] (U : C.left.Opens) (hU : IsAffineOpen U) (Q : C.Place)
    (h : Fin R.g → (C.baseChange K).functionField)
    (h_mem : ∀ j, 0 ≤ (C.baseChange K).div (h j) + R.W)
    (h_span : (C.baseChange K).L R.W = Submodule.span K (Set.range h))
    (s : Fin R.g → (C.left.presheaf.obj (Opposite.op U)))
    (hcrit : ∀ {F : Type u} [Field F] [Algebra K F]
      (p : FPt (Cprod C R.g) F) (hp : RPt.LandsIn p (cgOpen C U R.g)),
      (Matrix.det (Matrix.of (fun j m => evalSection (coord p m).left
        (coord_landsIn hp m) (s j)))) ≠ 0 ↔
        iOf C R.W (Work.SpecLin.SymGeom.divOf (ptComp p (quotMap C R.g))) = 0)
    (hnonspec : ∃ (F : Type u) (_ : Field F) (_ : Algebra K F)
      (p : FPt (Cprod C R.g) F) (hp : RPt.LandsIn p (cgOpen C U R.g)),
      iOf C R.W (Work.SpecLin.SymGeom.divOf (ptComp p (quotMap C R.g))) = 0)
    (hell_bc : ∀ {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
      (e : F →ₐ[K] F') (D : Dv C F), ell C (Work.SpecLin.DivBase.bc e D) = ell C D) :
    Nonempty (BNData C R) := by
  have hnonvan : ∃ (F : Type u) (_ : Field F) (_ : Algebra K F)
      (p : FPt (Cprod C R.g) F) (hp : RPt.LandsIn p (cgOpen C U R.g)),
      (Matrix.det (Matrix.of (fun j m => evalSection (coord p m).left
        (coord_landsIn hp m) (s j)))) ≠ 0 := by
    obtain ⟨F, hF, hAlg, p, hp, h0⟩ := hnonspec
    exact ⟨F, hF, hAlg, p, hp, hcrit p hp |>.mpr h0⟩
  have hδ : bnDelta C U R.g s ≠ 0 := bnDelta_ne_zero R U s hnonvan
  have hcb : chartOpen C R.g U s (quotMapIsClosedMap (C := C) R.g) ≠ ⊥ :=
    chartOpen_ne_bot U s (quotMapIsClosedMap (C := C) R.g) hδ
  have hci : ∀ {F : Type u} [Field F] [Algebra K F] (p : FPt (Sym C R.g) F),
      RPt.LandsIn p (chartOpen C R.g U s (quotMapIsClosedMap (C := C) R.g)) →
      iOf C R.W (Work.SpecLin.SymGeom.divOf p) = 0 :=
    fun {F} _ _ p hp =>
      iOf_eq_zero_of_landsIn_chartOpen R U s hell_bc
        (fun {F} _ _ p hp => (hcrit p hp).mp) (quotMapIsClosedMap (C := C) R.g) p hp
  set X := (Sym C R.g).left with hX
  set V : X.Opens := chartOpen C R.g U s (quotMapIsClosedMap (C := C) R.g) with hV
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

end Work.Charts
