/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR: the lattices `A(E) + K` and Riemann's inequality

For `E ≥ 0` the image of `A(E)` in `H1 C 0 = A_K/(A(0)+K)` is `(A(E)+K)/(A(0)+K)`, a finite
dimensional space of dimension `deg E - l E + l 0`.  Riemann's inequality bounds this dimension
uniformly, and `GenusTop.lean` uses that bound to prove `A_K = A(E₀) + K`, hence that the genus
is finite.
-/
import Submission.Work.RiemannRoch.Canonical
import Submission.Work.RiemannRoch.RR.finrank_sup_diagK_quot
import Submission.Work.RiemannRoch.Linear.l_zero_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The image of `A(D)` in `H1 C 0 = A/(A(0) + K)`: the classes of `D`-bounded adèles modulo
principal ones. -/
abbrev SEmap (C : Curve k) (D : C.Div) : Submodule k (H1 C 0) :=
  (Asub C D).map (Submodule.mkQ (Asub C 0 ⊔ diagK C))

theorem mem_SEmap {C : Curve k} {D : C.Div} {x : H1 C 0} :
    x ∈ SEmap C D ↔ ∃ a ∈ Asub C D, Submodule.mkQ (Asub C 0 ⊔ diagK C) a = x :=
  Submodule.mem_map

theorem l_zero (C : Curve k) : C.l 0 = 1 := Work.RiemannRoch.Linear.l_zero_eq_one C

theorem SEmap_mono (C : Curve k) {D E : C.Div} (h : D ≤ E) : SEmap C D ≤ SEmap C E :=
  Submodule.map_mono (Asub_mono C h)

/-- `diagK` is contained in `A(0) + K`, so it dies in `H1 C 0`. -/
theorem map_diagK_mkQ_eq_bot (C : Curve k) :
    (diagK C).map (Submodule.mkQ (Asub C 0 ⊔ diagK C)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact (le_sup_right : diagK C ≤ Asub C 0 ⊔ diagK C) hy

theorem map_sup_eq_SEmap (C : Curve k) (E : C.Div) :
    (Asub C E ⊔ diagK C).map (Submodule.mkQ (Asub C 0 ⊔ diagK C)) = SEmap C E := by
  rw [Submodule.map_sup, map_diagK_mkQ_eq_bot, sup_bot_eq]

/-- The image of `A(E)` in `H1 C 0` is finite dimensional, of dimension `deg E - l E + 1`. -/
theorem finrank_SEmap_eq (C : Curve k) {E : C.Div} (hE : 0 ≤ E) :
    (Module.finrank k ↥(SEmap C E) : ℤ) = (C.deg E - C.l E) + 1 := by
  haveI : FiniteDimensional k
      (relQuot (Asub C 0 ⊔ diagK C) (Asub C E ⊔ diagK C)) :=
    (Work.RiemannRoch.RR.finrank_sup_diagK_quot C (D := 0) (E := E) hE).1
  have h1 : Module.finrank k ↥(SEmap C E) =
      Module.finrank k (relQuot (Asub C 0 ⊔ diagK C) (Asub C E ⊔ diagK C)) := by
    rw [← map_sup_eq_SEmap C E]
    exact (LinearEquiv.finrank_eq
      (relQuotEquivMap (Asub C 0 ⊔ diagK C) (Asub C E ⊔ diagK C))).symm
  have h2 := (Work.RiemannRoch.RR.finrank_sup_diagK_quot C (D := 0) (E := E) hE).2
  rw [h1, h2, Curve.deg_zero, l_zero]
  ring

theorem finite_SEmap (C : Curve k) {E : C.Div} (hE : 0 ≤ E) :
    FiniteDimensional k ↥(SEmap C E) := by
  haveI : FiniteDimensional k
      (relQuot (Asub C 0 ⊔ diagK C) (Asub C E ⊔ diagK C)) :=
    (Work.RiemannRoch.RR.finrank_sup_diagK_quot C (D := 0) (E := E) hE).1
  rw [← map_sup_eq_SEmap C E]
  exact (relQuotEquivMap (Asub C 0 ⊔ diagK C) (Asub C E ⊔ diagK C)).finiteDimensional

/-- Riemann's inequality, in the form used for the finiteness of the genus: the dimension of the
image of `A(E)` in `H1 C 0` is bounded by `γ + 1`. -/
theorem finrank_SEmap_le (C : Curve k) {γ : ℤ}
    (hγ : ∀ D : C.Div, C.deg D - C.l D ≤ γ) {E : C.Div} (hE : 0 ≤ E) :
    Module.finrank k ↥(SEmap C E) ≤ (γ + 1).toNat := by
  have h1 : (Module.finrank k ↥(SEmap C E) : ℤ) = (C.deg E - C.l E) + 1 :=
    finrank_SEmap_eq C hE
  have h2 : ((Module.finrank k ↥(SEmap C E) : ℤ)).toNat ≤ (γ + 1).toNat := by
    refine Int.toNat_le_toNat ?_
    rw [h1]
    linarith [hγ E]
  simpa using h2

end

end Curve

end Work.RiemannRoch
