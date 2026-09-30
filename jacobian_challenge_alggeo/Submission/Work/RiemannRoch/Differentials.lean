/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR, layer 4: Weil differentials

Following Serre, *Algebraic Groups and Class Fields*, II §8, a Weil differential on a curve is
a `k`-linear functional on the adèle space that vanishes on the diagonal copy of `K` and on
some `A(D)`.  In this file we record the basic definitions of that theory:

* `WD C D` — the space of functionals vanishing on `K + A(D)`, i.e. `(A/(K+A(D)))^∨`;
* `WDequiv C D` — the canonical linear equivalence `Dual (H1 C D) ≃ WD C D`;
* `Omega C` — the space of all Weil differentials, `⋃_D WD C D`;
* `smulW C f ω` — the `K`-action `(f ω)(a) = ω(f a)`.

The main theorems (`finrank_WD`, `deg_le_of_mem_WD`, `exists_smulW_eq` expressing
`dim_K Ω = 1`, `exists_divW`, and the resulting duality `i D = l (W - D)` for a canonical
divisor `W`) are proved in `RiemannRoch/Duality.lean`.
-/
import Submission.Work.RiemannRoch.AdeleOps

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

/-- The space `WD D` of `k`-linear functionals on the adèles vanishing on `K + A(D)`; by
duality it is the dual of `H1 C D = A/(K + A(D))`. -/
abbrev WD (C : Curve k) (D : C.Div) : Submodule k (Module.Dual k (Adeles C)) :=
  (Asub C D ⊔ diagK C).dualAnnihilator

theorem mem_WD_iff {C : Curve k} {D : C.Div} {ω : Module.Dual k (Adeles C)} :
    ω ∈ WD C D ↔ ∀ a ∈ Asub C D ⊔ diagK C, ω a = 0 := by
  rw [WD, Submodule.mem_dualAnnihilator]

/-- The canonical identification of `WD D` with the dual of the quotient `H1 C D`. -/
def WDequiv (C : Curve k) (D : C.Div) :
    Module.Dual k (H1 C D) ≃ₗ[k] WD C D :=
  Submodule.dualQuotEquivDualAnnihilator (Asub C D ⊔ diagK C)

/-- A Weil differential on a curve. -/
abbrev WeilDifferential (C : Curve k) : Type u := Module.Dual k (Adeles C)

/-- The space `Ω` of all Weil differentials: those vanishing on `K + A(D)` for some `D`. -/
def Omega (C : Curve k) : Submodule k (WeilDifferential C) := ⨆ D : C.Div, WD C D

theorem WD_anti (C : Curve k) {D E : C.Div} (h : D ≤ E) : WD C E ≤ WD C D := by
  intro ω hω
  rw [mem_WD_iff] at hω ⊢
  intro a ha
  exact hω a (sup_le_sup_right (Asub_mono C h) (diagK C) ha)

theorem mem_Omega_iff {C : Curve k} {ω : WeilDifferential C} :
    ω ∈ Omega C ↔ ∃ D : C.Div, ω ∈ WD C D := by
  unfold Omega
  refine Submodule.mem_iSup_of_directed _ ?_ 
  intro D E
  exact ⟨D ⊓ E, WD_anti C inf_le_left, WD_anti C inf_le_right⟩

theorem le_Omega (C : Curve k) (D : C.Div) : WD C D ≤ Omega C := le_iSup (fun D => WD C D) D

/-- The `K`-action on Weil differentials: `(f ω)(a) = ω(f a)`. -/
def smulW (C : Curve k) (f : C.functionField) (ω : WeilDifferential C) :
    WeilDifferential C :=
  ω.comp (mulAdele C f)

theorem smulW_apply (C : Curve k) (f : C.functionField) (ω : WeilDifferential C)
    (a : Adeles C) : smulW C f ω a = ω (mulAdele C f a) := rfl

theorem smulW_smul (C : Curve k) (f g : C.functionField) (ω : WeilDifferential C) :
    smulW C f (smulW C g ω) = smulW C (f * g) ω := by
  ext a
  simp only [smulW_apply, mulAdele_mul_apply, mul_comm]

theorem smulW_one (C : Curve k) (ω : WeilDifferential C) :
    smulW C 1 ω = ω := by
  ext a
  simp only [smulW_apply, mulAdele_one, LinearMap.id_apply]

end

end Curve

end Work.RiemannRoch
