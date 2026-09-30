/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR: Riemann–Roch and its first consequences, unconditionally

The finiteness of the genus (`GenusTop.hasFiniteGenus`) makes the Riemann–Roch equation of
`RRMain.lean` unconditional.  This file records the resulting exports:

* `i_sub_i` — the index of speciality drops by `deg(E-D) - (l E - l D)`;
* `riemannRoch` — `l D - i D = deg D + 1 - g`;
* `exists_ne_zero_mem_L` — RR7 of the design: `deg D ≥ g` implies `L(D) ≠ 0`.
-/
import Submission.Work.RiemannRoch.GenusTop
import Submission.Work.RiemannRoch.RRMain
import Submission.Work.RiemannRoch.RR.finite_H1
import Submission.Work.RiemannRoch.RR.i_anti
import Submission.Work.RiemannRoch.RR.i_add_div

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

instance finiteDimensional_H1 (C : Curve k) (D : C.Div) : FiniteDimensional k (H1 C D) :=
  Work.RiemannRoch.RR.finite_H1 C (hasFiniteGenus C) D

/-- The index of speciality drops by `deg(E-D) - (l E - l D)`. -/
theorem i_sub_i (C : Curve k) {D E : C.Div} (h : D ≤ E) :
    (i C D : ℤ) - i C E = (C.deg E - C.l E) - (C.deg D - C.l D) :=
  i_sub_i_of_finiteGenus C (hasFiniteGenus C) h

/-- **Riemann–Roch**. -/
theorem riemannRoch (C : Curve k) (D : C.Div) :
    (C.l D : ℤ) - i C D = C.deg D + 1 - (genus C : ℤ) :=
  riemannRoch_of_finiteGenus C (hasFiniteGenus C) D

/-- The index of speciality is nonnegative: Riemann's inequality. -/
theorem riemann_inequality (C : Curve k) (D : C.Div) :
    (C.deg D : ℤ) + 1 - (genus C : ℤ) ≤ (C.l D : ℤ) := by
  have h := riemannRoch C D
  have h2 : (0 : ℤ) ≤ (i C D : ℤ) := Int.natCast_nonneg _
  linarith

/-- **RR7 of the design**: a divisor of degree at least the genus has a nonzero section. -/
theorem exists_ne_zero_mem_L (C : Curve k) {D : C.Div} (h : (genus C : ℤ) ≤ C.deg D) :
    ∃ f : C.functionField, f ≠ 0 ∧ f ∈ C.L D := by
  have h1 : (1 : ℤ) ≤ (C.l D : ℤ) := by
    have h2 := riemann_inequality C D
    linarith
  have hne : C.L D ≠ ⊥ := by
    intro hbot
    have : C.l D = 0 := by rw [Curve.l, hbot]; simp
    omega
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).mp hne
  exact ⟨f, hf0, hf⟩

end

end Curve

end Work.RiemannRoch
