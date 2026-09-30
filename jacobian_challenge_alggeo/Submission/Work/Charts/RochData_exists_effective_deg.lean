/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# RR7 with the degree preserved (the form used by area `GC`)

For a divisor `D` of degree at least the genus there is an **effective** representative
`E ~ D` of the *same degree*: take `h ≠ 0` in `L(D)` (RR7) and set `E := div h + D`; then `E`
is effective, `E ~ D` (witness `h⁻¹`), and `deg E = deg D` because `deg (div h) = 0`
(area CB, `Curve.deg_div`).

This is the field `rr7` of the chart datum `Work.GroupChunk.Input` of area `GC`, derived here
from `Work.Charts.RochData` (RR5 + the Riemann–Roch equation + RR7).
-/
import Submission.Work.Charts.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry
open scoped Classical MonoidalCategory

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K]

/-- **RR7 with the degree preserved.**  For `D` of degree at least the genus there is an
effective `E`, linearly equivalent to `D`, with `deg E = deg D`. -/
theorem RochData_exists_effective_deg {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
    {F : Type u} [Field F] [Algebra K F] (D : Dv C F) (h : (R.g : ℤ) ≤ Ddeg C F D) :
    ∃ E : Dv C F, E.IsEffective ∧ Ddeg C F E = Ddeg C F D ∧ LinEquiv C D E := by
  have h1 : 1 ≤ ell C D := R.ell_pos_of_genus_le_deg D h
  have hne : (C.baseChange F).L D ≠ ⊥ := by
    intro hbot
    have h0 : ell C D = 0 := by rw [ell, hbot, finrank_bot]
    omega
  obtain ⟨f, hf, hf0⟩ := Submodule.ne_bot_iff _ |>.mp hne
  have heff : ((C.baseChange F).div f + D).IsEffective :=
    ((Curve.mem_L_iff (C.baseChange F)).mp hf).resolve_left hf0
  have hdeg : Ddeg C F ((C.baseChange F).div f) = 0 :=
    Work.CurveBasics.Order.deg_div (C.baseChange F) f
  refine ⟨(C.baseChange F).div f + D, heff, ?_, ?_⟩
  · rw [Ddeg_add, hdeg, zero_add]
  · exact ⟨f⁻¹, inv_ne_zero hf0,
      by rw [Work.CurveBasics.Order.div_inv (C.baseChange F) hf0]; abel⟩

end

end Work.Charts
