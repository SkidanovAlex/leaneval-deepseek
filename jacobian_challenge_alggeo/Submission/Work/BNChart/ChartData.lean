/-
Copyright (c) 2026 The Jacobian challenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: area BNChart (Submission/Work/NOTES_LEAD_jacobian_closure.md §2.B4)

# Area BNChart — the book-keeping data of the Brill–Noether chart

`Work.Charts.BNData` carries, besides the chart itself, a family `h : Fin R.g → K(C)` of
rational functions with `h_mem` (`h j ∈ L (W)`) and `h_span` (`L W = span_K (range h)`).  These
two fields are never used by the construction (nor by any consumer on disk); this file simply
provides them for the concrete `R = rochDataPos C h`, as the basis of `(C_K).L (rochW C)`
produced by `Module.finBasisOfFinrankEq` from `ℓ(W) = g`.
-/
import Submission.Work.BNChart.Chart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open scoped Work.GCBasics

namespace Work.BNChart

open Work.CurveBasics Work.GCBasics Work.Charts

noncomputable section

variable {K : Type u} [Field K]

/-- **A `K`-basis of the Riemann–Roch space `(C_K).L (rochW C)` of the canonical divisor over
the base field**, indexed by the successor shape `chartIdx C`.

Since `rochW C` is the pullback of a canonical divisor, `ℓ (rochW C) = genus C`, so
`(genus C - 1) + 1 = genus C` (for `genus C ≠ 0`) is the dimension of this space. -/
noncomputable def chartH (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0) :
    Module.Basis (chartIdx C) K ((C.baseChange K).L (rochW C)) :=
  Module.finBasisOfFinrankEq K _
    (by
      haveI : Module.Finite K ((C.baseChange K).L (rochW C)) :=
        Work.CurveBasics.Linear.finiteDimensional_L (C.baseChange K) _
      have h1 : Module.finrank K ((C.baseChange K).L (rochW C))
          = RiemannRoch.Curve.genus C := by
        rw [show Module.finrank K ((C.baseChange K).L (rochW C))
              = (C.baseChange K).l (rochW C) from rfl,
          rochW, Curve.BCSquare.l_divMap]
        exact (RiemannRoch.Curve.isCanonical_canonical C).l_eq
      rw [h1]
      have := Nat.pos_of_ne_zero h
      omega)

/-- The elements of `chartH` lie in the Riemann–Roch space (the `h_mem` field of `BNData`). -/
theorem chartH_mem (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0) (j : chartIdx C) :
    0 ≤ (C.baseChange K).div ((chartH C h j : (C.baseChange K).L (rochW C))
      : (C.baseChange K).functionField) + rochW C := by
  have hmem : ((chartH C h j : (C.baseChange K).L (rochW C)) : (C.baseChange K).functionField)
      ∈ (C.baseChange K).L (rochW C) := (chartH C h j).2
  rw [Curve.mem_L_iff] at hmem
  have hne : ((chartH C h j : (C.baseChange K).L (rochW C))
      : (C.baseChange K).functionField) ≠ 0 := by
    intro h0
    exact (chartH C h).ne_zero j (Subtype.ext (by simpa using h0))
  exact hmem.resolve_left hne

/-- The elements of `chartH` span the Riemann–Roch space (the `h_span` field of `BNData`). -/
theorem span_chartH (C : Curve K) (h : RiemannRoch.Curve.genus C ≠ 0) :
    (C.baseChange K).L (rochW C)
      = Submodule.span K (Set.range (fun j : chartIdx C =>
          ((chartH C h j : (C.baseChange K).L (rochW C))
            : (C.baseChange K).functionField))) := by
  have h2 : Submodule.span K (Set.range (fun j : chartIdx C =>
      ((chartH C h j : (C.baseChange K).L (rochW C)) : (C.baseChange K).functionField)))
      = (C.baseChange K).L (rochW C) :=
    (Submodule.span_range_subtype_eq_top_iff ((C.baseChange K).L (rochW C))
      (s := fun j : chartIdx C => ((chartH C h j : (C.baseChange K).L (rochW C))
        : (C.baseChange K).functionField))
      (fun j => (chartH C h j).2)).mp (chartH C h).span_eq
  exact h2.symm

end

end Work.BNChart
