import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Green function commutes with the tricorn map up to the factor `2`

`G_c (T_c z) = 2 * G_c z`, the dynamical compatibility of the Green function of the
antiholomorphic unicritical family `T_c(z) = z̄^2 + c` with the map itself.

The mathematical content is the elementary identity
`greenIter (T_c) 2 (T_c z) n = 2 * greenIter (T_c) 2 z (n+1)` for the partial Green
functions, together with the fact that `green c` is the genuine limit of the partial
Green functions (`Work.Escape.tendsto_greenIter`).
-/

open Filter Function
open scoped Topology

namespace Work.Bottcher.Green

open LeanEval.ComplexAnalysis (Tantibar)

/-- If a real sequence converges, then its `limUnder` (with the ambient `Nonempty` instance)
is its limit.  Used to replace `limUnder` by an honest limit. -/
theorem limUnder_eq_of_tendsto {u : ℕ → ℝ} {L : ℝ}
    (h : Filter.Tendsto u Filter.atTop (nhds L)) : Filter.limUnder Filter.atTop u = L := by
  simpa using h.limUnder_eq

/-- The partial Green functions of `z` and of `T_c z` differ by the factor `2` and a shift of
the index: `greenIter (T_c) 2 (T_c z) n = 2 * greenIter (T_c) 2 z (n+1)`. -/
theorem greenIter_Tantibar_shift (c z : ℂ) (n : ℕ) :
    Work.Escape.greenIter (Tantibar c) 2 (Tantibar c z) n
      = 2 * Work.Escape.greenIter (Tantibar c) 2 z (n + 1) := by
  rw [Work.Escape.greenIter_def, Work.Escape.greenIter_def, Function.iterate_succ_apply, pow_succ]
  ring_nf

/-- **Key step.**  If `green c z` is the genuine limit of the partial Green functions of `z`,
then the Green function commutes with `T_c` up to the factor `2`. -/
theorem green_comm_of_tendsto (c z : ℂ)
    (h : Filter.Tendsto (Work.Escape.greenIter (Tantibar c) 2 z) Filter.atTop
      (nhds (Work.Bottcher.green c z))) :
    Work.Bottcher.green c (Tantibar c z) = 2 * Work.Bottcher.green c z := by
  have hshift : Filter.Tendsto (fun n : ℕ => Work.Escape.greenIter (Tantibar c) 2 z (n + 1))
      Filter.atTop (nhds (Work.Bottcher.green c z)) :=
    (tendsto_add_atTop_iff_nat 1).mpr h
  have hmul : Filter.Tendsto
      (fun n : ℕ => 2 * Work.Escape.greenIter (Tantibar c) 2 z (n + 1))
      Filter.atTop (nhds (2 * Work.Bottcher.green c z)) := hshift.const_mul 2
  have hfun : (fun n : ℕ => Work.Escape.greenIter (Tantibar c) 2 (Tantibar c z) n)
      = fun n : ℕ => 2 * Work.Escape.greenIter (Tantibar c) 2 z (n + 1) :=
    funext (greenIter_Tantibar_shift c z)
  calc Work.Bottcher.green c (Tantibar c z)
      = Filter.limUnder Filter.atTop
          (fun n : ℕ => Work.Escape.greenIter (Tantibar c) 2 (Tantibar c z) n) := rfl
    _ = Filter.limUnder Filter.atTop
          (fun n : ℕ => 2 * Work.Escape.greenIter (Tantibar c) 2 z (n + 1)) := by rw [hfun]
    _ = 2 * Work.Bottcher.green c z := limUnder_eq_of_tendsto hmul

/-- **The Green function of the tricorn commutes with the map, up to the factor `2`.**

This is the dynamical equation `G_c ∘ T_c = 2 G_c` of the Green function of the tricorn.
It follows from the elementary shift identity `greenIter_Tantibar_shift` for the partial Green
functions together with the fact that the partial Green functions genuinely converge to the
Green function (`Work.Escape.tendsto_greenIter`). -/
theorem green_comm (c z : ℂ) :
    Work.Bottcher.green c (LeanEval.ComplexAnalysis.Tantibar c z) = 2 * Work.Bottcher.green c z :=
  green_comm_of_tendsto c z
    (Work.Escape.tendsto_greenIter (Tantibar c) 2 ‖c‖ (Work.Escape.monicGrowth_Tantibar c) le_rfl z)

end Work.Bottcher.Green
