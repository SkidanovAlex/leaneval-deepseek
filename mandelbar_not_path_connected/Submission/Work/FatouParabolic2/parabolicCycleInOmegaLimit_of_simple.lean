/-
Copyright: subproject `Submission/Work/FatouParabolic2/` of `mandelbar_not_path_connected`.

# `ParabolicCycleInOmegaLimit` from the simple case of Fatou's input

The ledger statement `Work.LANDCL.ParabolicCycleInOmegaLimit c` (every parabolic point of `T_c`
lies in the closure of the critical orbit) is proved in the area
`Submission/Work/FatouParabolic/` from the classical input `Work.FatouParabolic.FatouParabolicInput`
(the basin of a multiplier-one fixed point of a polynomial of degree `≥ 2` contains a critical
point).  Here it is re-derived from the **simple** version of that input,

`Work.FatouParabolic2.fatouParabolicInput_simple : FatouParabolicInput_simple`

(proved in this area for `iteratedDeriv 2 F z₀ ≠ 0`), in two forms:

* `parabolicCycleInOmegaLimit_of_simple` — under the hypothesis `ParabolicCyclesSimple c` that
  every parabolic point of `T_c` is a *simple* parabolic point of its holomorphic return map;
* `parabolicCycleInOmegaLimit_of_degenerate` — under the degenerate case
  `FatouParabolicInput_degenerate` of the classical input only.  This is the strictly weakest
  hypothesis: no simplicity is assumed, because `fatouParabolicInput_simple` is unconditional.
-/
import Mathlib
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.FatouParabolic2.fatouParabolicInput_simple
import Submission.Work.FatouParabolic2.parabolicCycleInOmegaLimit_pointwise
import Submission.Work.FatouParabolic.Reduction

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology
open Filter Set

namespace Work.FatouParabolic2

noncomputable section

/-- **`ParabolicCycleInOmegaLimit` from the simple case of the input.**  If every parabolic point
of `T_c` is a simple parabolic point of its holomorphic return map
(`Work.FatouParabolic2.ParabolicCyclesSimple c`), then the simple input alone puts every parabolic
point of `T_c` in the closure of the critical orbit. -/
theorem parabolicCycleInOmegaLimit_of_simple (hFatou : FatouParabolicInput_simple) (c : ℂ)
    (hsimple : ParabolicCyclesSimple c) : Work.LANDCL.ParabolicCycleInOmegaLimit c := by
  intro z hz
  obtain ⟨m, hzm⟩ := hz
  exact parabolicCycleInOmegaLimit_pointwise hFatou hzm (hsimple z m hzm)

/-- **`ParabolicCycleInOmegaLimit` from the degenerate case of the input only.**  The simple case
of the classical input is proved (`Work.FatouParabolic2.fatouParabolicInput_simple`), so the whole
ledger statement follows from the degenerate case alone.  This is the form to use: the hypothesis
is strictly weaker than `Work.FatouParabolic.FatouParabolicInput`, and no statement about the
simplicity of the parabolic points of `T_c` has to be discharged. -/
theorem parabolicCycleInOmegaLimit_of_degenerate (hDeg : FatouParabolicInput_degenerate) (c : ℂ) :
    Work.LANDCL.ParabolicCycleInOmegaLimit c :=
  Work.FatouParabolic.parabolicCycleInOmegaLimit
    (fatouParabolicInput_split fatouParabolicInput_simple hDeg) c

/-- **`ParabolicCycleInOmegaLimit` from the simple case of the input, in the weakest
"simplicity" form.**  Here one only has to exhibit, for every parabolic point `z` of `T_c`,
*some* period `m` with `Work.Landing.IsParabolic c m z` at which the holomorphic return map
`(Tsq c)^[m]` is simple; the conclusion `z ∈ closure (range (n ↦ (T_c)^[n] c))` does not refer to
that period.

At the root-parabolic parameter this is what `Work.EL.RootParabolic.simple` (simplicity of the
period-`5` return map at the characteristic point `z₁`) provides for every point of the period-`5`
cycle, once the points of the cycle are known to be conjugate along the *holomorphic* map
`Tsq c` (which permutes them with `Tsq c` acting as `j ↦ j + 2` on `ℤ/5`). -/
theorem parabolicCycleInOmegaLimit_of_exists_simple (hFatou : FatouParabolicInput_simple) (c : ℂ)
    (h : ∀ z : ℂ, (∃ m : ℕ, Work.Landing.IsParabolic c m z) →
      ∃ m : ℕ, Work.Landing.IsParabolic c m z ∧
        iteratedDeriv 2 ((Work.Landing.Tsq c)^[m]) z ≠ 0) :
    Work.LANDCL.ParabolicCycleInOmegaLimit c := by
  intro z hz
  obtain ⟨m, hzm, hsimp⟩ := h z hz
  exact parabolicCycleInOmegaLimit_pointwise hFatou hzm hsimp


end

end Work.FatouParabolic2
