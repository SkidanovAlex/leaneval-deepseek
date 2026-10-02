/-
Copyright: subproject `Submission/Work/FatouDeg/` of `mandelbar_not_path_connected`.

# `Work.FatouDeg` — the degenerate half of Fatou's theorem

The deliverable of the area: the degenerate case of Fatou's theorem on parabolic cycles, hence
(with the already-proved simple case) the whole classical input
`Work.FatouParabolic.FatouParabolicInput`.

`Work.FatouDeg.fatouParabolicInput_degenerate` is *literally* the proposition
`Work.FatouParabolic2.FatouParabolicInput_degenerate`, so it can be used as the `hDeg` argument of
`Work.FatouParabolic2.fatouParabolicInput_split` and of every consumer of the degenerate input
(`Work.MandelFinal.finalInputs_of`, `Work.FatouParabolic2.mem_Mandelbar_of_parabolic_returnMap`,
`Work.FatouParabolic2.parabolicCycleInOmegaLimit_of_degenerate`,
`Work.FatouParabolic2.quarterParabolicIsFixed_of_degenerate`).
-/
import Mathlib
import Submission.Work.FatouParabolic2.Defs
import Submission.Work.FatouParabolic2.fatouParabolicInput_simple
import Submission.Work.FatouDeg.Degenerate
import Submission.Work.FatouDeg.normalizeDeg
import Submission.Work.FatouDeg.NormForm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg

noncomputable section

/-- **The degenerate case of Fatou's theorem**: for a polynomial map `F` of degree `≥ 2` with a
fixed point `z₀` of multiplier `1` at which the second derivative vanishes, the basin of `z₀`
contains a critical point of `F`. -/
theorem fatouParabolicInput_degenerate : Work.FatouParabolic2.FatouParabolicInput_degenerate :=
  fatouParabolicInput_degenerate_of fun F z₀ hF hfix h1 h2 => normalizeDeg F z₀ hF hfix h1 h2

/-- **Fatou's theorem on parabolic cycles** (the classical input of the tricorn project), obtained
by splitting into the simple case (`Work.FatouParabolic2.fatouParabolicInput_simple`) and the
degenerate case proved in this area. -/
theorem fatouParabolicInput : Work.FatouParabolic.FatouParabolicInput :=
  Work.FatouParabolic2.fatouParabolicInput_split Work.FatouParabolic2.fatouParabolicInput_simple
    fatouParabolicInput_degenerate

end

end Work.FatouDeg
