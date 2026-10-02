/-
Copyright: subproject `Submission/Work/FatouDeg/` of `mandelbar_not_path_connected`.

# `Work.FatouDeg` — the degenerate half of Fatou's theorem

One-stop import of the area.  Everything the tricorn project needs about the degenerate case of
Fatou's theorem on parabolic cycles:

## The deliverable

* `Work.FatouDeg.fatouParabolicInput_degenerate : Work.FatouParabolic2.FatouParabolicInput_degenerate`
  — for a polynomial map `F` of degree `≥ 2` with `F z₀ = z₀`, `deriv F z₀ = 1` and
  `iteratedDeriv 2 F z₀ = 0`, some critical point of `F` lies in the basin of `z₀`;
* `Work.FatouDeg.fatouParabolicInput : Work.FatouParabolic.FatouParabolicInput` — the same without
  the hypothesis on the second derivative, via
  `Work.FatouParabolic2.fatouParabolicInput_split`.

## The ingredients

* `Work.FatouDeg.Petal.fatouCoordSec3` — the multi-petal Leau--Fatou theory
  (`Submission/Work/MultiPetal/` ported to `m ≥ 3`): for
  `N_{m,G}(z) = z - z^m + z^(m+1) G(z)` with `3 ≤ m` and any `δ > 0` there is an open, nonempty
  petal `Pa ⊆ ball 0 δ` avoiding `0`, inside the sector `0 < Re z`, `m|Im z| < Re z`, forward
  invariant, with orbits converging to `0`, carrying an injective holomorphic Fatou coordinate
  `φa` with `φa (N z) = φa z + 1` whose image contains the tail of every horizontal strip;
* `Work.FatouDeg.normalizeDeg` — the normal form at a parabolic fixed point with vanishing second
  derivative, in the chart `z = z₀ + c w`, without any third-derivative hypothesis;
* `Work.FatouDeg.nf_isPoly`, `Work.FatouDeg.nf_zero`, `Work.FatouDeg.nf_deriv_zero` — the normal
  form is a polynomial map of degree `≥ 2` with `N 0 = 0` and `deriv N 0 = 1`;
* `Work.FatouDeg.fatouParabolicInput_degenerate_of` — the assembly from the normal-form input
  (`Work.FatouDeg.NormalFormInput`) and the Liouville step
  `Work.MultiPetal.criticalOrbitInPetalNoPre`.
-/
import Submission.Work.FatouDeg.Petal.All
import Submission.Work.FatouDeg.NormForm
import Submission.Work.FatouDeg.normalizeDeg
import Submission.Work.FatouDeg.Degenerate
import Submission.Work.FatouDeg.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

