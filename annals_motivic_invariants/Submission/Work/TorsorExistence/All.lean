/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TorsorExistence
-/
import Submission.Work.TorsorExistence.Main
import Submission.Work.TorsorExistence.Extensions
import Submission.Work.TorsorExistence.Twist
import Submission.Work.TorsorExistence.five_smul_cls
import Submission.Work.TorsorExistence.cls_eq_zero_iff
import Submission.Work.TorsorExistence.period_toTorsor_eq_five_iff
import Submission.Work.TorsorExistence.toTorsor_pointless

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.TorsorExistence` — single entry point

The area `Submission/Work/TorsorExistence` builds the arithmetic side of the paper's Lemma
`lem:torsors` for the four field classes of Lin–Shinder, *Motivic invariants of birational maps*,
Annals of Math. 199 (1), 2024, Theorem 1.2 (1) (a)–(d), and isolates what remains of the
geometry.

## Import this

`import Submission.Work.TorsorExistence.All`

## The main results

**The target (`Work.Arithmetic.HasLLinkCurve 𝕜`), reduced to one geometric residual:**

* `Work.TorsorExistence.PointlessIndexFiveCurve 𝕜` — the residual (`Defs.lean`): a smooth,
  proper, geometrically integral curve of dimension `1` over `𝕜`, with no `𝕜`-point, carrying a
  `𝕜`-rational divisor of degree `5`, and with every rational divisor degree divisible by `5`;
* `Work.TorsorExistence.HasPointlessIndexFiveCurve 𝕜` — the same in `Prop` form;
* `Work.Arithmetic.HasLLinkCurve 𝕜 ← HasPointlessIndexFiveCurve 𝕜`:
  `Work.TorsorExistence.hasLLinkCurve_of_hasPointlessIndexFiveCurve` (and the sharper
  `hasLLinkCurve_of_indexFive`, which takes the elliptic curve as a parameter);
* the converse `hasPointlessIndexFiveCurve_of_period_five`, so `HasLLinkCurve 𝕜` and
  `HasPointlessIndexFiveCurve 𝕜` are inter-derivable;
* the four field classes (`Main.lean`):
  `hasLLinkCurve_numberField`, `hasLLinkCurve_functionField_numberField`,
  `hasLLinkCurve_functionField_finite`, `hasLLinkCurve_functionField_algClosed`.

**The paper's proof of `lem:torsors`, step (A): cyclic quintic extensions** (`Defs.lean`,
`Extensions.lean`):

* `Work.TorsorExistence.CyclicExtension` / `ExistsCyclicExtension`;
* `existsCyclicExtension_of_zeta5` — Kummer theory in characteristic `≠ 5`;
* `existsCyclicExtension_of_charP_five` — Artin–Schreier theory in characteristic `5`;
* `existsCyclicExtension_numberField` — number fields, from `ℚ(ζ_{5^k})`.

**Step (B): a curve with a rational `5`-torsion point and `j ≠ 1728`:**

* `FiveTorsionPoint` / `FiveTorsionCurve` and `nonempty_fiveTorsionPoint` — the Tate normal form
  for `X₁(5)`: `E(c) : y² + (1-c)xy - cy = x³ - cx²` with `T = (0,0)` of order `5`;
* `OrderAutCurve`, `nonempty_orderAutCurve` and its three characteristic cases — Silverman,
  *AEC*, A.1.2 as data.

**Steps (C), (D): the quintic twist** (`Twist.lean` and siblings):

* `QuinticTwist.LPoints`, `galMap`, `norm`, `shift`, `cocycles`, `coboundaries`, `H1` — the
  Galois cohomology group `H¹(ℤ/5, E(L)) = ker N / (σ - 1)E(L)`;
* `QuinticTwist.cls`, `five_smul_cls`, `cls_eq_zero_iff`, `Pointless`;
* `QuinticTwist.toTorsor`, `period_toTorsor_eq_five_iff`, `toTorsor_pointless` — the bridge to
  `Work.Arithmetic.Torsor`.

See `NOTES.md` for what is proved, what is a named residual, and why.
-/
