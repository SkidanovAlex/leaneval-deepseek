/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.TorsorExistence
-/
import Submission.Work.TorsorExistence.existsCyclicExtension_of_zeta5
import Submission.Work.TorsorExistence.existsCyclicExtension_of_charP_five
import Submission.Work.TorsorExistence.existsCyclicExtension_numberField
import Submission.Work.TorsorExistence.nonempty_fiveTorsionPoint

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Step (A) and (B): cyclic quintic extensions and curves with rational `5`-torsion

Aggregation module for the existence statements of the paper's Lemma `lem:torsors`.

## (A) Cyclic quintic extensions of a field `𝕜`

The paper's proof needs, for each field class, *one* cyclic extension of degree `5` of `𝕜`, plus
an elliptic curve over `𝕜` with a rational point of order `5`.  Absent Hilbertianity (which is not
in Mathlib), the extensions come from

* **Kummer theory**, `existsCyclicExtension_of_zeta5`: if `ζ ∈ 𝕜` is a primitive `5`-th root of
  unity (which forces `char 𝕜 ≠ 5`) and `a` is not a fifth power, then a root field of `X⁵ - a`
  is cyclic of degree `5`.  This applies to any function field `𝕜 = 𝔽(X)` in characteristic
  `≠ 5` in which `ζ₅ ∈ 𝔽` (in particular whenever `𝔽` is algebraically closed of characteristic
  `≠ 5`, e.g. class (d)) with `a` the class of a separating transcendental whose class in
  `𝕜^*/𝕜^{*5}` is non-trivial;
* **Artin–Schreier theory**, `existsCyclicExtension_of_charP_five`: in characteristic `5`, if
  `a ∉ ℘(𝕜)` (`℘(x) = x⁵ - x`) then a root field of `X⁵ - X - a` is cyclic of degree `5`.  This
  is the case the paper leaves to the reader; for `𝕜 = 𝔽(X)` with `𝔽` of characteristic `5` and
  `X` of positive dimension one takes `a` the class of a separating transcendental, whose class
  in `𝕜/℘(𝕜)` is non-trivial because `x⁵ - x = t` would force `5·deg x = 1`;
* **cyclotomic fields**, `existsCyclicExtension_numberField`: every number field has one (via
  `ℚ(ζ_{5^k})` for `5 ^ (k-1) > [𝕜 : ℚ]` — no Dirichlet, no Hilbertianity); this is the
  number-field class (a).

**The one field-theoretic gap.**  For the function-field classes (b), (c), (d) the input above
("`ζ₅ ∈ 𝕜` and `a ∉ 𝕜^5`", resp. "`a ∉ ℘(𝕜)`") is satisfied for `𝕜 = X.functionField` with
`0 < topologicalKrullDim X`, but the *proof* that `𝕜` contains a separating transcendental (the
statement `trdeg_𝔽 𝕜 ≥ 1`) is not in Mathlib, and neither is the algebra structure
`Algebra 𝔽 X.functionField` needed even to name `ζ₅ ∈ 𝕜`.  That is a Mathlib gap in the direction
of §2 of `NOTES.md`, not a gap in the mathematics: the claim is Hilbertianity-free and is proved
here in the abstract form above.

## (B) Curves with a rational point of order `5` and `j ≠ 1728`

`nonempty_fiveTorsionPoint` is the Tate normal form for `X₁(5)`:
`E(c) : y² + (1-c)xy - cy = x³ - cx²` with `T = (0,0)` of order `5` for every `c ≠ 0` with
`c² - 11c - 1 ≠ 0`, and `j = 1728` excluded by a monic degree-`12` polynomial condition in `c`;
the Silverman A.1.2 datum is supplied by `Main.nonempty_orderAutCurve`.

See `NOTES.md` §4 for the deviation recorded in the number-field case (the lead's `ℓ ≡ 1 mod 5`
sketch has an insufficient hypothesis) and for the exact status of each statement.
-/
