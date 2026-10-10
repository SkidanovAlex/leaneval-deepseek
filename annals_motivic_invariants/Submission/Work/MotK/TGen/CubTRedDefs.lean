/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TGen.CensusFactors

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.cubTRed` — the cubic `cubT` in explicit normal form

`cubT a b h = kleinTwBilin p (kleinTwR (chart3))` is the cubic defining the "cone" (junk) divisor
of the target side of the `T`-twisted Crauder–Katz link.  This file records its explicit form

  `cubT a b h = C (a·b·h) · cubTRed a b h`

where

```
cubTRed a b h = a²b²h·x₀³ - 2a³bh·x₀²x₂ + a⁴h·x₀x₂² - a²b²h·x₁²x₂ + 2ab³h·x₀x₁²
                - ab³·x₁x₂² + a³b·x₁² - 2a³b·x₁ + a³b - ab³h·x₀x₁ + 2ab³·x₂² - b⁴·x₀x₂ .
```

Grouping the terms shows the two structural descriptions used below (with `R = K[x₀,x₂]`):

* `cubTRed = A·x₁² + B·x₁ + C` where
  `A = ab·(a² + b·h·(2b·x₀ - a·x₂))`, `B = -ab·(2a² + b²·(h·x₀ + x₂²))`, and
  `C = a²h·x₀·(a·x₂ - b·x₀)² + a³b + b³·x₂·(2a·x₂ - b·x₀)`;
* `cubTRed = a²h·x₀·P² + a³b·(x₁-1)² + ab²h·x₁²·Q - ab³·x₁·(h·x₀ + x₂²) + b³·x₂·(a·x₂ + P)`
  with `P = a·x₂ - b·x₀` and `Q = 2b·x₀ - a·x₂`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type*} [Field K]

/-- The explicit cubic `cubT / (a·b·h)`. -/
noncomputable def cubTRed (a b h : K) : MvPolynomial (Fin 3) K :=
  C (a ^ 2 * b ^ 2 * h) * X 0 ^ 3
  - C (2 * a ^ 3 * b * h) * X 0 ^ 2 * X 2
  + C (a ^ 4 * h) * X 0 * X 2 ^ 2
  - C (a ^ 2 * b ^ 2 * h) * X 1 ^ 2 * X 2
  + C (2 * a * b ^ 3 * h) * X 0 * X 1 ^ 2
  - C (a * b ^ 3) * X 1 * X 2 ^ 2
  + C (a ^ 3 * b) * X 1 ^ 2
  - C (2 * a ^ 3 * b) * X 1
  + C (a ^ 3 * b)
  - C (a * b ^ 3 * h) * X 0 * X 1
  + C (2 * a * b ^ 3) * X 2 ^ 2
  - C (b ^ 4) * X 0 * X 2

/-- The value of the point `p = kleinPointT a b h` as an explicit vector. -/
lemma pRa_val (a b h : K) : Work.MotK.pRa a b h
    = ![C 1, C 0, C 1, C (b / (a * h)), C 0] := by
  funext i
  fin_cases i <;> simp [Work.MotK.pRa, Work.MotK.kleinPointT]

end Work.MotK.TGen
