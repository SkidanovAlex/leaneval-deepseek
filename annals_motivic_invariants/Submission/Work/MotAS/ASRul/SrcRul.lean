import Mathlib
import Submission.Work.MotAS.ASRul.Matrices
import Submission.Work.MotAS.ASResidual

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRul.SrcRul` — the source ruling line of the AS2 chart, evaluated

The AS ruling matrix `AmatAS a b g ![1,u,v,w,0]` (`ASRul/Matrices.lean`) has rank `3` at every point
`(u,v,w)` of the residual curve `V(ZIAS)` with `w ≠ 0`, and its kernel — the ruling line of the
source divisor `{sAS2 = 0}` over the base point `(1 : u : v : w : 0)` — is spanned by the two
explicit vectors `srcRvEv`, `srcRwEv` below.  They are the *evaluated* form of the polynomial
witnesses (cf. `Work.MotAS.ASrulV` / `Work.MotAS.ASrulW`, and `Work.MotAS.ASRul.kbRv` /
`kbRw`), with slots `3, 4` equal to `(δ, 0)` resp. `(0, ε)` where

`δ = (2a−b)(a+2b)w²`,  `ε = (2a−b)(a+2b)²w²`

are nonzero under `a ≠ 0`, `b ≠ 0`, `b ≠ 2a` (char `5`) and `w ≠ 0`.  A general kernel vector is
`z = c • srcRvEv + d • srcRwEv`, whose 5th coordinate is `d·ε`; the point of the source chart
`{v₀ = 0, v₄ = 1}` cut out by the ruling line is therefore `π_{e₀}(z)` normalised by `z 4`, i.e.
the three ratios computed in `srcRulPt` below.  (`srcRulPt` is the AS analogue of the T-route's
`RVS`/`RWS` pair; here the projection `π_{e₀}` is trivial, `π_{e₀}(z) = (0,z₁,z₂,z₃,z₄)`.)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS.ASRul

variable {K : Type*} [Field K]

/-- **The first AS ruling vector, evaluated** at the base point `(u,v,w)`, denominators cleared
(slot `3` is `(2a−b)(a+2b)w²`, slot `4` is `0`). -/
noncomputable def srcRvEv (a b g u v w : K) : Fin 5 → K :=
  ![ (a + 2 * b) * (2 * a * u * v - a * v * w - a * w - b * u * v + 2 * b * v * w - 2 * b * w),
     (2 * a - b) * ((2 * a - b) * v ^ 2 + (a - 2 * b) * w ^ 2),
     (2 * a - b) * (a + 2 * b) * (v * w),
     (2 * a - b) * (a + 2 * b) * w ^ 2,
     0 ]

/-- **The second AS ruling vector, evaluated** at the base point `(u,v,w)`, denominators cleared
(slot `3` is `0`, slot `4` is `(2a−b)(a+2b)²w²`). -/
noncomputable def srcRwEv (a b g u v w : K) : Fin 5 → K :=
  ![ -(a + 2 * b) * ((4 * a ^ 2 - 4 * a * b + b ^ 2) * u ^ 2
        + (4 * a ^ 2 + 10 * a * b - b ^ 2) * u * w
        + (-3 * a ^ 2 - a * b - 2 * b ^ 2) * w ^ 2),
     -(2 * a - b) * ((4 * a ^ 2 - 4 * a * b + b ^ 2) * u * v
        + (6 * a ^ 2 + 5 * a * b + b ^ 2) * v * w
        + (2 * a ^ 2 + 3 * a * b - 2 * b ^ 2) * w),
     -(a + 2 * b) * (2 * a - b) * w * ((2 * a - b) * u + (2 * a + b) * w),
     0,
     (2 * a - b) * (a + 2 * b) ^ 2 * w ^ 2 ]

/-- **The point of the source chart on the ruling line** over the base point `(u,v,w)`, with ruling
parameter `t`: the chart coordinates of `π_{e₀}(t • srcRvEv + srcRwEv)`, normalised by the 5th
coordinate `(2a−b)(a+2b)²w²`. -/
noncomputable def srcRulPt (a b g u v w t : K) : Fin 3 → K :=
  ![ (t * srcRvEv a b g u v w 1 + srcRwEv a b g u v w 1) / (srcRwEv a b g u v w 4),
     (t * srcRvEv a b g u v w 2 + srcRwEv a b g u v w 2) / (srcRwEv a b g u v w 4),
     (t * srcRvEv a b g u v w 3 + srcRwEv a b g u v w 3) / (srcRwEv a b g u v w 4) ]

end Work.MotAS.ASRul
