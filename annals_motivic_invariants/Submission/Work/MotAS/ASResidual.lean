import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotK.TwAmbh

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The residual curve of the AS (characteristic-`5`) Crauder–Katz link, in the affine chart

Part of the subproject `Submission/Work/MotAS` (`Work.MotAS`), node **LK_AS′**.  This file is the
AS analogue of `Submission/Work/MotK/TwCensus/Defs.lean` (the T-twisted residual curve) and holds
only definitions, so that the statements about them can be proved in parallel.

* `zcubAS a b g k` (`k : Fin 5`): the five cubics of the *inverse* AS link map `kleinRAS` (the AS
  transport of `Work.MotK.kleinR`), evaluated at the affine chart vector
  `chartAS = (1, x₀, x₁, x₂, 0)` of the AS target *hyperplane* `{z₄ = 0}`;
* `ZIAS a b g`: the ideal they generate in `K[x₀,x₁,x₂]`.

⚠ The slice matters.  In the AS coordinates the target hyperplane is `{z₄ = 0}` (since
`Σ_k z_k = -z₄`, `MOTIVIC_KDATA_LEAD.md` §6.2), so the residual curve has to be read in the slice
`V(kleinRAS) ∩ {z₄ = 0}`, charted by one of `z₀,…,z₃ = 1`.  The *T-route* convention
`chart3 = (0,x₀,x₁,x₂,1)` (`V(kleinRAS) ∩ {z₀ = 0}`) is the wrong slice here: `Work.MotV5/STATUS.md`
§13.5 records (probe `_scratch/as_probe8.py`) that it admits **no** monomial isomorphism onto a
twist curve, whereas `V(kleinRAS) ∩ {z₄ = 0}` does (probes `as_probe9.py`–`as_probe11.py`, with
ideal-membership verified).  Recorded example: `(a,b) = (2,1)`, slice `{z₄ = 0, z₀ = 1}`,
twist-curve chart `y₁ = 1`, `(i₁,i₂,i₃) = (2,3,4)`, `(λ₁,λ₂,λ₃) = (2,3,4)` over `𝔽₅`.

Their common zero locus, the chart part of the **residual curve** `C'` of the AS link, is the base
of the ruling of the source ruling divisor `sAS` (the `D_Q` prime of the AS census,
`Submission/Work/MotAS/ChartDefs.lean`), and by the Crauder–Katz description of the quadro-cubic
transformation it is `Jac²` of the AS-twisted Klein curve, hence its function field is the twist
field of *twice* the class, `Work.MotAS.twistFieldAS D (2 • fAS 𝕜)`
(`MOTIVIC_KDATA_LEAD.md` §6.2, "The D_Q prime (`s^AS∘y`) has class `C'` = twist by `±2f`").

## Numerical checks (CAS, this session)

* Common zeros of the five `zcubAS` cubics in the chart `(X₀,X₁,X₂)` over `𝔽₅`:
  `(a,b,g) = (1,1,1) : 4`, `(1,1,2) : 5`, `(2,1,1) : 9`, `(2,1,3) : 9` — consistent with a
  genus-one residual curve, and matching `Work.MotV5/STATUS.md` §13.5 (probes `as_probe9.py`–
  `as_probe11.py`, which verify *ideal membership*: the pulled-back slice cubics are nonzero
  cubics in the ideal of the twist curve).  For `(a,b,g) = (2,1,1)` the slice is the monomial
  image of the twist curve with chart `y₁ = 1`, `(i₁,i₂,i₃) = (2,3,4)`, `(λ₁,λ₂,λ₃) = (2,3,4)`,
  the example recorded in that §13.5 addendum.
* Number of lines contained in the projective surface `{sAS(1,1,c) = 0} ⊂ ℙ³` over `𝔽₅`:
  `5` for `c = 1`, `5` for `c = 2` — the point count of a genus-one base curve over `𝔽₅`.
* ⚠ Open: §13.5 also records that over `𝔽₅` the twist classes `g` and `2g` cannot be separated
  (non-isomorphic curves with equal point counts, both admitting such monomial maps into suitable
  slices), so *which* of `fAS` and `2 • fAS` is the class of the residual curve is **not** settled
  by finite-field numerics — `2 • fAS` is the design's (and the T-route's) value, and it is what
  the census clause needs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotAS

open MvPolynomial

variable {K : Type*}

/-- The five cubics of the inverse AS link map `kleinRAS`, in the affine chart
`chartAS = (1, x₀, x₁, x₂, 0)` of the AS target hyperplane `{z₄ = 0}`: the equations of the chart
part of the residual curve `C'`. -/
noncomputable def zcubAS [Field K] (a b g : K) (k : Fin 5) : MvPolynomial (Fin 3) K :=
  kleinRAS (C a) (C b) (C g) ![1, X 0, X 1, X 2, 0] k

/-- The ideal of the chart part of the residual curve `C'` of the AS link. -/
noncomputable def ZIAS [Field K] (a b g : K) : Ideal (MvPolynomial (Fin 3) K) :=
  Ideal.span (Set.range (zcubAS a b g))

end Work.MotAS
