import Mathlib
import Submission.Work.MotAS.ASData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotC5N3.KleinPASNegApply` — the reversal identity for the AS twisted Pfaffians, cycle-free

`Work.MotAS.kleinPAS_neg_apply` (proved in `Submission/Work/MotAS/ASZTwistDivPlaneGeomV2.lean`)
says that changing the sign of the AS class is implemented by the diagonal `diag((-1)^i)`, up to the
componentwise sign `(-1)^j`:

`p^AS_k(a, b, -c)(z) = (-1)^k · p^AS_k(a, b, c)((-1)^i z_i)`.

The same statement is restated here over `Work.MotAS.ASData` alone (no `ASZTwistDivPlaneGeomV2`
import), because `MotAS/ASZTwistDivPlaneGeomV2.lean` now imports
`Work.MotC5N3.ASZTwistDivPlaneGeomGen`, which forces an **import cycle**

`MotAS/ASZTwistDivPlaneGeomV2 → MotC5N3/ASZTwistDivPlaneGeomGen →
MotC5N3/ASZTwistDivPlaneGeom → MotC5N3/ASZChartNegIso → MotAS/ASZTwistDivPlaneGeomV2`,

which blocks the build of every module on the K6 chain (including `MotC5N3.ASZTwistDiv2`).
`Work.MotC5N3.ASZChartNegIso` uses exactly one declaration from `ASZTwistDivPlaneGeomV2`
(`kleinPAS_neg_apply`, at its line 119), so repointing that import to this module breaks the cycle:

* in `Submission/Work/MotC5N3/ASZChartNegIso.lean`, replace
  `import Submission.Work.MotAS.ASZTwistDivPlaneGeomV2` by
  `import Submission.Work.MotC5N3.KleinPASNegApply`, and
  `Work.MotAS.kleinPAS_neg_apply` by `Work.MotC5N3.kleinPAS_neg_apply` (one occurrence, line 119).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Work.MotC5N3

/-- **The reversal identity for the AS twisted Pfaffians.**  Changing the sign of the AS class is
implemented by the diagonal `diag((-1)^i)`, up to the componentwise sign `(-1)^j` (which is the
graded permutation of the Pfaffian net under the reversal `z_i ↦ z_{-i}`, `p_{rev k}(z)`).

This is a verbatim copy of `Work.MotAS.kleinPAS_neg_apply`
(`Submission/Work/MotAS/ASZTwistDivPlaneGeomV2.lean`), stated here over the cycle-free import
`Work.MotAS.ASData`. -/
theorem kleinPAS_neg_apply {R : Type*} [CommRing R] (a b c : R) (z : Fin 5 → R) (j : Fin 5) :
    Work.MotAS.kleinPAS a b (-c) z j
      = (-1 : R) ^ (j : ℕ) *
        Work.MotAS.kleinPAS a b c (fun i => (-1 : R) ^ (i : ℕ) * z i) j := by
  fin_cases j <;>
    simp only [Work.MotAS.kleinPAS, Work.MotAS.kleinPAS0, Work.MotAS.kleinPAS1,
      Work.MotAS.kleinPAS2, Work.MotAS.kleinPAS3, Work.MotAS.kleinPAS4,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;>
    norm_num <;> ring

end Work.MotC5N3
