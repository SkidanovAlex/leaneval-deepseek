/-
# The core chart inverse lands in the core stratum

`cuspInvCore v q` is the inverse of the core chart `ThetaCore v` (blueprint §1): for
`q = (a, b, w₁, w₂)` it recovers the polar data `r = √(a²+b²)`, `θ = argOf b a` and then runs the
inner-chart inverse `cuspInvInner v (r, θ, w₁, w₂)`, whose first component is the layer parameter
`p = t • bndOfU u` of the filling square.

The target of the chart is `coreBox = {q | √(q 0² + q 1²) < 1/2}`, i.e. `r < 1/2`, which is
contained in the inner branch `r ≤ r_J = 3` of `cuspInvInner`, so the recovered layer parameter is
`t = r / (2 r_J) = r / 6`.  Since `bndOfU u` lies on the boundary `∂Sq` of the unit square, its sup
norm is `1` (`nrm_bndOfU`), so `nrm (t • bndOfU u) = t = r/6 < (1/2)/6 = 1/12`, which is exactly the
core stratum `coreStratum = {p | nrm p < 1/12}`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.nrm_smul
import Submission.Work.Cusp.nrm_bndOfU

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- On its inner branch (`q 0 ≤ r_J`) the layer parameter recovered by `cuspInvInner` is
`t = q 0 / (2 r_J)`, and its first component is `t • bndOfU u`; because `nrm (bndOfU u) = 1`
(`nrm_bndOfU`) its sup norm is `t` up to the absolute value, which the hypothesis `0 ≤ q 0` removes
(`nrm_smul`). -/
private lemma nrm_fst_cuspInvInner_of_le (v : Fin 5) (q : E4) (h0 : 0 ≤ q 0) (h : q 0 ≤ rJ) :
    nrm (cuspInvInner v q).1 = q 0 / (2 * rJ) := by
  have hnn : 0 ≤ q 0 / (2 * rJ) := div_nonneg h0 (by norm_num [rJ])
  simp only [cuspInvInner, h, ite_true]
  rw [nrm_smul, nrm_bndOfU, mul_one, abs_of_nonneg hnn]

/-- The first component of `cuspInvCore v q` is the first component of `cuspInvInner v` at the
polar coordinates `(r, θ, w) = (√(q 0² + q 1²), argOf (q 1) (q 0), q 2, q 3)`; this is the
definition of `cuspInvCore`, with the two `let` bindings inlined. -/
theorem fst_cuspInvCore_eq (v : Fin 5) (q : E4) :
    (cuspInvCore v q).1
      = (cuspInvInner v !₂[Real.sqrt (q 0 ^ 2 + q 1 ^ 2), argOf (q 1) (q 0), q 2, q 3]).1 :=
  rfl

/-- **The inverse of the core chart lands in the core stratum.**  For `q ∈ coreBox` the recovered
layer parameter is `t = √(q 0² + q 1²)/(2 r_J) < (1/2)/6 = 1/12`, and `nrm (bndOfU u) = 1`, so the
recovered point `(cuspInvCore v q).1 = t • bndOfU u` has sup norm `< 1/12`, i.e. lies in
`coreStratum`. -/
theorem cuspInvCore_mem_coreStratum (v : Fin 5) (q : E4) (hq : q ∈ coreBox) :
    (cuspInvCore v q).1 ∈ coreStratum := by
  have hrlt : Real.sqrt (q 0 ^ 2 + q 1 ^ 2) < 1/2 := hq
  have hrnn : 0 ≤ Real.sqrt (q 0 ^ 2 + q 1 ^ 2) := Real.sqrt_nonneg _
  have hrle : Real.sqrt (q 0 ^ 2 + q 1 ^ 2) ≤ rJ := by
    rw [show rJ = 3 from rfl]; linarith
  rw [coreStratum, Set.mem_ofPred_eq, fst_cuspInvCore_eq v q,
    nrm_fst_cuspInvInner_of_le v _ hrnn hrle]
  have h2 : (2 : ℝ) * rJ = 6 := by rw [show rJ = 3 from rfl]; norm_num
  rw [h2]
  show Real.sqrt (q 0 ^ 2 + q 1 ^ 2) / 6 < 1/12
  nlinarith [hrlt]

end Work.Cusp
