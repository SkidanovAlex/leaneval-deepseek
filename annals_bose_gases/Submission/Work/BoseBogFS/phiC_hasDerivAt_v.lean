import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.BoseBogFS.phiC_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- **The `v`-derivative of the clean bracket.**  For `0 < u`, `u + 2v > 0` and `r ≠ 0`, the
function `v ↦ phiC u v r` has at `v` the derivative

  `2v/S − v²(1 + u/D)/S² − v/r²`,   `S = u+v+√(u²+2uv)`, `D = √(u²+2uv)`.

Route: quotient rule on `v²/S` (with `S` differentiable by the chain rule for `Real.sqrt` on the
positive `u²+2uv`), plus `d/dv (v²/(2r²)) = v/r²`. -/
theorem phiC_hasDerivAt_v {u v r : ℝ} (hu : 0 < u) (huv : 0 < u + 2 * v) (hr : r ≠ 0) :
    HasDerivAt (fun w : ℝ => phiC u w r)
      (2 * v / (u + v + Real.sqrt (u ^ 2 + 2 * u * v))
        - v ^ 2 * (1 + u / Real.sqrt (u ^ 2 + 2 * u * v))
            / (u + v + Real.sqrt (u ^ 2 + 2 * u * v)) ^ 2
        - v / r ^ 2) v := by
  have harg : 0 < u ^ 2 + 2 * u * v := by
    have h : u ^ 2 + 2 * u * v = u * (u + 2 * v) := by ring
    rw [h]; exact mul_pos hu huv
  set D := Real.sqrt (u ^ 2 + 2 * u * v) with hDdef
  set S := u + v + D with hSdef
  have hDpos : 0 < D := by rw [hDdef]; exact Real.sqrt_pos.mpr harg
  have hDne : D ≠ 0 := hDpos.ne'
  have hDsq : D ^ 2 = u ^ 2 + 2 * u * v := by rw [hDdef]; exact Real.sq_sqrt harg.le
  -- `u + v = (u² + D²)/(2u) > 0`, so that the denominator `S` does not vanish
  have hSpos : 0 < S := by
    have h1 : u + v = (u ^ 2 + D ^ 2) / (2 * u) := by
      rw [eq_div_iff (by positivity : (2 : ℝ) * u ≠ 0)]
      rw [hDsq]; ring
    have h2 : 0 < (u ^ 2 + D ^ 2) / (2 * u) := div_pos (by positivity) (by positivity)
    rw [hSdef]
    linarith
  have hbase : HasDerivAt (fun w : ℝ => u ^ 2 + 2 * u * w) (2 * u) v :=
    (((hasDerivAt_id v).const_mul (2 * u)).congr_deriv (by ring)).const_add (u ^ 2)
  have hsqrt : HasDerivAt (fun w : ℝ => Real.sqrt (u ^ 2 + 2 * u * w)) (u / D) v := by
    have h := hbase.sqrt (ne_of_gt harg)
    have h2 : (2 * u) / (2 * Real.sqrt (u ^ 2 + 2 * u * v)) = u / D := by
      rw [hDdef]; field_simp
    rwa [h2] at h
  have hSderiv : HasDerivAt (fun w : ℝ => u + w + Real.sqrt (u ^ 2 + 2 * u * w)) (1 + u / D) v :=
    ((hasDerivAt_id v).const_add u).add hsqrt
  have hv2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * v) v :=
    HasDerivAt.congr_deriv (hasDerivAt_pow 2 v) (by simp)
  -- the quotient rule on `w ↦ w²/S(w)`
  have hfirst : HasDerivAt (fun w : ℝ => w ^ 2 / (u + w + Real.sqrt (u ^ 2 + 2 * u * w)))
      (2 * v / S - v ^ 2 * (1 + u / D) / S ^ 2) v := by
    have h := hv2.div hSderiv hSpos.ne'
    have hSval : u + v + Real.sqrt (u ^ 2 + 2 * u * v) = S := by rw [hSdef, hDdef]
    refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w => rfl))).congr_deriv ?_
    rw [hSval]
    field_simp [hSpos.ne', hDne]
  have hsecond : HasDerivAt (fun w : ℝ => w ^ 2 / (2 * r ^ 2)) (v / r ^ 2) v := by
    refine (hv2.div_const (2 * r ^ 2)).congr_deriv ?_
    field_simp
  have hmain : HasDerivAt
      (fun w : ℝ => w ^ 2 / (u + w + Real.sqrt (u ^ 2 + 2 * u * w)) - w ^ 2 / (2 * r ^ 2))
      (2 * v / S - v ^ 2 * (1 + u / D) / S ^ 2 - v / r ^ 2) v := hfirst.sub hsecond
  refine (hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun w => rfl))).congr_deriv ?_
  rfl

end Work.BoseBogFS
