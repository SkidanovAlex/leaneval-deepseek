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

/-- **The `u`-derivative of the clean bracket.**  For `0 < u` and `u + 2v > 0` (so that
`u² + 2uv > 0`), the function `u ↦ phiC u v r` has derivative `-v²/(S·D)` at `u`, where
`S = u + v + √(u²+2uv)` and `D = √(u²+2uv)`.

Route: quotient rule (or `phiC_eq_phiG`); the identity `1 + (u+v)/D = S/D` turns the
quotient-rule answer into `-v²/(S·D)`. -/
theorem phiC_hasDerivAt_u {u v r : ℝ} (hu : 0 < u) (huv : 0 < u + 2 * v) :
    HasDerivAt (fun w : ℝ => phiC w v r)
      (-(v ^ 2 / ((u + v + Real.sqrt (u ^ 2 + 2 * u * v))
        * Real.sqrt (u ^ 2 + 2 * u * v)))) u := by
  -- `D = √(u²+2uv) > 0` and `S = u+v+D > 0` on the honest range.
  have harg : 0 < u ^ 2 + 2 * u * v := by nlinarith [mul_pos hu huv]
  have hD : 0 < Real.sqrt (u ^ 2 + 2 * u * v) := Real.sqrt_pos_of_pos harg
  have hS : 0 < u + v + Real.sqrt (u ^ 2 + 2 * u * v) := by
    have := Real.sqrt_nonneg (u ^ 2 + 2 * u * v); linarith
  -- `d/du (u²+2uv) = 2u+2v`.
  have hquad : HasDerivAt (fun w : ℝ => w ^ 2 + 2 * w * v) (2 * u + 2 * v) u := by
    have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have hl : HasDerivAt (fun w : ℝ => 2 * w * v) (2 * v) u :=
      (hasDerivAt_const_mul (2 : ℝ) (x := u)).mul_const v
    exact hp.add hl
  -- Chain rule: `d/du √(u²+2uv) = (u+v)/D`.
  have hsq : HasDerivAt (fun w : ℝ => Real.sqrt (w ^ 2 + 2 * w * v))
      ((u + v) / Real.sqrt (u ^ 2 + 2 * u * v)) u := by
    have h := hquad.sqrt harg.ne'
    convert h using 1
    rw [div_eq_div_iff hD.ne' (mul_ne_zero two_ne_zero hD.ne')]
    ring
  have hid : HasDerivAt (fun w : ℝ => w + v) 1 u := by
    simpa using (hasDerivAt_id u).add_const v
  -- `d/du S = 1 + (u+v)/D`.
  have hDfun : HasDerivAt (fun w : ℝ => w + v + Real.sqrt (w ^ 2 + 2 * w * v))
      (1 + (u + v) / Real.sqrt (u ^ 2 + 2 * u * v)) u := hid.add hsq
  have hnum : HasDerivAt (fun _ : ℝ => v ^ 2) 0 u := hasDerivAt_const u (v ^ 2)
  have hquot := hnum.div hDfun hS.ne'
  have hC : HasDerivAt (fun _ : ℝ => v ^ 2 / (2 * r ^ 2)) 0 u := hasDerivAt_const u _
  have hsub : HasDerivAt
      (fun w : ℝ => v ^ 2 / (w + v + Real.sqrt (w ^ 2 + 2 * w * v)) - v ^ 2 / (2 * r ^ 2))
      ((0 * (u + v + Real.sqrt (u ^ 2 + 2 * u * v))
          - v ^ 2 * (1 + (u + v) / Real.sqrt (u ^ 2 + 2 * u * v)))
        / (u + v + Real.sqrt (u ^ 2 + 2 * u * v)) ^ 2 - 0) u := hquot.sub hC
  -- `1 + (u+v)/D = S/D`.
  have hkey : 1 + (u + v) / Real.sqrt (u ^ 2 + 2 * u * v)
      = (u + v + Real.sqrt (u ^ 2 + 2 * u * v)) / Real.sqrt (u ^ 2 + 2 * u * v) := by
    rw [eq_div_iff hD.ne', add_mul, one_mul, div_mul_cancel₀ _ hD.ne']
    ring
  -- The quotient-rule answer equals `-v²/(S·D)`.
  have hEq : ((0 * (u + v + Real.sqrt (u ^ 2 + 2 * u * v))
          - v ^ 2 * (1 + (u + v) / Real.sqrt (u ^ 2 + 2 * u * v)))
        / (u + v + Real.sqrt (u ^ 2 + 2 * u * v)) ^ 2 - 0)
      = -(v ^ 2 / ((u + v + Real.sqrt (u ^ 2 + 2 * u * v))
          * Real.sqrt (u ^ 2 + 2 * u * v))) := by
    rw [sub_zero, zero_mul, zero_sub, hkey]
    field_simp
  change HasDerivAt
      (fun w : ℝ => v ^ 2 / (w + v + Real.sqrt (w ^ 2 + 2 * w * v)) - v ^ 2 / (2 * r ^ 2))
      (-(v ^ 2 / ((u + v + Real.sqrt (u ^ 2 + 2 * u * v))
        * Real.sqrt (u ^ 2 + 2 * u * v)))) u
  rw [← hEq]
  exact hsub

end Work.BoseBogFS
