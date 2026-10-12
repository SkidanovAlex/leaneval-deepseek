import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.BoseBox.LatticeModel.LhyAuxDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Differentiability of `lhyF c` on `(0,∞)` with derivative `lhyD c r`

`lhyF c r = r² + c − r·√(r²+2c) − c²/(2r²)` is differentiable on `r > 0`
with derivative `lhyD c r = 2r − 2(r²+c)/√(r²+2c) + c²/r³`.

The only point needing an argument (beyond the chain rule and the quotient
rule) is that the "raw" derivative coming out of the product rule,

`2r − (√(r²+2c) + r·(2r/(2√(r²+2c)))) + c²/r³`,

coincides with `lhyD c r`; this uses
`√(r²+2c)·√(r²+2c) = r²+2c` to replace
`√(r²+2c) + r²/√(r²+2c)` by `2(r²+c)/√(r²+2c)`.
-/

noncomputable section

open scoped Real

namespace Work.BoseBox.LatticeModel

/-- The rationalised Bogoliubov bracket `lhyF c` is differentiable on `(0,∞)`,
with the explicit derivative `lhyD c r`. -/
theorem hasDerivAt_lhyF (c r : ℝ) (hc : 0 < c) (hr : 0 < r) :
    HasDerivAt (lhyF c) (lhyD c r) r := by
  have harg : 0 < r ^ 2 + 2 * c := by nlinarith [sq_nonneg r]
  have hs_pos : 0 < Real.sqrt (r ^ 2 + 2 * c) := Real.sqrt_pos.2 harg
  have hs_ne : Real.sqrt (r ^ 2 + 2 * c) ≠ 0 := ne_of_gt hs_pos
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hs2 : Real.sqrt (r ^ 2 + 2 * c) ^ 2 = r ^ 2 + 2 * c := Real.sq_sqrt (le_of_lt harg)
  -- derivative of the inner square root factor
  have hg : HasDerivAt (fun x : ℝ => x ^ 2 + 2 * c) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).add_const (2 * c)
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 + 2 * c))
      (2 * r / (2 * Real.sqrt (r ^ 2 + 2 * c))) r :=
    hg.sqrt (ne_of_gt harg)
  -- the three pieces of `lhyF c`
  have hA : HasDerivAt (fun x : ℝ => x ^ 2 + c) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).add_const c
  have hB : HasDerivAt (fun x : ℝ => x * Real.sqrt (x ^ 2 + 2 * c))
      (Real.sqrt (r ^ 2 + 2 * c) + r * (2 * r / (2 * Real.sqrt (r ^ 2 + 2 * c)))) r := by
    refine ((hasDerivAt_id r).mul hs).congr_deriv ?_
    simp only [id_eq]
    ring
  have hC : HasDerivAt (fun x : ℝ => c ^ 2 / (2 * x ^ 2)) (-(c ^ 2 / r ^ 3)) r := by
    have h2 : HasDerivAt (fun x : ℝ => 2 * x ^ 2) (2 * (2 * r)) r := by
      simpa using (hasDerivAt_pow 2 r).const_mul 2
    refine ((hasDerivAt_const (x := r) (c := c ^ 2)).div h2 (by positivity)).congr_deriv ?_
    field_simp
    ring
  -- combine and rewrite the raw derivative into `lhyD c r`
  have h2s : r * (2 * r / (2 * Real.sqrt (r ^ 2 + 2 * c)))
      = r ^ 2 / Real.sqrt (r ^ 2 + 2 * c) := by
    field_simp
  have hkey : Real.sqrt (r ^ 2 + 2 * c) + r ^ 2 / Real.sqrt (r ^ 2 + 2 * c)
      = 2 * (r ^ 2 + c) / Real.sqrt (r ^ 2 + 2 * c) := by
    have h : Real.sqrt (r ^ 2 + 2 * c) + r ^ 2 / Real.sqrt (r ^ 2 + 2 * c)
        = (Real.sqrt (r ^ 2 + 2 * c) ^ 2 + r ^ 2) / Real.sqrt (r ^ 2 + 2 * c) := by
      field_simp
    rw [h, hs2]
    ring
  exact ((hA.sub hB).sub hC).congr_deriv (by
    rw [lhyD, h2s, hkey]
    ring)

end Work.BoseBox.LatticeModel
