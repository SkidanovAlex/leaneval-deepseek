import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Series.Deleg.phiASeriesDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

/-- The `n`-th summand of `phiAseries α k`, differentiated: the derivative is the `n`-th summand
of `phiAseries α (k+1)`.  The point is that
`(d/dz) (1+z)^{m} = m (1+z)^{m-1}` and `∏_{i<k+1}(m-i) = (∏_{i<k}(m-i)) · (m-k)`. -/
private lemma hasDerivAt_phiAterm (α : ℝ) (k n : ℕ) {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (fun w : ℝ => phiAcoef α n * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
        * (1 + w) ^ (-(n : ℤ) - 1 - (k : ℤ)))
      (phiAcoef α n * (∏ i ∈ Finset.range (k + 1), ((-(n : ℝ) - 1) - i))
        * (1 + z) ^ (-(n : ℤ) - 1 - (((k + 1 : ℕ)) : ℤ))) z := by
  have h1z : (1 : ℝ) + z ≠ 0 := by
    intro h
    exact hz (by linarith)
  -- the pure power `(1+w)^m`, `m = -n-1-k`
  have hb : HasDerivAt (fun w : ℝ => ((1 : ℝ) + w) ^ (-(n : ℤ) - 1 - (k : ℤ)))
      (((-(n : ℤ) - 1 - (k : ℤ) : ℤ) : ℝ) * (1 + z) ^ ((-(n : ℤ) - 1 - (k : ℤ)) - 1)) z := by
    have h := (hasDerivAt_zpow (-(n : ℤ) - 1 - (k : ℤ)) ((1 : ℝ) + z) (Or.inl h1z)).comp z
      ((hasDerivAt_id z).const_add 1)
    simpa [Function.comp_def] using h
  have hprod :=
    HasDerivAt.const_mul (phiAcoef α n * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))) hb
  refine hprod.congr_deriv ?_
  rw [show (-(n : ℤ) - 1 - (((k + 1 : ℕ)) : ℤ)) = (-(n : ℤ) - 1 - (k : ℤ)) - 1 from by
        push_cast; ring,
      Finset.prod_range_succ]
  have hcast : ((-(n : ℤ) - 1 - (k : ℤ) : ℤ) : ℝ) = (-(n : ℝ) - 1) - (k : ℝ) := by
    push_cast; ring
  rw [hcast]
  ring

theorem hasDerivAtPhiAseries (α : ℝ) (k : ℕ) {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (Work.FTS.PhiStar.Series.Deleg.phiAseries α k)
      (Work.FTS.PhiStar.Series.Deleg.phiAseries α (k + 1) z) z := by
  change HasDerivAt (fun w : ℝ => ∑ n ∈ Finset.range 4,
      phiAcoef α n * (∏ i ∈ Finset.range k, ((-(n : ℝ) - 1) - i))
        * (1 + w) ^ (-(n : ℤ) - 1 - (k : ℤ)))
    (∑ n ∈ Finset.range 4,
      phiAcoef α n * (∏ i ∈ Finset.range (k + 1), ((-(n : ℝ) - 1) - i))
        * (1 + z) ^ (-(n : ℤ) - 1 - (((k + 1 : ℕ)) : ℤ))) z
  exact HasDerivAt.fun_sum (u := Finset.range 4) (fun n _ => hasDerivAt_phiAterm α k n hz)

end Work.FTS.PhiStar.Series.Deleg
