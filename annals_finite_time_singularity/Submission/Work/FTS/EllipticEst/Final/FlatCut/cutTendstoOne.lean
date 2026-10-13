import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Submission.Work.FTS.EllipticEst.interpol_trunc_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Final.FlatCut

open Filter

/-- For fixed `z > 0` the cut-off `cut n z` is eventually `1`: the two thresholds
`2/(n+1) ≤ z` and `z ≤ 2(n+1)` hold as soon as `n ≥ ⌈2/z⌉ + ⌈z/2⌉`. -/
theorem eventually_cut_eq_one (z : ℝ) (hz : 0 < z) :
    (fun n : ℕ => Work.FTS.EllipticEst.cut n z) =ᶠ[Filter.atTop] (fun _ : ℕ => (1 : ℝ)) := by
  refine Filter.eventually_atTop.mpr ⟨Nat.ceil (2 / z) + Nat.ceil (z / 2), fun n hn => ?_⟩
  have h1 : 2 / z ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (Nat.le_add_right _ _) hn)
  have h2 : z / 2 ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (Nat.le_add_left _ _) hn)
  have h1' : 2 ≤ (n : ℝ) * z := by
    rw [div_le_iff₀ hz] at h1
    linarith
  have h2' : z ≤ 2 * (n : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)] at h2
    linarith
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  refine Work.FTS.EllipticEst.cut_eq_one_of_mem n ?_ ?_
  · rw [div_le_iff₀ hn1]
    nlinarith
  · nlinarith

theorem cutTendstoOne (z : ℝ) (hz : 0 < z) : Filter.Tendsto (fun n : ℕ => Work.FTS.EllipticEst.cut n z) Filter.atTop (nhds 1) :=
  Filter.Tendsto.congr' (eventually_cut_eq_one z hz).symm tendsto_const_nhds

end Work.FTS.EllipticEst.Final.FlatCut
