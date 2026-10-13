import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Submission.Work.FTS.EllipticEst.Alpha4.Cut
import Submission.Work.FTS.EllipticEst.ZCuts.zCut_props

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.EllipticEst.Alpha4

/-- The logarithmic cut-off vanishes everywhere strictly to the *right* of the inner
threshold: `zc φ k w = 0` for `w < 1/k²` (where on `w ≤ 0` it is zero by construction and
on `0 < w < 1/k²` by `psiFun` vanishing there). -/
theorem zc_eq_zero_of_lt {φ : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hzero : ∀ z, 0 < z → z ≤ 1 / (k : ℝ) ^ 2 ∨ (k : ℝ) ^ 2 ≤ z →
      Work.FTS.EllipticEst.psiFun φ k z = 0)
    {w : ℝ} (hw : w < 1 / (k : ℝ) ^ 2) : zc φ k w = 0 :=
  zc_eq_zero_of_notMem hk hzero fun hmem => absurd hmem.1 (not_le.mpr hw)

/-- The logarithmic cut-off vanishes everywhere strictly to the *left* of the outer
threshold: `zc φ k w = 0` for `k² < w`. -/
theorem zc_eq_zero_of_gt {φ : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hzero : ∀ z, 0 < z → z ≤ 1 / (k : ℝ) ^ 2 ∨ (k : ℝ) ^ 2 ≤ z →
      Work.FTS.EllipticEst.psiFun φ k z = 0)
    {w : ℝ} (hw : (k : ℝ) ^ 2 < w) : zc φ k w = 0 :=
  zc_eq_zero_of_notMem hk hzero fun hmem => absurd hmem.2 (not_le.mpr hw)

theorem deriv_zc_eq_zero_of_notMem {k : ℕ} (hk2 : 2 ≤ k) {φ : ℝ → ℝ} {K : ℝ}
    (hφK : Work.FTS.EllipticEst.IsZCut φ K)
    {z : ℝ} (hz : z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2)) :
    deriv (Work.FTS.EllipticEst.Alpha4.zc φ k) z = 0 := by
  obtain ⟨-, hzero, -, -, -⟩ := Work.FTS.EllipticEst.ZCuts.zCut_props hφK k hk2
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk2
  -- off the interval, `zc φ k` is *locally* zero, so its derivative vanishes there
  have hlt : z < 1 / (k : ℝ) ^ 2 ∨ (k : ℝ) ^ 2 < z := by
    by_contra hcon
    rw [not_or] at hcon
    exact hz ⟨le_of_not_gt hcon.1, le_of_not_gt hcon.2⟩
  have hev : zc φ k =ᶠ[𝓝 z] fun _ : ℝ => (0 : ℝ) := by
    rcases hlt with h | h
    · filter_upwards [isOpen_Iio.mem_nhds h] with w hw
      exact zc_eq_zero_of_lt hk1 hzero hw
    · filter_upwards [isOpen_Ioi.mem_nhds h] with w hw
      exact zc_eq_zero_of_gt hk1 hzero hw
  rw [hev.deriv_eq, deriv_const]

end Work.FTS.EllipticEst.Alpha4
