/-
The assembly of the mixed weighted interpolation estimate.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.ZCuts.zCut_props

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Alpha4

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The logarithmic cut-off, extended by zero to `z ≤ 0` -/

/-- The logarithmic cut-off `ZCuts.psiFun`, extended by `0` to `z ≤ 0`.  It is `C^∞` on
`(0,∞)`, lies in `[0,1]`, equals `1` on `[1/k, k]`, vanishes off `[1/k², k²]` (on the whole
line now), and satisfies `|z ζ'(z)| ≤ K / log k` for `z > 0`. -/
def zc (φ : ℝ → ℝ) (k : ℕ) : ℝ → ℝ := fun z => if 0 < z then Work.FTS.EllipticEst.psiFun φ k z else 0

theorem zc_of_pos {φ : ℝ → ℝ} {k : ℕ} {z : ℝ} (hz : 0 < z) :
    zc φ k z = Work.FTS.EllipticEst.psiFun φ k z := by
  simp only [zc, if_pos hz]

theorem zc_of_nonpos {φ : ℝ → ℝ} {k : ℕ} {z : ℝ} (hz : z ≤ 0) : zc φ k z = 0 := by
  simp only [zc, if_neg (not_lt.mpr hz)]

theorem zc_deriv_eq {φ : ℝ → ℝ} {k : ℕ} {z : ℝ} (hz : 0 < z) :
    deriv (zc φ k) z = deriv (Work.FTS.EllipticEst.psiFun φ k) z := by
  have hev : zc φ k =ᶠ[𝓝 z] Work.FTS.EllipticEst.psiFun φ k := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    exact zc_of_pos hy
  exact hev.deriv_eq

theorem zc_contDiffOn {φ : ℝ → ℝ} {k : ℕ}
    (hcd : ContDiffOn ℝ Work.FTS.EllipticEst.smoothOrder
      (Work.FTS.EllipticEst.psiFun φ k) (Set.Ioi 0)) :
    ContDiffOn ℝ 1 (zc φ k) (Set.Ioi 0) := by
  refine (hcd.of_le ?_).congr (fun z hz => zc_of_pos hz)
  simp only [Work.FTS.EllipticEst.ThetaU.smoothOrder_eq]
  simp

theorem zc_nonneg {φ : ℝ → ℝ} {k : ℕ} (hφ : ∀ z, 0 ≤ Work.FTS.EllipticEst.psiFun φ k z)
    (z : ℝ) : 0 ≤ zc φ k z := by
  rcases le_or_gt z 0 with h | h
  · rw [zc_of_nonpos h]
  · rw [zc_of_pos h]; exact hφ z

theorem zc_le_one {φ : ℝ → ℝ} {k : ℕ}
    (hφ : ∀ z, Work.FTS.EllipticEst.psiFun φ k z ≤ 1) (z : ℝ) : zc φ k z ≤ 1 := by
  rcases le_or_gt z 0 with h | h
  · rw [zc_of_nonpos h]; norm_num
  · rw [zc_of_pos h]; exact hφ z

theorem zc_eq_zero_of_notMem {φ : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hφ : ∀ z, 0 < z → z ≤ 1 / (k : ℝ) ^ 2 ∨ (k : ℝ) ^ 2 ≤ z →
      Work.FTS.EllipticEst.psiFun φ k z = 0)
    {z : ℝ} (hz : z ∉ Set.Icc (1 / (k : ℝ) ^ 2) ((k : ℝ) ^ 2)) : zc φ k z = 0 := by
  rcases le_or_gt z 0 with h | h
  · exact zc_of_nonpos h
  · rw [zc_of_pos h]
    refine hφ z h ?_
    rcases lt_or_ge z (1 / (k : ℝ) ^ 2) with h1 | h1
    · exact Or.inl h1.le
    · exact Or.inr (by
        by_contra hc
        exact hz ⟨h1, le_of_lt (not_le.mp hc)⟩)

theorem zc_eq_one_of_mem {φ : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hφ : ∀ z, 0 < z → 1 / (k : ℝ) ≤ z → z ≤ (k : ℝ) →
      Work.FTS.EllipticEst.psiFun φ k z = 1)
    {z : ℝ} (h1 : 1 / (k : ℝ) ≤ z) (h2 : z ≤ (k : ℝ)) : zc φ k z = 1 := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hz : 0 < z := lt_of_lt_of_le (by positivity) h1
  rw [zc_of_pos hz]
  exact hφ z hz h1 h2

theorem zc_deriv_bound {φ : ℝ → ℝ} {k : ℕ} {K : ℝ}
    (hφ : ∀ z, 0 < z → |z * deriv (Work.FTS.EllipticEst.psiFun φ k) z| ≤ K) :
    ∀ z, 0 < z → |z * deriv (zc φ k) z| ≤ K := by
  intro z hz
  rw [zc_deriv_eq hz]
  exact hφ z hz

