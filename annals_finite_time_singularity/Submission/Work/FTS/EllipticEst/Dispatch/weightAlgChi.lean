import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.EllipticEst.Dispatch.AeCutGDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Dispatch

open Filter Set
open scoped Topology

/-- `iteratedDeriv 2 f` agrees with `deriv (deriv f)`. -/
private lemma iteratedDeriv_two_eq (f : ℝ → ℝ) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

/-- The second-derivative product rule: for two functions of class `C²` at a point,
`(f·g)'' = f''·g + 2 f'·g' + f·g''` at that point. -/
private lemma deriv_deriv_mul_eq (f g : ℝ → ℝ) (x : ℝ) (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    deriv (deriv (fun y : ℝ => f y * g y)) x
      = deriv (deriv f) x * g x + 2 * (deriv f x * deriv g x) + f x * deriv (deriv g) x := by
  rw [← iteratedDeriv_two_eq (fun y : ℝ => f y * g y)]
  change iteratedDeriv 2 (f * g) x
      = deriv (deriv f) x * g x + 2 * (deriv f x * deriv g x) + f x * deriv (deriv g) x
  rw [iteratedDeriv_mul hf hg]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_self, Nat.choose_zero_right,
    Nat.choose_one_right, iteratedDeriv_zero, iteratedDeriv_one, Nat.reduceSub, Nat.reduceAdd,
    zero_add]
  rw [iteratedDeriv_two_eq f, iteratedDeriv_two_eq g]
  ring

/-- The derived weight `z ↦ z² w(z)²` is of class `C²` away from `0`. -/
private lemma contDiffAt_wsq (z : ℝ) (hz : z ≠ 0) :
    ContDiffAt ℝ 2 (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z := by
  have hrat : ContDiffAt ℝ 2 (fun y : ℝ => (1 + y) ^ 4 / y ^ 2) z := by
    have h1 : ContDiffAt ℝ 2 (fun y : ℝ => (1 + y) ^ 4) z := by fun_prop
    have h2 : ContDiffAt ℝ 2 (fun y : ℝ => y ^ 2) z := by fun_prop
    exact h1.div h2 (by simpa using pow_ne_zero 2 hz)
  have h : (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)
      =ᶠ[𝓝 z] (fun y : ℝ => (1 + y) ^ 4 / y ^ 2) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    rw [Work.Spaces.w]; field_simp
  exact hrat.congr_of_eventuallyEq h

/-- The derived weight `z ↦ z w(z)²` is of class `C²` away from `0`. -/
private lemma contDiffAt_wlin (z : ℝ) (hz : z ≠ 0) :
    ContDiffAt ℝ 2 (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z := by
  have hrat : ContDiffAt ℝ 2 (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) z := by
    have h1 : ContDiffAt ℝ 2 (fun y : ℝ => (1 + y) ^ 4) z := by fun_prop
    have h2 : ContDiffAt ℝ 2 (fun y : ℝ => y ^ 3) z := by fun_prop
    exact h1.div h2 (by simpa using pow_ne_zero 3 hz)
  have h : (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)
      =ᶠ[𝓝 z] (fun y : ℝ => (1 + y) ^ 4 / y ^ 3) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    rw [Work.Spaces.w]; field_simp
  exact hrat.congr_of_eventuallyEq h

theorem weightAlgChi (χ : ℝ → ℝ) (hχsm : ContDiff ℝ 2 χ) (hχnn : ∀ z : ℝ, 0 ≤ χ z) :
    (∀ z : ℝ, 0 < z →
      deriv (deriv (fun y : ℝ => y ^ 2 * Work.FTS.EllipticEst.Dispatch.Wcut χ y)) z
        ≤ 6 * Work.FTS.EllipticEst.Dispatch.Wcut χ z
          + Work.FTS.EllipticEst.Dispatch.AeCut.F2g χ z) ∧
    (∀ z : ℝ, 0 < z →
      -3 * Work.FTS.EllipticEst.Dispatch.Wcut χ z
          - Work.FTS.EllipticEst.Dispatch.AeCut.F1g χ z
        ≤ deriv (fun y : ℝ => y * Work.FTS.EllipticEst.Dispatch.Wcut χ y) z) := by
  -- the two-sided weight algebra of `weight_algebra_fts`:
  -- `(z²w²)'' ≤ 6w²` and `(zw²)' ≥ -3w²` on `z > 0`.
  obtain ⟨_, _, _, _, _, wa6, wa7, _, _, _, _⟩ := Work.FTS.EllipticEst.weight_algebra_fts
  constructor
  · -- `(z²W)'' ≤ 6W + F2g`
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have hχ2 : ContDiffAt ℝ 2 χ z := hχsm.contDiffAt
    have hg2 : ContDiffAt ℝ 2 (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z :=
      contDiffAt_wsq z hz0
    -- `z²·Wcut χ = χ·(z²w²)`
    have hfun : (fun y : ℝ => y ^ 2 * Work.FTS.EllipticEst.Dispatch.Wcut χ y)
        = (fun y : ℝ => χ y * (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) y) := by
      funext y
      simp only [Work.FTS.EllipticEst.Dispatch.Wcut]
      ring
    rw [hfun, deriv_deriv_mul_eq χ (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z hχ2 hg2]
    have hF2 := wa6 z hz
    have h1 : deriv (deriv χ) z * (z ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h2 : 2 * (deriv χ z * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z)
        ≤ 2 * |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z| := by
      have : deriv χ z * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z
          ≤ |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z| := by
        calc deriv χ z * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z
            ≤ |deriv χ z * deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z| :=
              le_abs_self _
          _ = |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z| :=
              abs_mul _ _
      nlinarith [this]
    have h3 : χ z * deriv (deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2)) z
        ≤ 6 * (χ z * (Work.Spaces.w z) ^ 2) := by
      have h := mul_le_mul_of_nonneg_left hF2 (hχnn z)
      linarith [h]
    have hF2g : Work.FTS.EllipticEst.Dispatch.AeCut.F2g χ z
        = 2 * |deriv χ z| * |deriv (fun y : ℝ => y ^ 2 * (Work.Spaces.w y) ^ 2) z|
          + |deriv (deriv χ) z| * (z ^ 2 * (Work.Spaces.w z) ^ 2) := rfl
    have hW : Work.FTS.EllipticEst.Dispatch.Wcut χ z = χ z * (Work.Spaces.w z) ^ 2 := rfl
    rw [hF2g, hW]
    linarith
  · -- `(zW)' ≥ -3W - F1g`
    intro z hz
    have hz0 : z ≠ 0 := ne_of_gt hz
    have hχ2 : ContDiffAt ℝ 2 χ z := hχsm.contDiffAt
    have hg2 : ContDiffAt ℝ 2 (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z := contDiffAt_wlin z hz0
    -- `z·Wcut χ = χ·(zw²)`
    have hfun : (fun y : ℝ => y * Work.FTS.EllipticEst.Dispatch.Wcut χ y)
        = (fun y : ℝ => χ y * (y * (Work.Spaces.w y) ^ 2)) := by
      funext y
      simp only [Work.FTS.EllipticEst.Dispatch.Wcut]
      ring
    rw [hfun]
    change deriv (χ * (fun y : ℝ => y * (Work.Spaces.w y) ^ 2)) z ≥ _
    rw [deriv_mul (hχ2.differentiableAt (by norm_num)) (hg2.differentiableAt (by norm_num))]
    have hb1 : -(Work.FTS.EllipticEst.Dispatch.AeCut.F1g χ z)
        ≤ deriv χ z * (z * (Work.Spaces.w z) ^ 2) := by
      have h := mul_le_mul_of_nonneg_right (neg_abs_le (deriv χ z))
        (by positivity : (0 : ℝ) ≤ z * (Work.Spaces.w z) ^ 2)
      have hF1 : Work.FTS.EllipticEst.Dispatch.AeCut.F1g χ z
          = |deriv χ z| * (z * (Work.Spaces.w z) ^ 2) := rfl
      rw [hF1]
      linarith [h]
    have hb2 : -(3 * (χ z * (Work.Spaces.w z) ^ 2))
        ≤ χ z * deriv (fun y : ℝ => y * (Work.Spaces.w y) ^ 2) z := by
      have h := mul_le_mul_of_nonneg_left (wa7 z hz) (hχnn z)
      linarith [h]
    have hW : Work.FTS.EllipticEst.Dispatch.Wcut χ z = χ z * (Work.Spaces.w z) ^ 2 := rfl
    rw [hW]
    linarith

end Work.FTS.EllipticEst.Dispatch
