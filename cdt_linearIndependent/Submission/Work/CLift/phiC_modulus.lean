import Mathlib
import Submission.Work.CLift.bridge
import Submission.Work.CPhi.phiC_analytic
import Submission.Work.CLift.min_modulus_dslope

/-!
# CLift: modulus bounds for `phiC = hauptH ∘ psiC` on the closed unit disc

`phiC : ℂ → ℂ` is the contour map of Theorem C (`phiC z = hauptH (psiC z)`, `psiC = -(3/4) ·
lune(23/10, ·)`, `hauptH q = -256 q ∏ₙ (1 + q^{n+1})^{24}`).  The certified numerics `hN`
(`CNumerics`) give the two boundary bounds `10⁻¹³ ≤ |phiC z| ≤ 7·10⁵` on the unit circle.  Here we
propagate them to the whole closed unit disc:

* the upper bound is the maximum modulus principle applied to the holomorphic `phiC` (holomorphic
  on the open ball by `Work.CPhi.phiC_analytic`, continuous on the closed ball because `psiC` maps
  the closed ball into `ball 0 (3/4) ⊆ ball 0 1` and `hauptH` is holomorphic there);
* the lower bound is the minimum modulus principle applied to the holomorphic function
  `z ↦ phiC z / z` (`dslope phiC 0`, holomorphic on the disc since `phiC` is, and zero-free there
  because `phiC` vanishes only at `0` and `(phiC)'(0) = -256·(-1287/2516) ≠ 0`), whose boundary
  values are `|phiC z| ≥ 10⁻¹³`; this is the general lemma `Work.CLift.min_modulus_dslope`.
-/

namespace Work.CLift

open Complex Metric Filter
open Submission.CDTPlan

/-- `phiC` is continuous on the closed unit disc: `psiC` maps it into `closedBall 0 (3/4)`, on
which `hauptH` is continuous (it is holomorphic on the larger ball `ball 0 1`). -/
theorem phiC_continuousOn_closedBall (hM : HauptFacts) (hP : PsiCFacts) :
    ContinuousOn phiC (Metric.closedBall (0 : ℂ) 1) := by
  obtain ⟨hP_cont, hP_diff, hP_zero, hP_deriv, hP_bound, hP_inj⟩ := hP
  obtain ⟨hM_diff, hM_deriv, hM_zero, _k, _hk_diff, _hk_eq⟩ := hM
  have hHcont : ContinuousOn hauptH (Metric.closedBall (0 : ℂ) (3 / 4)) := by
    apply continuousOn_of_forall_continuousAt
    intro q hq
    have hqn : ‖q‖ ≤ 3 / 4 := by simpa [mem_closedBall, dist_zero_right] using hq
    have hq1 : q ∈ Metric.ball (0 : ℂ) 1 := by
      simp only [mem_ball, dist_zero_right]; linarith
    exact (hM_diff.differentiableAt (isOpen_ball.mem_nhds hq1)).continuousAt
  have hcomp : ContinuousOn (hauptH ∘ psiC) (Metric.closedBall (0 : ℂ) 1) :=
    hHcont.comp hP_cont (fun z hz => by
      simp only [mem_closedBall, dist_zero_right] at hz ⊢
      have h := hP_bound z (by simp only [mem_closedBall, dist_zero_right]; exact hz)
      linarith)
  exact hcomp

theorem phiC_modulus (hM : HauptFacts) (hP : PsiCFacts) (hN : CNumerics) :
    (∀ z : ℂ, ‖z‖ ≤ 1 → ‖phiC z‖ ≤ 700000) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → (1 / 10 ^ 13 : ℝ) * ‖z‖ ≤ ‖phiC z‖) := by
  obtain ⟨hN_rearr, hN_bd⟩ := hN
  obtain ⟨hφdiff, hφ0, hφderiv, hψle, hφzero, _hrest⟩ := Work.CPhi.phiC_analytic hM hP
  have hφcont : ContinuousOn phiC (Metric.closedBall (0 : ℂ) 1) :=
    phiC_continuousOn_closedBall hM hP
  have hd : DiffContOnCl ℂ phiC (Metric.ball (0 : ℂ) 1) :=
    DiffContOnCl.mk_ball hφdiff hφcont
  constructor
  · -- upper bound: maximum modulus principle
    intro z hz
    have hzcl : z ∈ closure (Metric.ball (0 : ℂ) 1) := by
      rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
      simpa [mem_closedBall, dist_zero_right] using hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_ hzcl
    intro w hw
    have hwn : ‖w‖ = 1 := by
      rw [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hw
      simpa [mem_sphere_iff_norm] using hw
    exact (hN_bd w hwn).2
  · -- lower bound: minimum modulus principle via the quotient `z ↦ phiC z / z`
    have hderiv_ne : deriv phiC 0 ≠ 0 := by rw [hφderiv]; norm_num
    have hmem : Metric.closedBall (0 : ℂ) 1 ∈ nhds (0 : ℂ) :=
      Filter.mem_of_superset (Metric.ball_mem_nhds 0 one_pos) Metric.ball_subset_closedBall
    have hgc : ContinuousOn (dslope phiC (0 : ℂ)) (Metric.closedBall (0 : ℂ) 1) :=
      (continuousOn_dslope (f := phiC) (s := Metric.closedBall (0 : ℂ) 1) (a := (0 : ℂ))
        hmem).mpr ⟨hφcont, hφdiff.differentiableAt (Metric.ball_mem_nhds 0 one_pos)⟩
    have hne : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ 1 → phiC z ≠ 0 := by
      intro z hz0 hz1 hzero
      rcases lt_or_eq_of_le hz1 with hlt | heq
      · have hz_eq0 : z = 0 :=
          hφzero z (by simp only [mem_ball, dist_zero_right]; exact hlt) hzero
        rw [hz_eq0, norm_zero] at hz0
        exact lt_irrefl 0 hz0
      · have hb := (hN_bd z heq).1
        rw [hzero, norm_zero] at hb
        norm_num at hb
    have hbd : ∀ w : ℂ, ‖w‖ = 1 → (1 / 10 ^ 13 : ℝ) ≤ ‖phiC w‖ :=
      fun w hw => (hN_bd w hw).1
    exact min_modulus_dslope (c := (1 / 10 ^ 13 : ℝ)) (by norm_num) hφdiff hgc hφ0
      hderiv_ne hne hbd

end Work.CLift
