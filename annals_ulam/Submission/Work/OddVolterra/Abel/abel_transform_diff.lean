import Mathlib
import Submission.Commons.Analysis.Abel.volterra_equivalence_full
import Submission.Commons.Analysis.Abel.volterra_double_integral
import Submission.Commons.Analysis.Abel.continuousOn_abel_K
import Submission.Work.OddVolterra.Abel.abel_fixed_interval_diff

open scoped Interval Topology
open Set Filter MeasureTheory

namespace Work.OddVolterra.Abel

set_option linter.unusedVariables false

/-- The Abel transform is differentiable at every interior point, when `Q` is continuous
up to `1` and `C²` on every `[a,b]` with `b < 1`. -/
theorem abel_transform_diff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {a : ℝ} (ha1 : a < 1) {Q : ℝ → E}
    (hQcont : ContinuousOn Q (Set.Icc a 1))
    (hQsmooth : ∀ b : ℝ, a < b → b < 1 → ContDiffOn ℝ 2 Q (Set.Icc a b)) :
    ∀ x ∈ Set.Ioo a 1,
      DifferentiableAt ℝ (fun u : ℝ => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v) x := by
  intro x hx
  have hax : a < x := hx.1
  have hx1 : x < 1 := hx.2
  -- split point
  set c : ℝ := (x + 1) / 2 with hcdef
  have hxc : x < c := by rw [hcdef]; linarith
  have hc1 : c < 1 := by rw [hcdef]; linarith
  have hac : a < c := lt_trans hax hxc
  -- the three pieces
  set A : ℝ → E := fun u => ∫ v in u..c, (Real.sqrt (v - u))⁻¹ • (Q v - Q c) with hAdef
  set B : ℝ → E := fun u => ∫ v in u..c, (Real.sqrt (v - u))⁻¹ • Q c with hBdef
  set C : ℝ → E := fun u => ∫ v in c..1, (Real.sqrt (v - u))⁻¹ • Q v with hCdef
  -- a small ball around x staying in (a, c)
  set δ : ℝ := min ((c - x) / 2) ((x - a) / 2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (by linarith) (by linarith)
  have hδcx : δ ≤ (c - x) / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδxa : δ ≤ (x - a) / 2 := by rw [hδdef]; exact min_le_right _ _
  have hUmx : ∀ u ∈ Metric.ball x δ, u < c := by
    intro u hu
    have hdist : |u - x| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hu
    have hlt : u - x < δ := (abs_lt.mp hdist).2
    have : δ < c - x := by linarith
    linarith
  have hUax : ∀ u ∈ Metric.ball x δ, a < u := by
    intro u hu
    have hdist : |u - x| < δ := by simpa [Metric.mem_ball, Real.dist_eq] using hu
    have hlt : -δ < u - x := (abs_lt.mp hdist).1
    have : δ < x - a := by linarith
    linarith
  have hQcont_c1 : ContinuousOn Q (Set.uIcc c 1) := by
    rw [Set.uIcc_of_le (le_of_lt hc1)]
    exact hQcont.mono (fun y hy => ⟨le_trans (le_of_lt hac) hy.1, hy.2⟩)
  -- the splitting identity on the ball
  have hsplit : ∀ u ∈ Metric.ball x δ,
      (∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v) = A u + (B u + C u) := by
    intro u hu
    have huc : u < c := hUmx u hu
    have hau : a < u := hUax u hu
    have hcontQ_uc : ContinuousOn Q (Set.uIcc u c) := by
      rw [Set.uIcc_of_le (le_of_lt huc)]
      exact hQcont.mono (fun y hy => ⟨le_trans (le_of_lt hau) hy.1, le_trans hy.2 (le_of_lt hc1)⟩)
    have hint1 : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • (Q v - Q c))
        volume u c :=
      (Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub huc).smul_continuousOn
        (hcontQ_uc.sub continuousOn_const)
    have hint2 : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q c) volume u c :=
      (Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub huc).smul_continuousOn
        continuousOn_const
    have hint3 : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q v) volume u c :=
      (Commons.Analysis.Abel.intervalIntegrable_invSqrt_sub huc).smul_continuousOn hcontQ_uc
    have hint4 : IntervalIntegrable (fun v : ℝ => (Real.sqrt (v - u))⁻¹ • Q v) volume c 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      have hsqrt_cont : ContinuousOn (fun v : ℝ => Real.sqrt (v - u)) (Set.uIcc c 1) :=
        Real.continuous_sqrt.comp_continuousOn (continuousOn_id.sub continuousOn_const)
      have hsqrt_ne : ∀ v ∈ Set.uIcc c 1, Real.sqrt (v - u) ≠ 0 := by
        intro v hv
        rw [Set.uIcc_of_le (le_of_lt hc1)] at hv
        exact ne_of_gt (Real.sqrt_pos_of_pos (by linarith [hv.1]))
      exact (hsqrt_cont.inv₀ hsqrt_ne).smul hQcont_c1
    have e1 : (∫ v in u..c, (Real.sqrt (v - u))⁻¹ • (Q v - Q c))
        + (∫ v in u..c, (Real.sqrt (v - u))⁻¹ • Q c)
        = ∫ v in u..c, (Real.sqrt (v - u))⁻¹ • Q v := by
      rw [← intervalIntegral.integral_add hint1 hint2]
      refine intervalIntegral.integral_congr (fun v _ => ?_)
      rw [smul_sub, sub_add_cancel]
    have e2 : (∫ v in u..c, (Real.sqrt (v - u))⁻¹ • Q v)
        + (∫ v in c..1, (Real.sqrt (v - u))⁻¹ • Q v)
        = ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v :=
      intervalIntegral.integral_add_adjacent_intervals hint3 hint4
    have key : (∫ v in u..c, (Real.sqrt (v - u))⁻¹ • (Q v - Q c))
        + ((∫ v in u..c, (Real.sqrt (v - u))⁻¹ • Q c)
            + (∫ v in c..1, (Real.sqrt (v - u))⁻¹ • Q v))
        = ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v := by
      rw [← add_assoc, e1, e2]
    rw [hAdef, hBdef, hCdef]
    exact key.symm
  -- differentiability of A
  have hA_diff : DifferentiableAt ℝ A x := by
    rw [hAdef]
    refine Commons.Analysis.Abel.differentiableAt_intervalIntegral_invSqrt_Q (E := E) hac ?_ ?_
      ⟨hax, hxc⟩
    · exact (hQsmooth c hac hc1).sub contDiffOn_const
    · simp
  -- differentiability of B
  have hB_diff : DifferentiableAt ℝ B x := by
    have hB_eq : ∀ u ∈ Metric.ball x δ, B u = (2 * Real.sqrt (c - u)) • Q c := by
      intro u hu
      have huc : u < c := hUmx u hu
      change (∫ v in u..c, (Real.sqrt (v - u))⁻¹ • Q c) = (2 * Real.sqrt (c - u)) • Q c
      rw [Commons.Analysis.Abel.intervalIntegral_abel_subst (E := E) (le_of_lt huc)
        (fun _ σ => Q c)]
      rw [intervalIntegral.integral_const]
      simp
    have hdiff_smul : DifferentiableAt ℝ (fun u : ℝ => (2 * Real.sqrt (c - u)) • Q c) x := by
      have hne : c - x ≠ 0 := by linarith
      have h1 : HasDerivAt (fun u : ℝ => c - u) (-1) x := (hasDerivAt_id x).const_sub c
      have h2 : HasDerivAt (fun u : ℝ => Real.sqrt (c - u))
          ((1 / (2 * Real.sqrt (c - x))) * (-1)) x :=
        (Real.hasDerivAt_sqrt hne).comp x h1
      have h3 : DifferentiableAt ℝ (fun u : ℝ => 2 * Real.sqrt (c - u)) x :=
        (differentiableAt_const (2 : ℝ)).mul h2.differentiableAt
      exact h3.smul (differentiableAt_const (Q c))
    exact hdiff_smul.congr_of_eventuallyEq
      (Filter.eventually_of_mem (Metric.ball_mem_nhds x hδpos) hB_eq)
  -- differentiability of C
  have hC_diff : DifferentiableAt ℝ C x := by
    rw [hCdef]
    refine abel_fixed_interval_diff hxc (le_of_lt hc1) ?_
    exact hQcont.mono (fun y hy => ⟨le_trans (le_of_lt hac) hy.1, hy.2⟩)
  -- combine
  have hABC : DifferentiableAt ℝ (fun u : ℝ => A u + (B u + C u)) x :=
    hA_diff.add (hB_diff.add hC_diff)
  have hev : (fun u : ℝ => A u + (B u + C u))
      =ᶠ[𝓝 x] (fun u : ℝ => ∫ v in u..1, (Real.sqrt (v - u))⁻¹ • Q v) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds x hδpos) (fun u hu => (hsplit u hu).symm)
  exact hABC.congr_of_eventuallyEq hev.symm

end Work.OddVolterra.Abel
