import Mathlib
import Submission.Work.Drive.weakcase_deps
import Submission.Work.Drive.unitPolePlan
import Submission.Work.Drive.unitPoleSuperharmonic
import Submission.Work.Drive.log_div_le_inv_mul_neg_log
import Submission.Work.Drive.inv_mul_neg_log_add_log_le

namespace Work.Drive

/-! # The member of the sweep family with a unit logarithmic pole

`Work.Drive.unitPoleMember` produces, from a holomorphic `h : X → ℂ` bounded by `1` and vanishing
at `y` together with the local factorization `h ∘ c.symm = (· - a)^k · ψ` (with `m ≤ ‖ψ‖ ≤ M` on
the chart ball of radius `r`), a member `v` of the sweep family of the clamped logarithmic barrier
`greenBarrier y ρ` which is bounded by `log (1/‖c · - a‖) + C` on the chart ball of radius `ρ`.

The witness is the function obtained by pasting `-(1/k) log ‖h‖` on `chartBall c a ρ` to the
clamped potential `clampedLogNorm h K` outside, with the clamp constant
`K = max 0 (-log ((ρ/2)^k m))` chosen so that the two pieces agree in a neighbourhood of the
pasting sphere `‖c z - a‖ = ρ`. -/

theorem unitPoleMember {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {y : X} {h : X → ℂ}
    (hhol : Submission.HolomorphicOnX h Set.univ) (hb : ∀ x : X, ‖h x‖ ≤ 1) (hy0 : h y = 0)
    {ρ r : ℝ} {k : ℕ} {ψ : ℂ → ℂ} {M m : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hk : 1 ≤ k) (hM : 1 ≤ M) (hm : 0 < m) (hmM : m ≤ M)
    (hsub : Metric.closedBall ((chartAt ℂ y) y) r ⊆ (chartAt ℂ y).target)
    (hMρ : M * ρ ^ k ≤ 1)
    (hfac : ∀ w : ℂ, dist w ((chartAt ℂ y) y) < r →
        (h ∘ (chartAt ℂ y).symm) w = (w - (chartAt ℂ y) y) ^ k * ψ w)
    (hψ : ∀ w : ℂ, dist w ((chartAt ℂ y) y) < r → m ≤ ‖ψ w‖ ∧ ‖ψ w‖ ≤ M) :
    ∃ (v : X → ℝ) (C : ℝ),
      v ∈ Submission.sweepFamily (Submission.greenBarrier y ρ) (Set.univ \ {y}) ∧
      ∀ x : X, x ∈ Submission.chartBall (chartAt ℂ y) ((chartAt ℂ y) y) ρ → x ≠ y →
        v x + Real.log ‖(chartAt ℂ y) x - (chartAt ℂ y) y‖ ≤ C := by
  classical
  let c : OpenPartialHomeomorph X ℂ := chartAt ℂ y
  let a : ℂ := c y
  let K : ℝ := max 0 (-(Real.log ((ρ / 2) ^ k * m)))
  let v : X → ℝ := fun z => if z ∈ Submission.chartBall c a ρ
      then (1 / (k : ℝ)) * (-Real.log ‖h z‖)
      else (1 / (k : ℝ)) * Work.SimplyConnected.ABS.clampedLogNorm h K z
  refine ⟨v, -(1 / (k : ℝ)) * Real.log m, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · -- superharmonicity of the pasted function on `X \ {y}`
      exact unitPoleSuperharmonic (y := y) (h := h) hhol hρ hρr hk hm hsub hfac
        (fun w hw => (hψ w hw).1)
    · -- domination of the clamped logarithmic barrier
      intro x hxU
      have hxne : x ≠ y := by simpa using hxU.2
      by_cases hxB : x ∈ Submission.chartBall c a ρ
      · have hxsrc : x ∈ c.source := hxB.1
        have hlt : ‖c x - a‖ < ρ := by
          have h1 : c x ∈ Metric.ball a ρ := hxB.2
          rwa [Metric.mem_ball, dist_eq_norm] at h1
        have hcne : c x ≠ a := by
          intro hcon
          have hcy : c y = a := rfl
          exact hxne (c.injOn hxsrc (mem_chart_source ℂ y) (by rw [hcon, hcy]))
        have hdpos : 0 < ‖c x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcne)
        have hdistr : dist (c x) a < r := by
          rw [dist_eq_norm]; exact lt_of_lt_of_le hlt hρr
        have hfacx : h x = (c x - a) ^ k * ψ (c x) := by
          have h1 : h (c.symm (c x)) = (c x - a) ^ k * ψ (c x) := by
            have h2 := hfac (c x) hdistr
            rw [Function.comp_apply] at h2
            exact h2
          rwa [c.left_inv hxsrc] at h1
        have hnorm : ‖h x‖ = ‖c x - a‖ ^ k * ‖ψ (c x)‖ := by
          rw [hfacx, norm_mul, norm_pow]
        have hsx : 0 < ‖ψ (c x)‖ := lt_of_lt_of_le hm (hψ (c x) hdistr).1
        have hvx : v x = (1 / (k : ℝ)) * (-Real.log ‖h x‖) := if_pos hxB
        have hgb : Submission.greenBarrier y ρ x = Real.log (ρ / ‖c x - a‖) := by
          rw [Submission.greenBarrier_apply]
          exact Submission.chartLogClamp_of_mem hxB
        rw [hgb, hvx]
        have h1 := log_div_le_inv_mul_neg_log hρ hdpos hsx hk (hψ (c x) hdistr).2 hMρ
        rw [← hnorm] at h1
        exact h1
      · have hvx : v x = (1 / (k : ℝ)) * Work.SimplyConnected.ABS.clampedLogNorm h K x :=
          if_neg hxB
        have hgb : Submission.greenBarrier y ρ x = 0 := by
          rw [Submission.greenBarrier_apply]
          exact Submission.chartLogClamp_of_not_mem hxB
        rw [hgb, hvx]
        have hKnn : 0 ≤ K := le_max_left _ _
        have h1 : 0 ≤ Work.SimplyConnected.ABS.clampedLogNorm h K x :=
          Work.SimplyConnected.ABS.clampedLogNorm_nonneg hKnn hb x
        have h2 : 0 ≤ (1 / (k : ℝ)) := by positivity
        exact mul_nonneg h2 h1
  · -- the unit logarithmic pole
    intro x hxball hxne
    have hxB : x ∈ Submission.chartBall c a ρ := hxball
    have hxsrc : x ∈ c.source := hxB.1
    have hlt : ‖c x - a‖ < ρ := by
      have h1 : c x ∈ Metric.ball a ρ := hxB.2
      rwa [Metric.mem_ball, dist_eq_norm] at h1
    have hcne : c x ≠ a := by
      intro hcon
      have hcy : c y = a := rfl
      exact hxne (c.injOn hxsrc (mem_chart_source ℂ y) (by rw [hcon, hcy]))
    have hdpos : 0 < ‖c x - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hcne)
    have hdistr : dist (c x) a < r := by
      rw [dist_eq_norm]; exact lt_of_lt_of_le hlt hρr
    have hfacx : h x = (c x - a) ^ k * ψ (c x) := by
      have h1 : h (c.symm (c x)) = (c x - a) ^ k * ψ (c x) := by
        have h2 := hfac (c x) hdistr
        rw [Function.comp_apply] at h2
        exact h2
      rwa [c.left_inv hxsrc] at h1
    have hnorm : ‖h x‖ = ‖c x - a‖ ^ k * ‖ψ (c x)‖ := by
      rw [hfacx, norm_mul, norm_pow]
    have hvx : v x = (1 / (k : ℝ)) * (-Real.log ‖h x‖) := if_pos hxB
    rw [hvx]
    have h1 := inv_mul_neg_log_add_log_le (d := ‖c x - a‖) (s := ‖ψ (c x)‖) (m := m)
      hdpos hm (hψ (c x) hdistr).1 hk
    rw [← hnorm] at h1
    exact h1

end Work.Drive
