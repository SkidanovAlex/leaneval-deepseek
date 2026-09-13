import Mathlib
import Submission.Commons.Analysis.Harmonic.exists_harmonicOn_ball_eqOn_sphere
import Submission.Commons.Analysis.Harmonic.le_setAverage_ball_of_laplacian_nonneg_of_isOpen
import Submission.Commons.Analysis.Harmonic.integral_laplacian_nonneg_of_ball_meanValue_cs
import Submission.Commons.Analysis.Measure.Integral.poissonIntegral_tendsto_boundary
import Submission.Commons.Analysis.Measure.Integral.poissonIntegral_const_eq_one
import Submission.Commons.Analysis.Calculus.Laplacian.le_of_le_on_sphere_of_laplacian_nonneg_nontrivial
import Submission.Commons.Analysis.Harmonic.le_of_subMVP_closedBall
import Submission.Commons.Analysis.Harmonic.contDiffOn_top_pExt

open MeasureTheory Metric Set Filter Function
open scoped Topology RealInnerProductSpace InnerProductSpace BigOperators ENNReal

noncomputable section
namespace Commons.Analysis.Harmonic

variable {n : ℕ}

/-- The Poisson integral of continuous boundary data is analytic, harmonic and has those
boundary values (in the sense of having continuous extension). -/
theorem pExt_props (hn : 0 < n) {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : ContinuousOn g (Metric.sphere c R)) :
    ContDiffOn ℝ ⊤ (Commons.Analysis.Harmonic.pExt n c R g) (Metric.ball c R) ∧
      (∀ x ∈ Metric.ball c R, Laplacian.laplacian (Commons.Analysis.Harmonic.pExt n c R g) x = 0) := by
  refine ⟨contDiffOn_top_pExt hn hR hg, ?_⟩
  have h := (Commons.Analysis.Calculus.Laplacian.contDiffOn_two_poissonIntegral hn hR g hg).2
  intro x hx
  convert h x hx using 2
  funext u
  simp only [Commons.Analysis.Harmonic.pExt, Commons.Analysis.Harmonic.pKern,
    Commons.Analysis.Harmonic.sphereArea]


theorem local_step (hn : 0 < n) {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hcont : ContinuousOn v (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hmvp : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, ∀ r : ℝ, 0 < r →
      Metric.closedBall x r ⊆ Metric.ball 0 1 → v x = ⨍ y in Metric.ball x r, v y)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    (R : ℝ) (hRdef : R = (1 - ‖x₀‖) / 2) :
    ContDiffOn ℝ ⊤ v (Metric.ball x₀ R) ∧
      ∀ x ∈ Metric.ball x₀ R, Laplacian.laplacian v x = 0 := by
  have hx0lt : ‖x₀‖ < 1 := by simpa [mem_ball, dist_eq_norm, sub_zero] using hx₀
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRsub : Metric.closedBall x₀ R ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball, dist_eq_norm, sub_zero]
    have h1 : ‖y‖ ≤ ‖y - x₀‖ + ‖x₀‖ := by
      simpa [dist_eq_norm, sub_zero] using dist_triangle y x₀ 0
    have h2 : ‖y - x₀‖ ≤ R := hy
    rw [hRdef] at h2
    linarith
  have hsphere_sub : Metric.sphere x₀ R ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
    fun y hy => hRsub (Metric.sphere_subset_closedBall hy)
  have hg : ContinuousOn v (Metric.sphere x₀ R) := hcont.mono hsphere_sub
  -- The Poisson integral of `v` on `sphere x₀ R`.
  have hp := pExt_props (n := n) hn hRpos hg
  -- mass identity
  have hmass : ∀ x ∈ Metric.ball x₀ R,
      Commons.Analysis.Harmonic.pExt n x₀ R (fun _ => (1 : ℝ)) x = 1 := by
    have hmain1 := Commons.Analysis.Calculus.Laplacian.contDiffOn_two_poissonIntegral hn hRpos
      (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))
      (continuousOn_const : ContinuousOn (fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ))
        (Metric.sphere x₀ R))
    have h := Commons.Analysis.Measure.Integral.poissonIntegral_const_eq_one hn hRpos (c := x₀)
      (by simpa using hmain1.1) (by simpa using hmain1.2)
    intro x hx
    simpa [Commons.Analysis.Harmonic.pExt, Commons.Analysis.Harmonic.pKern,
      Commons.Analysis.Harmonic.sphereArea] using h x hx
  -- boundary values of the Poisson integral
  have hbd : ∀ y ∈ Metric.sphere x₀ R, ∀ ε > 0, ∃ δ > 0,
      ∀ x : EuclideanSpace ℝ (Fin n), ‖x - x₀‖ < R → ‖x - y‖ < δ →
        |Commons.Analysis.Harmonic.pExt n x₀ R v x - v y| < ε := by
    intro y hy ε hε
    obtain ⟨δ, hδ, hδp⟩ :=
      Commons.Analysis.Measure.Integral.poissonIntegral_tendsto_boundary hn hRpos v hg
        (by
          intro x hx
          simpa [Commons.Analysis.Harmonic.pExt, Commons.Analysis.Harmonic.pKern,
            Commons.Analysis.Harmonic.sphereArea] using hmass x hx)
        y hy ε hε
    exact ⟨δ, hδ, fun x hxc hxy => by
      simpa [Commons.Analysis.Harmonic.pExt, Commons.Analysis.Harmonic.pKern,
        Commons.Analysis.Harmonic.sphereArea] using hδp x hxc hxy⟩
  set h : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => if ‖x - x₀‖ < R then Commons.Analysis.Harmonic.pExt n x₀ R v x else v x with hhdef
  have hh_analytic : ContDiffOn ℝ ⊤ h (Metric.ball x₀ R) := by
    refine (contDiffOn_congr (f := Commons.Analysis.Harmonic.pExt n x₀ R v) (f₁ := h) ?_).mpr hp.1
    intro x hx
    simp only [hhdef]
    rw [if_pos (by simpa [mem_ball, dist_eq_norm] using hx)]
  have hh_lap : ∀ x ∈ Metric.ball x₀ R, Laplacian.laplacian h x = 0 := by
    intro x hx
    have heq : h =ᶠ[𝓝 x] Commons.Analysis.Harmonic.pExt n x₀ R v := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      simp only [hhdef]
      rw [if_pos (by simpa [mem_ball, dist_eq_norm] using hy)]
    rw [(_root_.InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds, hp.2 x hx]
  have hh_bd : ∀ y ∈ Metric.sphere x₀ R, h y = v y := by
    intro y hy
    simp only [hhdef]
    rw [if_neg]
    rw [mem_sphere, dist_eq_norm] at hy
    rw [hy]; exact lt_irrefl R
  have hh_c2 : ContDiffOn ℝ 2 h (Metric.ball x₀ R) := hh_analytic.of_le le_top
  have hh_cont : ContinuousOn h (Metric.closedBall x₀ R) := by
    intro x hx
    by_cases hxc : ‖x - x₀‖ < R
    · have hxb : x ∈ Metric.ball x₀ R := by simpa [mem_ball, dist_eq_norm] using hxc
      have hpcont : ContinuousAt (Commons.Analysis.Harmonic.pExt n x₀ R v) x :=
        hp.1.continuousOn.continuousAt (isOpen_ball.mem_nhds hxb)
      have hv : h =ᶠ[𝓝 x] Commons.Analysis.Harmonic.pExt n x₀ R v := by
        filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
        simp only [hhdef]
        rw [if_pos (by simpa [mem_ball, dist_eq_norm] using hy)]
      exact (hpcont.congr_of_eventuallyEq hv).continuousWithinAt
    · have hxR : ‖x - x₀‖ = R := by
        have hle : ‖x - x₀‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hx
        exact le_antisymm hle (le_of_not_gt hxc)
      rw [continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ₁, hδ₁, hδ₁p⟩ := hbd x (by simpa [mem_sphere, dist_eq_norm] using hxR) ε hε
      obtain ⟨δ₂, hδ₂, hδ₂p⟩ :=
        continuousWithinAt_iff.mp (hg x (by simpa [mem_sphere, dist_eq_norm] using hxR)) ε hε
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
      intro y hy hxy
      have hxy₁ : dist y x < δ₁ := lt_of_lt_of_le hxy (min_le_left _ _)
      have hxy₂ : dist y x < δ₂ := lt_of_lt_of_le hxy (min_le_right _ _)
      have hyc : ‖y - x₀‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hy
      have hxval : h x = v x := by
        simp only [hhdef]; rw [if_neg hxc]
      by_cases hyc' : ‖y - x₀‖ < R
      · have : |h y - v x| < ε := by
          simp only [hhdef]; rw [if_pos hyc']
          exact hδ₁p y hyc' (by simpa [dist_eq_norm] using hxy₁)
        simpa [hxval, Real.dist_eq] using this
      · have hyR : ‖y - x₀‖ = R := le_antisymm hyc (le_of_not_gt hyc')
        have : |h y - v x| < ε := by
          simp only [hhdef]; rw [if_neg hyc']
          have h := hδ₂p (x := y) (by simpa [mem_sphere, dist_eq_norm] using hyR)
            (by simpa [dist_eq_norm] using hxy₂)
          simpa [Real.dist_eq] using h
        simpa [hxval, Real.dist_eq] using this
  have hh_mvp : ∀ x ∈ Metric.ball x₀ R, ∀ r : ℝ, 0 < r →
      Metric.closedBall x r ⊆ Metric.ball x₀ R → h x = ⨍ y in Metric.ball x r, h y := by
    intro x hx r hr hsub
    have h1 := Commons.Analysis.Harmonic.le_setAverage_ball_of_laplacian_nonneg_of_isOpen
      isOpen_ball hh_c2 (fun z hz => by rw [hh_lap z hz]) hr hsub
    have hc2neg : ContDiffOn ℝ 2 (fun z => -h z) (Metric.ball x₀ R) := hh_c2.neg
    have h2 := Commons.Analysis.Harmonic.le_setAverage_ball_of_laplacian_nonneg_of_isOpen
      isOpen_ball hc2neg (fun z hz => by
        have hlapneg : Laplacian.laplacian (fun z => -h z) z = -Laplacian.laplacian h z := by
          have h1 : Laplacian.laplacian (fun z => -h z) = Laplacian.laplacian (-h) := rfl
          rw [h1, InnerProductSpace.laplacian_neg]
          rfl
        rw [hlapneg, hh_lap z hz, neg_zero]) hr hsub
    have h2' : -h x ≤ -(⨍ y in Metric.ball x r, h y) := by
      have havg : (⨍ y in Metric.ball x r, -h y) = -(⨍ y in Metric.ball x r, h y) :=
        average_neg (Measure.restrict volume (Metric.ball x r)) h
      rw [← havg]; exact h2
    linarith
  have hv_mvp : ∀ x ∈ Metric.ball x₀ R, ∀ r : ℝ, 0 < r →
      Metric.closedBall x r ⊆ Metric.ball x₀ R → v x = ⨍ y in Metric.ball x r, v y := by
    intro x hx r hr hsub
    have hx1 : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      hRsub (Metric.ball_subset_closedBall hx)
    exact hmvp x hx1 r hr (hsub.trans (Metric.ball_subset_closedBall.trans hRsub))
  -- The difference `v - h` satisfies the sub-mean-value property.
  have hw_cont : ContinuousOn (fun y => v y - h y) (Metric.closedBall x₀ R) :=
    (hcont.mono hRsub).sub hh_cont
  have hw_sub : ∀ y ∈ Metric.ball x₀ R, ∀ r : ℝ, 0 < r →
      Metric.closedBall y r ⊆ Metric.ball x₀ R →
      (v y - h y) ≤ ⨍ z in Metric.ball y r, (v z - h z) := by
    intro y hy r hr hsuby
    have hvc := hv_mvp y hy r hr hsuby
    have hhc := hh_mvp y hy r hr hsuby
    have hsub1 : Metric.closedBall y r ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      hsuby.trans (Metric.ball_subset_closedBall.trans hRsub)
    have hiv : IntegrableOn v (Metric.ball y r) volume :=
      ((hcont.mono hsub1).integrableOn_compact (isCompact_closedBall y r)).mono_set
        Metric.ball_subset_closedBall
    have hih : IntegrableOn h (Metric.ball y r) volume :=
      ((hh_cont.mono (hsuby.trans Metric.ball_subset_closedBall)).integrableOn_compact
        (isCompact_closedBall y r)).mono_set Metric.ball_subset_closedBall
    have havg := Commons.Analysis.Harmonic.setAverage_sub_real hiv hih
    rw [hvc, hhc, havg]
  have hw_cont' : ContinuousOn (fun y => h y - v y) (Metric.closedBall x₀ R) :=
    hh_cont.sub (hcont.mono hRsub)
  have hw_sub' : ∀ y ∈ Metric.ball x₀ R, ∀ r : ℝ, 0 < r →
      Metric.closedBall y r ⊆ Metric.ball x₀ R →
      (h y - v y) ≤ ⨍ z in Metric.ball y r, (h z - v z) := by
    intro y hy r hr hsuby
    have hvc := hv_mvp y hy r hr hsuby
    have hhc := hh_mvp y hy r hr hsuby
    have hsub1 : Metric.closedBall y r ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 :=
      hsuby.trans (Metric.ball_subset_closedBall.trans hRsub)
    have hiv : IntegrableOn v (Metric.ball y r) volume :=
      ((hcont.mono hsub1).integrableOn_compact (isCompact_closedBall y r)).mono_set
        Metric.ball_subset_closedBall
    have hih : IntegrableOn h (Metric.ball y r) volume :=
      ((hh_cont.mono (hsuby.trans Metric.ball_subset_closedBall)).integrableOn_compact
        (isCompact_closedBall y r)).mono_set Metric.ball_subset_closedBall
    have havg := Commons.Analysis.Harmonic.setAverage_sub_real hih hiv
    rw [hhc, hvc, havg]
  have key : ∀ x ∈ Metric.ball x₀ R, v x = h x := by
    intro x hx
    have hclosed : x ∈ Metric.closedBall x₀ R := Metric.ball_subset_closedBall hx
    have hm1 := Commons.Analysis.Harmonic.le_of_subMVP_closedBall hn (c := x₀) (R := R) (A := 0) hRpos hw_cont hw_sub
      (fun y hy => by rw [hh_bd y hy, sub_self])
    have hm1' := Commons.Analysis.Harmonic.le_of_subMVP_closedBall hn (c := x₀) (R := R) (A := 0) hRpos hw_cont' hw_sub'
      (fun y hy => by rw [hh_bd y hy, sub_self])
    have h1 := hm1 x hclosed
    have h2 := hm1' x hclosed
    linarith
  refine ⟨?_, ?_⟩
  · refine (contDiffOn_congr (f := h) (f₁ := v) ?_).mpr hh_analytic
    intro x hx
    exact key x hx
  · intro x hx
    have heq : v =ᶠ[𝓝 x] h := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact key y hy
    rw [(_root_.InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds, hh_lap x hx]

theorem mvp_contDiff_harmonic {n : ℕ} (hn : 0 < n) {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hcont : ContinuousOn v (Metric.ball 0 1))
    (hmvp : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1, ∀ r : ℝ, 0 < r →
      Metric.closedBall x r ⊆ Metric.ball 0 1 → v x = ⨍ y in Metric.ball x r, v y) :
    ContDiffOn ℝ ⊤ v (Metric.ball 0 1) ∧
      ∀ x ∈ Metric.ball 0 1, Laplacian.laplacian v x = 0 := by
  have hstep : ∀ x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      (ContDiffOn ℝ ⊤ v (Metric.ball x ((1 - ‖x‖) / 2)) ∧
        ∀ y ∈ Metric.ball x ((1 - ‖x‖) / 2), Laplacian.laplacian v y = 0) := by
    intro x hx
    exact local_step hn hcont hmvp x hx ((1 - ‖x‖) / 2) rfl
  constructor
  · intro x hx
    have hxmem : x ∈ Metric.ball x ((1 - ‖x‖) / 2) := by
      rw [mem_ball, dist_self]
      have : ‖x‖ < 1 := by simpa [mem_ball, dist_eq_norm, sub_zero] using hx
      linarith
    exact ((hstep x hx).1.contDiffAt (isOpen_ball.mem_nhds hxmem)).contDiffWithinAt
  · intro x hx
    have hxmem : x ∈ Metric.ball x ((1 - ‖x‖) / 2) := by
      rw [mem_ball, dist_self]
      have : ‖x‖ < 1 := by simpa [mem_ball, dist_eq_norm, sub_zero] using hx
      linarith
    exact (hstep x hx).2 x hxmem

end Commons.Analysis.Harmonic
