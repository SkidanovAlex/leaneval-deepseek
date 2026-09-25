/-
The Beltrami coefficient of a `C^∞` field of complex structures is `C^∞` on a small ball.
-/
import Mathlib
import Submission.Work.Beltrami.Defs

noncomputable section

namespace Work.Beltrami

open scoped ContDiff Topology

/-- If a field of real-linear endomorphisms `J` is `C^∞` on the ball of radius `ρ` about `0`
and `J 0` is the standard structure, then on some smaller ball the Beltrami coefficient
`z ↦ beltramiCoeff (J z)` is `C^∞` and the denominator `1 + i·conj (J z 1)` is non-zero. -/
theorem beltramiCoeff_contDiffOn {J : ℂ → ℂ →L[ℝ] ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hJs : ContDiffOn ℝ ∞ J (Metric.ball 0 ρ)) (hJ0 : J 0 = JstdC 0) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧
      ContDiffOn ℝ ∞ (fun z => beltramiCoeff (J z)) (Metric.ball 0 ρ') ∧
      (∀ z ∈ Metric.ball 0 ρ', 1 + Complex.I * star (J z 1) ≠ 0) := by
  have hg : ContDiffOn ℝ ∞ (fun z : ℂ => (J z) 1) (Metric.ball 0 ρ) := by
    have h : ContDiff ℝ ∞ (fun L : ℂ →L[ℝ] ℂ => L 1) :=
      (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).contDiff
    simpa [Function.comp_def] using h.comp_contDiffOn hJs
  have hmul : ContDiff ℝ ∞ (fun t : ℂ => Complex.I * t) :=
    (Complex.I • (1 : ℂ →L[ℝ] ℂ)).contDiff
  have hstar : ContDiff ℝ ∞ (fun t : ℂ => star t) := by
    rw [show (fun t : ℂ => star t) = ⇑Complex.conjCLE from
      funext (fun t => by rw [Complex.conjCLE_apply, starRingEnd_apply])]
    exact Complex.conjCLE.contDiff
  have hν0 : (fun z : ℂ => 1 + Complex.I * star (J z 1)) 0 ≠ 0 := by
    have h01 : J 0 1 = Complex.I := by rw [hJ0, JstdC_apply]; ring
    show 1 + Complex.I * star (J 0 1) ≠ 0
    rw [h01]
    have hstarI : star Complex.I = -Complex.I := by
      rw [← starRingEnd_apply]; exact Complex.conj_I
    rw [hstarI, mul_neg, Complex.I_mul_I]
    norm_num
  have hcont : ContinuousAt (fun z : ℂ => 1 + Complex.I * star (J z 1)) 0 := by
    have hJc : ContinuousAt (fun z : ℂ => J z) 0 :=
      (hJs.contDiffAt (Metric.ball_mem_nhds 0 hρ)).continuousAt
    have hgc : ContinuousAt (fun z : ℂ => (J z) 1) 0 :=
      ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.continuousAt).comp hJc
    exact continuousAt_const.add
      (ContinuousAt.const_mul ((continuous_star.continuousAt).comp hgc) Complex.I)
  obtain ⟨r, hr, hνr⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually_ne hν0)
  refine ⟨min ρ r, lt_min hρ hr, min_le_left _ _, ?_, ?_⟩
  · have hsub : Metric.ball (0 : ℂ) (min ρ r) ⊆ Metric.ball 0 ρ :=
      Metric.ball_subset_ball (min_le_left _ _)
    have hg' : ContDiffOn ℝ ∞ (fun z : ℂ => (J z) 1) (Metric.ball 0 (min ρ r)) :=
      hg.mono hsub
    have hnum : ContDiffOn ℝ ∞ (fun z : ℂ => -(1 + Complex.I * (J z 1)))
        (Metric.ball 0 (min ρ r)) :=
      (contDiffOn_const.add (hmul.comp_contDiffOn hg')).neg
    have hden : ContDiffOn ℝ ∞ (fun z : ℂ => 1 + Complex.I * star (J z 1))
        (Metric.ball 0 (min ρ r)) :=
      contDiffOn_const.add ((hmul.comp hstar).comp_contDiffOn hg')
    have hne : ∀ z ∈ Metric.ball (0:ℂ) (min ρ r),
        (fun z : ℂ => 1 + Complex.I * star (J z 1)) z ≠ 0 :=
      fun z hz => hνr (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _))
    have hinv : ContDiffOn ℝ ∞ (fun z : ℂ => (1 + Complex.I * star (J z 1))⁻¹)
        (Metric.ball 0 (min ρ r)) := hden.inv hne
    have hm := hnum.mul hinv
    simpa only [beltramiCoeff, div_eq_mul_inv] using hm
  · intro z hz
    exact hνr (lt_of_lt_of_le (Metric.mem_ball.mp hz) (min_le_right _ _))

end Work.Beltrami
