import Mathlib
import Submission.Work.Drive.EpsForm.goodHeight_exists

namespace Work.Drive.Mono.Band

/-- A `C²` function on the plane all of whose critical points are nondegenerate has only finitely
many critical points in any compact set.  (Generalisation of
`Work.Drive.EpsForm.finite_critSet_box`, which treats the square `[0,2π]²`, to an arbitrary compact
set; the proof is the same: nondegenerate critical points are isolated, and a closed discrete subset
of a compact set is finite.) -/
theorem finite_critSet_isCompact {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hnd : ∀ p : ℝ × ℝ, fderiv ℝ g p = 0 →
      Function.Injective (fderiv ℝ (fderiv ℝ g) p)) {K : Set (ℝ × ℝ)} (hK : IsCompact K) :
    (K ∩ {p : ℝ × ℝ | fderiv ℝ g p = 0}).Finite := by
  have h4 := Work.Drive.EpsForm.eventually_eq_of_crit_nondegen hg hnd
  have hcont : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hC : IsClosed {p : ℝ × ℝ | fderiv ℝ g p = 0} := by
    have h : {p : ℝ × ℝ | fderiv ℝ g p = 0} = (fderiv ℝ g) ⁻¹' {0} := rfl
    rw [h]; exact isClosed_singleton.preimage hcont
  have hcomp : IsCompact (K ∩ {p : ℝ × ℝ | fderiv ℝ g p = 0}) := hK.inter_right hC
  have hdisj : IsDiscrete (K ∩ {p : ℝ × ℝ | fderiv ℝ g p = 0}) := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro y hy
    have hyC : fderiv ℝ g y = 0 := hy.2
    obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp (h4 y hyC)
    refine ⟨Metric.ball y ε, Metric.isOpen_ball, ?_⟩
    ext z
    constructor
    · rintro ⟨hzball, hzmem⟩
      have hzC : fderiv ℝ g z = 0 := hzmem.2
      have : z = y := hεP hzball hzC
      simp [this]
    · rintro hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨Metric.mem_ball_self hε, hy⟩
  exact hcomp.finite hdisj

end Work.Drive.Mono.Band
