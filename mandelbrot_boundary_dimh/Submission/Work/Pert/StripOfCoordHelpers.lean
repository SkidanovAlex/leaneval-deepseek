import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.goodP_of_mem_Dphi
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.Parabolic

/-! Assembly helpers for `Work.Pert.strip_of_coord`. -/

namespace Work.Pert

open MandelDim

/-- `NearOn` is monotone in both arguments (local copy; the same statement is
`Work.Pert.nearOn_mono`). -/
lemma nearOn_mono' {f₀ f : ℂ → ℂ} {Df L L' : Set ℂ} {δ δ' : ℝ}
    (h : MandelDim.NearOn f₀ f Df L δ) (hL : L' ⊆ L) (hδ : δ ≤ δ') :
    MandelDim.NearOn f₀ f Df L' δ' :=
  ⟨h.1, hL.trans h.2.1, h.2.2.1, fun z hz => lt_of_lt_of_le (h.2.2.2 z (hL hz)) hδ⟩

/-- The band `{|Re| ≤ 1, y₁ ≤ |Im| ≤ Y}` is compact. -/
lemma isCompact_band {y₁ Y : ℝ} :
    IsCompact {w : ℂ | y₁ ≤ |w.im| ∧ |w.re| ≤ 1 ∧ |w.im| ≤ Y} := by
  have hclosed : IsClosed {w : ℂ | y₁ ≤ |w.im| ∧ |w.re| ≤ 1 ∧ |w.im| ≤ Y} := by
    refine IsClosed.inter (isClosed_le continuous_const (continuous_abs.comp Complex.continuous_im)) ?_
    refine IsClosed.inter (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const) ?_
    exact isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
  have hsub : {w : ℂ | y₁ ≤ |w.im| ∧ |w.re| ≤ 1 ∧ |w.im| ≤ Y} ⊆
      Metric.closedBall (0 : ℂ) (|Y| + 4) := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hw
    rw [Metric.mem_closedBall, dist_zero_right]
    have h4 := Complex.norm_le_abs_re_add_abs_im w
    have h5 : |w.im| ≤ |Y| := le_trans h3 (le_abs_self Y)
    have h0 : (0:ℝ) ≤ |Y| + 4 := by positivity
    calc ‖w‖ ≤ |w.re| + |w.im| := h4
      _ ≤ 1 + |Y| := by linarith
      _ ≤ |Y| + 4 := by linarith
  exact (isCompact_closedBall (0 : ℂ) (|Y| + 4)).of_isClosed_subset hclosed hsub

/-- The band is inside the datum's maximal domain (all its points have `|Im| > η₀`). -/
lemma band_sub_Dφ {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {y₁ Y : ℝ} (hy₁ : d.η₀ < y₁) :
    {w : ℂ | y₁ ≤ |w.im| ∧ |w.re| ≤ 1 ∧ |w.im| ≤ Y} ⊆ d.Dφ :=
  fun w hw => (d.ends_sub w (lt_of_lt_of_le hy₁ hw.1)).1

/-- For `α ∈ 𝓕₁` (`|Im α| < Re α`) the real part of the inverse is at least `1/(2‖α‖)`. -/
lemma inv_re_ge_of_InF1 {α : ℂ} (h : MandelDim.InF1 α) : 1 / (2 * ‖α‖) ≤ (1 / α).re := by
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) h
  have him2 : α.im ^ 2 < α.re ^ 2 := by
    have h1 : -α.re < α.im := (abs_lt.mp h).1
    have h2 : α.im < α.re := (abs_lt.mp h).2
    nlinarith
  have hval : (1 / α).re = α.re / (α.re ^ 2 + α.im ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    ring_nf
  rw [hval]
  have hden : 0 < α.re ^ 2 + α.im ^ 2 := by positivity
  have h2re : 0 < 2 * α.re := by positivity
  have hkey : (1:ℝ) / (2 * α.re) ≤ α.re / (α.re ^ 2 + α.im ^ 2) := by
    rw [div_le_div_iff₀ h2re hden]
    nlinarith
  have hle : (1:ℝ) / (2 * ‖α‖) ≤ 1 / (2 * α.re) := by
    have h3 : α.re ≤ ‖α‖ := by
      simpa using Complex.re_le_norm α
    have h4 : 2 * α.re ≤ 2 * ‖α‖ := by linarith
    exact one_div_le_one_div_of_le (by positivity) h4
  linarith

end Work.Pert
