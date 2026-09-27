import Mathlib
import Submission.Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn

namespace Work.EQ

open Filter Metric
open scoped Topology

/-- **Holomorphic local inverse from injectivity (inverse function theorem).** -/
theorem analyticAt_local_inverse {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) (hinj : Set.InjOn g U) {υ : ℂ} (hυ : υ ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ψ : ℂ → ℂ,
      AnalyticOnNhd ℂ ψ (Metric.ball (g υ) ε) ∧ ψ (g υ) = υ ∧
      (∀ w ∈ Metric.ball (g υ) ε, g (ψ w) = w) ∧
      (∀ w ∈ Metric.ball (g υ) ε, ψ w ∈ U) := by
  -- a ball around `υ` contained in `U`
  obtain ⟨r, hr, hrU⟩ : ∃ r : ℝ, 0 < r ∧ Metric.ball υ r ⊆ U := by
    rcases Metric.mem_nhds_iff.mp (hU.mem_nhds hυ) with ⟨r, hr, hrU⟩
    exact ⟨r, hr, hrU⟩
  have hAnalυ : AnalyticAt ℂ g υ := hg υ hυ
  have hd : deriv g υ ≠ 0 :=
    Commons.Analysis.Complex.Analytic.deriv_ne_zero_of_injOn hr hAnalυ (hinj.mono hrU)
  let i : ℂ ≃L[ℂ] ℂ := .unitsEquivAut ℂ (.mk0 (deriv g υ) hd)
  have hfd : HasStrictFDerivAt g i.toContinuousLinearMap υ := hAnalυ.hasStrictDerivAt
  let e₂ : OpenPartialHomeomorph ℂ ℂ := hfd.toOpenPartialHomeomorph g
  have he₂ : (e₂ : ℂ → ℂ) = g := rfl
  have hzs : υ ∈ e₂.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hfd
  have hzt : g υ ∈ e₂.target := by rw [← he₂]; exact e₂.map_source hzs
  have hy : e₂.symm (g υ) = υ := by rw [← he₂]; exact e₂.left_inv hzs
  have hr_an : AnalyticAt ℂ (e₂.symm : ℂ → ℂ) (g υ) := by
    refine OpenPartialHomeomorph.analyticAt_symm (f := e₂) (a := g υ) (i := i) hzt ?_ ?_
    · rw [hy, he₂]; exact hAnalυ
    · rw [hy, he₂]; exact hfd.hasFDerivAt.fderiv
  obtain ⟨ρ, hρpos, hρan⟩ := hr_an.exists_ball_analyticOnNhd
  -- shrink to a ball contained in the target and on which the inverse lands in `U`
  have hcontψ : ContinuousAt (e₂.symm : ℂ → ℂ) (g υ) :=
    e₂.symm.continuousAt (by rw [OpenPartialHomeomorph.symm_source]; exact hzt)
  have hUψ : (e₂.symm : ℂ → ℂ) ⁻¹' U ∈ 𝓝 (g υ) :=
    hcontψ.preimage_mem_nhds (hU.mem_nhds (by rw [hy]; exact hυ))
  have htarget : e₂.target ∈ 𝓝 (g υ) := e₂.open_target.mem_nhds hzt
  have hball : Metric.ball (g υ) ρ ∩ e₂.target ∩ (e₂.symm : ℂ → ℂ) ⁻¹' U ∈ 𝓝 (g υ) :=
    Filter.inter_mem (Filter.inter_mem (Metric.ball_mem_nhds (g υ) hρpos) htarget) hUψ
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hball
  refine ⟨ε, hεpos, (e₂.symm : ℂ → ℂ), ?_, ?_, ?_, ?_⟩
  · exact hρan.mono fun w hw => (hεsub hw).1.1
  · exact hy
  · intro w hw
    have hwt : w ∈ e₂.target := (hεsub hw).1.2
    have : e₂ (e₂.symm w) = w := e₂.right_inv hwt
    rw [← he₂]; exact this
  · intro w hw
    exact (hεsub hw).2

end Work.EQ
