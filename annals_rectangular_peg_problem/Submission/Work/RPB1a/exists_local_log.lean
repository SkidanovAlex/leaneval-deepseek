import Mathlib
import Submission.Work.RPB1a.RMT.log_sqrt_of_primitive

namespace Work.RPB1a

open Complex Set Metric
open scoped ContDiff

/-- **A nonvanishing holomorphic function on a disk has a holomorphic logarithm.**  If `G` is
analytic and nowhere zero on the open disk `ball z₀ r`, then there is `L` holomorphic on the disk
with `L z₀ = 0` and `G z = G z₀ * exp (L z)` for every `z` in the disk.

The disk is convex, so every holomorphic function on it has a primitive (`IsExactOn` from
Morera/Goursat); hence by `Work.RPB1a.RMT.log_sqrt_of_primitive` the disk carries a logarithm of
`G`.  Shifting it by the constant `L z₀` normalises the value at the centre and absorbs the factor
`G z₀`. -/
theorem exists_local_log {G : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hG : ∀ z ∈ Metric.ball z₀ r, AnalyticAt ℂ G z) (hGne : ∀ z ∈ Metric.ball z₀ r, G z ≠ 0) :
    ∃ L : ℂ → ℂ, L z₀ = 0 ∧ DifferentiableOn ℂ L (Metric.ball z₀ r) ∧
      ∀ z ∈ Metric.ball z₀ r, G z = G z₀ * Complex.exp (L z) := by
  have hz₀ : z₀ ∈ Metric.ball z₀ r := mem_ball_self hr
  have hG0 : G z₀ ≠ 0 := hGne z₀ hz₀
  have hUo : IsOpen (Metric.ball z₀ r) := isOpen_ball
  have hUpc : IsPreconnected (Metric.ball z₀ r) := (convex_ball z₀ r).isPreconnected
  -- On a disk every holomorphic function has a primitive.
  have hprim : ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball z₀ r) →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball z₀ r) ∧
        EqOn (deriv g) f (Metric.ball z₀ r) := by
    intro f hf
    obtain ⟨g, hg⟩ := hf.isExactOn_ball
    exact ⟨g, fun z hz => (hg z hz).differentiableAt.differentiableWithinAt,
      fun z hz => (hg z hz).deriv⟩
  obtain ⟨hlog, _⟩ := RMT.log_sqrt_of_primitive hUo hUpc hprim
  have hGd : DifferentiableOn ℂ G (Metric.ball z₀ r) :=
    fun z hz => (hG z hz).differentiableAt.differentiableWithinAt
  -- A holomorphic logarithm of `G` on the disk.
  obtain ⟨L, hLd, hLeq⟩ := hlog G hGd hGne
  refine ⟨fun z => L z - L z₀, by simp, hLd.sub_const (L z₀), ?_⟩
  intro z hz
  have hLz : Complex.exp (L z) = G z := hLeq hz
  have hL0 : Complex.exp (L z₀) = G z₀ := hLeq hz₀
  rw [Complex.exp_sub, hLz, hL0]
  field_simp

end Work.RPB1a
