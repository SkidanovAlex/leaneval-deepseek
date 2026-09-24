import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.smoothed_properties
import Submission.Work.GM.Affine.supf_le_of_decay

open MeasureTheory

namespace Work.GM.Affine

/-- `psiSmooth` vanishes outside `|x| < 1`: its support is the ball of radius `psiBump.rOut = 1/4`. -/
lemma psiSmooth_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : psiSmooth x = 0 := by
  by_contra h
  have hmem : x ∈ Function.support (psiBump.normed (volume : Measure ℝ)) := by
    rw [Function.mem_support]
    exact h
  rw [ContDiffBump.support_normed_eq] at hmem
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hmem
  have hr : psiBump.rOut = 1 / 4 := rfl
  rw [hr] at hmem
  linarith

/-- `psiSmooth` has compact support. -/
lemma psiSmooth_hasCompactSupport : HasCompactSupport psiSmooth :=
  ContDiffBump.hasCompactSupport_normed (f := psiBump) (μ := (volume : Measure ℝ))

/-- **GM §9: the smoothing `f ↦ f̃ = smoothed psiSmooth T f` preserves the `Λ`-form of the
Fourier decay.** If `f` is continuous, nonnegative, supported in `[1/C₀, C₀]`, satisfies
`‖Fhat f ξ‖ ≤ c j ε T^ε (T/|ξ|)^j Λ` and the compatibility `Λ ≤ 16 c 2 1 T³ ∫f`, then so does
`f̃`: all the properties of `smoothed_properties`, with the *same* decay scale `Λ`. -/
theorem smoothed_lam_transfer {c : ℕ → ℝ → ℝ} {C₀ T Λ : ℝ} (hC₀ : 1 ≤ C₀) (hT : 2 * C₀ ≤ T)
    {f : ℝ → ℝ} (hf : Continuous f) (hnn : ∀ u, 0 ≤ f u) (hs : SuppHyp C₀ f)
    (hΛ : 0 < Λ)
    (hdec : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ)
    (hcompat : Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u) :
    Continuous (smoothed psiSmooth T f) ∧ (∀ u, 0 ≤ smoothed psiSmooth T f u) ∧
    SuppHyp (2 * C₀) (smoothed psiSmooth T f) ∧
    (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
      ‖Fhat (smoothed psiSmooth T f) ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) ∧
    Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, smoothed psiSmooth T f u ∧
    (∫ u, smoothed psiSmooth T f u = ∫ u, f u) ∧
    (∫ u, (smoothed psiSmooth T f u) ^ 2 ≤ ∫ u, (f u) ^ 2) := by
  obtain ⟨P1, P2, _P3, P4, P5, P6, _P7, P8⟩ :=
    smoothed_properties (ψ := psiSmooth) (f := f) (C₀ := C₀) (T := T)
      psiSmooth_contDiff.continuous psiSmooth_nonneg psiSmooth_hasCompactSupport
      psiSmooth_integral (fun x hx => psiSmooth_eq_zero_of_one_le_abs hx) hC₀ hf hnn hs hT
  refine ⟨P1, P2, P4, ?_, ?_, P5, P6⟩
  · intro j ε hε ξ hξ
    exact le_trans (P8 ξ) (hdec j ε hε ξ hξ)
  · rw [P5]
    exact hcompat

end Work.GM.Affine
