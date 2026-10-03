import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.invFunOn_differentiableOn

/-!
# `Work.Repel.exists_piExp_lift`

The projection `π = piExp w = exp (2πi w)` is a covering map `ℂ → ℂ \ {0}` with deck group `ℤ`
acting by `w ↦ w + 1`.  Its restriction to an **open** ball of radius `≤ 1/2` is therefore
injective: two points `w₁, w₂` of such a ball satisfy `‖w₁ - w₂‖ < 2ρ ≤ 1`, and `π w₁ = π w₂`
forces `w₁ - w₂ ∈ ℤ`, whence `w₁ = w₂`.

Consequently, if a holomorphic `f` on an open set `V` admits, above every `v ∈ V`, a lift in a
fixed ball `ball a ρ₀` with `ρ₀ ≤ 1/2`, then the lift is unique there and — being the composition
of `f` with the (holomorphic) inverse branch of `π` on that ball — is again holomorphic on `V`.
This is the §6 ingredient that lets a return-map picture be lifted to the linearising coordinate.
-/

namespace Work.Repel

open Complex Set Metric

/-- **`π` is injective on an open ball of radius `≤ 1/2`.** -/
lemma piExp_injOn_ball_lift {a : ℂ} {ρ : ℝ} (hρ : ρ ≤ 1 / 2) :
    Set.InjOn MandelDim.piExp (Metric.ball a ρ) := by
  intro w1 h1 w2 h2 hEq
  have hE : Complex.exp (2 * Real.pi * I * w1) = Complex.exp (2 * Real.pi * I * w2) := hEq
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hE
  have hne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hw : w1 - w2 = (n : ℂ) := by
    have hn' : (2 * Real.pi * I) * w1 = (2 * Real.pi * I) * (w2 + n) := by
      rw [hn]; ring
    have := mul_left_cancel₀ hne hn'
    rw [this]; ring
  have h1' : ‖w1 - a‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using h1
  have h2' : ‖w2 - a‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using h2
  have h3 : ‖w1 - w2‖ < 1 := by
    have hsub : w1 - w2 = (w1 - a) - (w2 - a) := by ring
    have hle : ‖w1 - w2‖ ≤ ‖w1 - a‖ + ‖w2 - a‖ := by
      rw [hsub]; exact norm_sub_le _ _
    linarith
  have h4 : |(n : ℝ)| < 1 := by
    have : ‖(n : ℂ)‖ < 1 := by rw [← hw]; exact h3
    rwa [Complex.norm_intCast] at this
  have hn0 : n = 0 := by
    have h' : |n| < 1 := by
      rw [← Int.cast_lt (R := ℝ), Int.cast_abs, Int.cast_one]
      simpa using h4
    exact Int.abs_lt_one_iff.mp h'
  have : w1 - w2 = 0 := by rw [hw, hn0]; simp
  exact sub_eq_zero.mp this

/-- **The lift of a holomorphic function through `π`, in a ball of radius `≤ 1/2`.** -/
theorem exists_piExp_lift {V : Set ℂ} {f : ℂ → ℂ} (hVo : IsOpen V) (hf : DifferentiableOn ℂ f V)
    {a : ℂ} {ρ₀ : ℝ} (hρ₀ : ρ₀ ≤ 1 / 2)
    (hex : ∀ v ∈ V, ∃ w ∈ Metric.ball a ρ₀, MandelDim.piExp w = f v) :
    ∃ W : ℂ → ℂ, DifferentiableOn ℂ W V ∧
      (∀ v ∈ V, W v ∈ Metric.ball a ρ₀ ∧ MandelDim.piExp (W v) = f v) ∧
      (∀ v ∈ V, ∀ w ∈ Metric.ball a ρ₀, MandelDim.piExp w = f v → w = W v) := by
  have hBopen : IsOpen (Metric.ball a ρ₀) := Metric.isOpen_ball
  have hinj : Set.InjOn MandelDim.piExp (Metric.ball a ρ₀) := piExp_injOn_ball_lift hρ₀
  have hdiff : DifferentiableOn ℂ MandelDim.piExp (Metric.ball a ρ₀) := by
    intro w _
    exact (show DifferentiableAt ℂ MandelDim.piExp w by
      unfold MandelDim.piExp
      fun_prop).differentiableWithinAt
  have hinv : DifferentiableOn ℂ (Function.invFunOn MandelDim.piExp (Metric.ball a ρ₀))
      (MandelDim.piExp '' (Metric.ball a ρ₀)) :=
    invFunOn_differentiableOn hBopen hinj hdiff
  refine ⟨fun v => Function.invFunOn MandelDim.piExp (Metric.ball a ρ₀) (f v), ?_, ?_, ?_⟩
  · have hmaps : MapsTo f V (MandelDim.piExp '' (Metric.ball a ρ₀)) := fun v hv =>
      hex v hv
    simpa [Function.comp_def] using hinv.comp hf hmaps
  · intro v hv
    obtain ⟨w, hw, hwπ⟩ := hex v hv
    exact ⟨Function.invFunOn_mem ⟨w, hw, hwπ⟩, Function.invFunOn_eq ⟨w, hw, hwπ⟩⟩
  · intro v hv w hw hwπ
    obtain ⟨w', hw', hw'π⟩ := hex v hv
    have hmem' : Function.invFunOn MandelDim.piExp (Metric.ball a ρ₀) (f v)
        ∈ Metric.ball a ρ₀ := Function.invFunOn_mem ⟨w', hw', hw'π⟩
    have heq' : MandelDim.piExp (Function.invFunOn MandelDim.piExp (Metric.ball a ρ₀) (f v))
        = f v := Function.invFunOn_eq ⟨w', hw', hw'π⟩
    exact hinj hw hmem' (by rw [hwπ, heq'])

end Work.Repel
