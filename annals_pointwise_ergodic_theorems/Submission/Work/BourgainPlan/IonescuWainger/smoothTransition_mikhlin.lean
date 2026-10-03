import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.cutoff

namespace Work.BourgainPlan.IonescuWainger

open Filter
open scoped Topology

noncomputable section

/-- Mikhlin-type control of the complexified smooth transition function
`ξ ↦ (Real.smoothTransition ξ : ℂ)`.

The three bounds are: `‖f‖ ≤ A`, `|ξ| ‖f'(ξ)‖ ≤ A`, `|ξ|² ‖f''(ξ)‖ ≤ A`.  They hold because
`Real.smoothTransition` is `C²`, equals `0` on `(-∞,0]` and `1` on `[1,∞)`, so all derivatives
vanish off the compact interval `[0,1]`, while on `[0,1]` the continuous weighted derivatives
attain a maximum. -/

private lemma complex_norm_ofReal (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := RCLike.norm_ofReal r

/-- The complexified smooth transition function is `C²`. -/
private lemma contDiff_smoothTransition_complex :
    ContDiff ℝ 2 (fun ξ : ℝ => (Real.smoothTransition ξ : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp Real.smoothTransition.contDiff

/-- The derivative of the complexified smooth transition function is the complexification of the
real derivative. -/
private lemma deriv_smoothTransition_complex (ξ : ℝ) :
    deriv (fun x : ℝ => (Real.smoothTransition x : ℂ)) ξ
      = ((deriv Real.smoothTransition ξ : ℝ) : ℂ) := by
  have hG : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff
  have hdiff : DifferentiableAt ℝ Real.smoothTransition ξ :=
    (hG.differentiable (by norm_num)).differentiableAt
  exact (HasDerivAt.ofReal_comp hdiff.hasDerivAt).deriv

/-- `deriv Real.smoothTransition` is differentiable, since `Real.smoothTransition` is `C²`. -/
private lemma differentiable_deriv_smoothTransition :
    Differentiable ℝ (deriv Real.smoothTransition) := by
  have hG : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff
  have h := hG.differentiable_iteratedDeriv 1 (by norm_num)
  rwa [iteratedDeriv_one] at h

/-- The second derivative of the complexified smooth transition function is the complexification of
the real second derivative. -/
private lemma iteratedDeriv_two_smoothTransition_complex (ξ : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => (Real.smoothTransition x : ℂ)) ξ
      = ((iteratedDeriv 2 Real.smoothTransition ξ : ℝ) : ℂ) := by
  have hderiv : deriv (fun x : ℝ => (Real.smoothTransition x : ℂ))
      = fun x : ℝ => ((deriv Real.smoothTransition x : ℝ) : ℂ) := by
    funext y
    exact deriv_smoothTransition_complex y
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv]
  rw [show iteratedDeriv 2 Real.smoothTransition ξ = deriv (deriv Real.smoothTransition) ξ from by
        rw [iteratedDeriv_succ, iteratedDeriv_one]]
  exact (HasDerivAt.ofReal_comp
    (differentiable_deriv_smoothTransition.differentiableAt.hasDerivAt)).deriv

/-- On `(-∞,0)` the smooth transition function is locally constant, hence its derivative vanishes. -/
private lemma deriv_smoothTransition_eq_zero_of_lt_zero {x : ℝ} (hx : x < 0) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0:ℝ)) := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact Real.smoothTransition.zero_of_nonpos hy.le
  rw [h.deriv_eq, deriv_const]

/-- On `(1,∞)` the smooth transition function is locally constant, hence its derivative vanishes. -/
private lemma deriv_smoothTransition_eq_zero_of_one_lt {x : ℝ} (hx : 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (1:ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact Real.smoothTransition.one_of_one_le hy.le
  rw [h.deriv_eq, deriv_const]

/-- The second derivative of the smooth transition function vanishes off `[0,1]`. -/
private lemma iteratedDeriv_two_smoothTransition_eq_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) :
    iteratedDeriv 2 Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have h : deriv Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0:ℝ)) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact deriv_smoothTransition_eq_zero_of_lt_zero hy
    rw [iteratedDeriv_succ, iteratedDeriv_one, h.deriv_eq, deriv_const]
  · have h : deriv Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0:ℝ)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact deriv_smoothTransition_eq_zero_of_one_lt hy
    rw [iteratedDeriv_succ, iteratedDeriv_one, h.deriv_eq, deriv_const]

theorem smoothTransition_mikhlin : ∃ A : ℝ, 0 ≤ A ∧ ContDiff ℝ 2 (fun ξ : ℝ => (Real.smoothTransition ξ : ℂ)) ∧ (∀ ξ : ℝ, ‖(Real.smoothTransition ξ : ℂ)‖ ≤ A) ∧ (∀ ξ : ℝ, |ξ| * ‖deriv (fun ξ : ℝ => (Real.smoothTransition ξ : ℂ)) ξ‖ ≤ A) ∧ (∀ ξ : ℝ, |ξ| ^ 2 * ‖iteratedDeriv 2 (fun ξ : ℝ => (Real.smoothTransition ξ : ℂ)) ξ‖ ≤ A) := by
  have hG : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff
  have hcd : Continuous (deriv Real.smoothTransition) := hG.continuous_deriv (by norm_num)
  have hci : Continuous (iteratedDeriv 2 Real.smoothTransition) :=
    hG.continuous_iteratedDeriv 2 (by norm_num)
  have hcont₁ : Continuous (fun ξ : ℝ => |ξ| * |deriv Real.smoothTransition ξ|) :=
    (continuous_abs.comp continuous_id).mul (continuous_abs.comp hcd)
  have hcont₂ : Continuous (fun ξ : ℝ => |ξ| ^ 2 * |iteratedDeriv 2 Real.smoothTransition ξ|) :=
    ((continuous_abs.comp continuous_id).pow 2).mul (continuous_abs.comp hci)
  obtain ⟨x₁, -, hmax₁⟩ := isCompact_Icc.exists_isMaxOn (s := Set.Icc (0:ℝ) 1)
      ⟨0, le_rfl, zero_le_one⟩ hcont₁.continuousOn
  obtain ⟨x₂, -, hmax₂⟩ := isCompact_Icc.exists_isMaxOn (s := Set.Icc (0:ℝ) 1)
      ⟨0, le_rfl, zero_le_one⟩ hcont₂.continuousOn
  refine ⟨max 1 (max (|x₁| * |deriv Real.smoothTransition x₁|)
        (|x₂| ^ 2 * |iteratedDeriv 2 Real.smoothTransition x₂|)), ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans zero_le_one (le_max_left _ _)
  · exact contDiff_smoothTransition_complex
  · intro ξ
    have h1 : ‖((Real.smoothTransition ξ : ℝ) : ℂ)‖ = Real.smoothTransition ξ := by
      rw [complex_norm_ofReal, abs_of_nonneg (Real.smoothTransition.nonneg ξ)]
    rw [h1]
    exact le_trans (Real.smoothTransition.le_one ξ) (le_max_left _ _)
  · intro ξ
    rw [deriv_smoothTransition_complex ξ, complex_norm_ofReal]
    rcases lt_or_ge ξ 0 with h | h
    · rw [deriv_smoothTransition_eq_zero_of_lt_zero h, abs_zero, mul_zero]
      exact le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left _ _)
    · rcases lt_or_ge 1 ξ with h' | h'
      · rw [deriv_smoothTransition_eq_zero_of_one_lt h', abs_zero, mul_zero]
        exact le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left _ _)
      · exact le_trans (hmax₁ ⟨h, h'⟩) (le_trans (le_max_left _ _) (le_max_right _ _))
  · intro ξ
    rw [iteratedDeriv_two_smoothTransition_complex ξ, complex_norm_ofReal]
    rcases lt_or_ge ξ 0 with h | h
    · rw [iteratedDeriv_two_smoothTransition_eq_zero (Or.inl h), abs_zero, mul_zero]
      exact le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left _ _)
    · rcases lt_or_ge 1 ξ with h' | h'
      · rw [iteratedDeriv_two_smoothTransition_eq_zero (Or.inr h'), abs_zero, mul_zero]
        exact le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_left _ _)
      · exact le_trans (hmax₂ ⟨h, h'⟩) (le_trans (le_max_right _ _) (le_max_right _ _))

end

end Work.BourgainPlan.IonescuWainger
