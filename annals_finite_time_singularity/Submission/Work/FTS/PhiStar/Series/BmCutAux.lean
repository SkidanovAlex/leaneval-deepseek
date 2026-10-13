import Mathlib

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

/-! # The rescaled ramp `θ ↦ smoothTransition (a * θ + b)`

Auxiliary material for the cutoff family `chi` of `BmCut.lean`: the values of
`Real.smoothTransition` on `(-∞,0]` and `[1,∞)`, the vanishing of its first two derivatives
there *including the endpoints* `0` and `1` (which is what makes the derivatives of the
cutoff vanish on the closed outer regions), and the derivative formulas and bounds for the
rescaled ramps. -/

/-! ## Derivatives of `Real.smoothTransition` at the ends of `[0,1]` -/

private lemma st_eq_zero_nhds {x : ℝ} (hx : x < 0) :
    Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
  filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
  exact Real.smoothTransition.zero_of_nonpos hy.le

private lemma st_eq_one_nhds {x : ℝ} (hx : 1 < x) :
    Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (1 : ℝ)) := by
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact Real.smoothTransition.one_of_one_le hy.le

private lemma st_deriv_zero {x : ℝ} (hx : x < 0) : deriv Real.smoothTransition x = 0 := by
  rw [Filter.EventuallyEq.deriv_eq (st_eq_zero_nhds hx), deriv_const]

private lemma st_deriv_one {x : ℝ} (hx : 1 < x) : deriv Real.smoothTransition x = 0 := by
  rw [Filter.EventuallyEq.deriv_eq (st_eq_one_nhds hx), deriv_const]

private lemma st_deriv2_zero {x : ℝ} (hx : x < 0) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have h1 : deriv Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) :=
    (st_eq_zero_nhds hx).deriv.trans (Filter.Eventually.of_forall fun y => deriv_const y 0)
  rw [Filter.EventuallyEq.deriv_eq h1, deriv_const]

private lemma st_deriv2_one {x : ℝ} (hx : 1 < x) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  have h1 : deriv Real.smoothTransition =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
    have h2 := (st_eq_one_nhds hx).deriv
    have h3 : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ : ℝ => (0 : ℝ) := by
      funext y
      exact deriv_const y 1
    rwa [h3] at h2
  rw [Filter.EventuallyEq.deriv_eq h1, deriv_const]

private lemma st_deriv_cont : Continuous (deriv Real.smoothTransition) := by fun_prop

private lemma st_deriv2_cont : Continuous (deriv (deriv Real.smoothTransition)) := by fun_prop

/-- The first derivative of `Real.smoothTransition` vanishes on `(-∞,0]`. -/
theorem st_deriv_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  rcases lt_or_eq_of_le hx with h | rfl
  · exact st_deriv_zero h
  · have hclosed : IsClosed {y : ℝ | deriv Real.smoothTransition y = 0} :=
      isClosed_eq st_deriv_cont continuous_const
    have hle : closure (Set.Iio (0 : ℝ)) ⊆ {y : ℝ | deriv Real.smoothTransition y = 0} :=
      hclosed.closure_subset_iff.mpr (fun y hy => st_deriv_zero hy)
    exact hle (by rw [closure_Iio]; exact Set.mem_Iic.mpr le_rfl)

/-- The first derivative of `Real.smoothTransition` vanishes on `[1,∞)`. -/
theorem st_deriv_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  rcases lt_or_eq_of_le hx with h | rfl
  · exact st_deriv_one h
  · have hclosed : IsClosed {y : ℝ | deriv Real.smoothTransition y = 0} :=
      isClosed_eq st_deriv_cont continuous_const
    have hle : closure (Set.Ioi (1 : ℝ)) ⊆ {y : ℝ | deriv Real.smoothTransition y = 0} :=
      hclosed.closure_subset_iff.mpr (fun y hy => st_deriv_one hy)
    exact hle (by rw [closure_Ioi]; exact Set.mem_Ici.mpr le_rfl)

/-- The second derivative of `Real.smoothTransition` vanishes on `(-∞,0]`. -/
theorem st_deriv2_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  rcases lt_or_eq_of_le hx with h | rfl
  · exact st_deriv2_zero h
  · have hclosed : IsClosed {y : ℝ | deriv (deriv Real.smoothTransition) y = 0} :=
      isClosed_eq st_deriv2_cont continuous_const
    have hle : closure (Set.Iio (0 : ℝ))
        ⊆ {y : ℝ | deriv (deriv Real.smoothTransition) y = 0} :=
      hclosed.closure_subset_iff.mpr (fun y hy => st_deriv2_zero hy)
    exact hle (by rw [closure_Iio]; exact Set.mem_Iic.mpr le_rfl)

/-- The second derivative of `Real.smoothTransition` vanishes on `[1,∞)`. -/
theorem st_deriv2_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv (deriv Real.smoothTransition) x = 0 := by
  rcases lt_or_eq_of_le hx with h | rfl
  · exact st_deriv2_one h
  · have hclosed : IsClosed {y : ℝ | deriv (deriv Real.smoothTransition) y = 0} :=
      isClosed_eq st_deriv2_cont continuous_const
    have hle : closure (Set.Ioi (1 : ℝ))
        ⊆ {y : ℝ | deriv (deriv Real.smoothTransition) y = 0} :=
      hclosed.closure_subset_iff.mpr (fun y hy => st_deriv2_one hy)
    exact hle (by rw [closure_Ioi]; exact Set.mem_Ici.mpr le_rfl)

/-! ## Boundedness of the derivatives -/

private theorem st_deriv_bound : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C := by
  have hcont : Continuous fun x : ℝ => |deriv Real.smoothTransition x| := st_deriv_cont.abs
  obtain ⟨x₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (s := Set.Icc (0 : ℝ) 1)
    ⟨0, by norm_num, by norm_num⟩ hcont.continuousOn
  refine ⟨|deriv Real.smoothTransition x₀| + 1, by positivity, fun x => ?_⟩
  rcases le_or_gt x 0 with hx | hx
  · rw [st_deriv_eq_zero_of_nonpos hx, abs_zero]
    positivity
  · rcases le_or_gt 1 x with hx1 | hx1
    · rw [st_deriv_eq_zero_of_one_le hx1, abs_zero]
      positivity
    · exact le_trans (hmax ⟨hx.le, hx1.le⟩) (le_add_of_nonneg_right zero_le_one)

private theorem st_deriv2_bound : ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ C := by
  have hcont : Continuous fun x : ℝ => |deriv (deriv Real.smoothTransition) x| :=
    st_deriv2_cont.abs
  obtain ⟨x₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (s := Set.Icc (0 : ℝ) 1)
    ⟨0, by norm_num, by norm_num⟩ hcont.continuousOn
  refine ⟨|deriv (deriv Real.smoothTransition) x₀| + 1, by positivity, fun x => ?_⟩
  rcases le_or_gt x 0 with hx | hx
  · rw [st_deriv2_eq_zero_of_nonpos hx, abs_zero]
    positivity
  · rcases le_or_gt 1 x with hx1 | hx1
    · rw [st_deriv2_eq_zero_of_one_le hx1, abs_zero]
      positivity
    · exact le_trans (hmax ⟨hx.le, hx1.le⟩) (le_add_of_nonneg_right zero_le_one)

/-! ## The rescaled ramp -/

/-- The rescaled ramp `θ ↦ ψ (a * θ + b)` where `ψ = Real.smoothTransition`. -/
def ramp (a b : ℝ) : ℝ → ℝ := fun t => Real.smoothTransition (a * t + b)

theorem ramp_nonneg (a b θ : ℝ) : 0 ≤ ramp a b θ := Real.smoothTransition.nonneg _

theorem ramp_le_one (a b θ : ℝ) : ramp a b θ ≤ 1 := Real.smoothTransition.le_one _

theorem ramp_eq_zero (a b θ : ℝ) (h : a * θ + b ≤ 0) : ramp a b θ = 0 :=
  Real.smoothTransition.zero_of_nonpos h

theorem ramp_eq_one (a b θ : ℝ) (h : 1 ≤ a * θ + b) : ramp a b θ = 1 :=
  Real.smoothTransition.one_of_one_le h

theorem ramp_contDiff (a b : ℝ) : ContDiff ℝ 2 (ramp a b) := by
  show ContDiff ℝ 2 (fun t : ℝ => Real.smoothTransition (a * t + b))
  fun_prop

theorem ramp_diff (a b : ℝ) : Differentiable ℝ (ramp a b) :=
  (ramp_contDiff a b).differentiable (by norm_num)

private theorem st_deriv2_diff : Differentiable ℝ (deriv Real.smoothTransition) := by fun_prop

theorem deriv_ramp (a b θ : ℝ) :
    deriv (ramp a b) θ = deriv Real.smoothTransition (a * θ + b) * a := by
  have h1 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (a * θ + b))
      (a * θ + b) :=
    (((Real.smoothTransition.contDiff (n := 2)).differentiable
      (by norm_num)).differentiableAt).hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => a * t + b) a θ := by
    simpa using (((hasDerivAt_id θ).const_mul a).const_add b)
  have h3 := h1.comp θ h2
  show deriv (fun t : ℝ => Real.smoothTransition (a * t + b)) θ = _
  simpa [Function.comp_def] using h3.deriv

theorem deriv2_ramp (a b θ : ℝ) :
    deriv (deriv (ramp a b)) θ = deriv (deriv Real.smoothTransition) (a * θ + b) * a * a := by
  have hfun : deriv (ramp a b) = fun t => deriv Real.smoothTransition (a * t + b) * a := by
    funext t
    exact deriv_ramp a b t
  rw [hfun]
  have h3 : HasDerivAt (fun t : ℝ => deriv Real.smoothTransition (a * t + b))
      (deriv (deriv Real.smoothTransition) (a * θ + b) * a) θ := by
    have hg : HasDerivAt (deriv Real.smoothTransition)
        (deriv (deriv Real.smoothTransition) (a * θ + b)) (a * θ + b) :=
      (st_deriv2_diff.differentiableAt).hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => a * t + b) a θ := by
      simpa using (((hasDerivAt_id θ).const_mul a).const_add b)
    simpa [Function.comp_def] using hg.comp θ h2
  have hpm : (fun t : ℝ => deriv Real.smoothTransition (a * t + b) * a)
      = (fun t : ℝ => deriv Real.smoothTransition (a * t + b)) * (fun _ : ℝ => a) := rfl
  rw [hpm, deriv_mul h3.differentiableAt (differentiableAt_const a), h3.deriv, deriv_const]
  ring

theorem ramp_diffAt_deriv (a b θ : ℝ) : DifferentiableAt ℝ (deriv (ramp a b)) θ := by
  have hfun : deriv (ramp a b) = fun t => deriv Real.smoothTransition (a * t + b) * a := by
    funext t
    exact deriv_ramp a b t
  rw [hfun]
  have hg : DifferentiableAt ℝ (fun t : ℝ => a * t + b) θ := by
    simpa using (((hasDerivAt_id θ).const_mul a).const_add b).differentiableAt
  have h1 : DifferentiableAt ℝ (fun t : ℝ => deriv Real.smoothTransition (a * t + b)) θ := by
    have hc : DifferentiableAt ℝ (deriv Real.smoothTransition) (a * θ + b) :=
      st_deriv2_diff.differentiableAt
    simpa [Function.comp_def] using hc.comp θ hg
  simpa using h1.mul_const a

theorem deriv_ramp_bound {C : ℝ} (hC : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C)
    (a b θ : ℝ) : |deriv (ramp a b) θ| ≤ C * |a| := by
  rw [deriv_ramp, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC _) (abs_nonneg a)

theorem deriv2_ramp_bound {C : ℝ}
    (hC : ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ C) (a b θ : ℝ) :
    |deriv (deriv (ramp a b)) θ| ≤ C * (|a| * |a|) := by
  rw [deriv2_ramp, abs_mul, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC _) (mul_nonneg (abs_nonneg a) (abs_nonneg a))

/-- The bounds `C₁`, `C₂` on the first two derivatives of `Real.smoothTransition`. -/
theorem st_bounds : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    (∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₁) ∧
    (∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ C₂) := by
  obtain ⟨C₁, hC₁, h1⟩ := st_deriv_bound
  obtain ⟨C₂, hC₂, h2⟩ := st_deriv2_bound
  exact ⟨C₁, C₂, hC₁, hC₂, h1, h2⟩

end Work.FTS.PhiStar.Series
