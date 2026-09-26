import Mathlib

namespace Work.Radial

/-- The continuous linear map `E →L[ℝ] (E →L[ℝ] ℝ)` underlying the derivative of the
quadratic function `x ↦ ‖x‖^2`: it sends `x` to the functional `y ↦ 2 * ⟪x, y⟫`
(implemented as `2 • innerSL ℝ x`, with `2` a natural number scalar). -/
noncomputable def quadDerivCLM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    E →L[ℝ] E →L[ℝ] ℝ := (2:ℕ) • (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)

/-- The operator norm of `quadDerivCLM` is at most `2`. -/
lemma norm_quadDerivCLM_le (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ‖quadDerivCLM E‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun y => ?_)
  show ‖quadDerivCLM E y‖ ≤ 2 * ‖y‖
  rw [show quadDerivCLM E y = (2:ℕ) • innerSL ℝ y from rfl]
  calc ‖(2:ℕ) • innerSL ℝ y‖ ≤ (2:ℝ) * ‖innerSL ℝ y‖ := norm_nsmul_le
    _ = 2 * ‖y‖ := by rw [innerSL_apply_norm]

/-- The Fréchet derivative of `x ↦ ‖x‖^2` is the continuous linear map `quadDerivCLM`. -/
lemma fderiv_norm_sq_eq (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    fderiv ℝ (fun x : E => ‖x‖ ^ 2) = fun y => quadDerivCLM E y := by
  funext y
  rw [fderiv_norm_sq_apply]
  rfl

/-- For a continuous linear map `L`, the iterated derivatives of `L` itself are uniformly
bounded by `‖L‖ * (1 + ‖x‖)` independently of the order. -/
lemma norm_iteratedFDeriv_linearMap_le {E' F : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E' →L[ℝ] F) (m : ℕ) (x : E') :
    ‖iteratedFDeriv ℝ m (fun x => L x) x‖ ≤ ‖L‖ * (1 + ‖x‖) := by
  obtain h0 | hpos := Nat.eq_zero_or_pos m
  · subst h0
    rw [norm_iteratedFDeriv_zero]
    calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
      _ ≤ ‖L‖ * (1 + ‖x‖) := mul_le_mul_of_nonneg_left (by linarith [norm_nonneg x]) (norm_nonneg L)
  · obtain rfl | h1m := eq_or_lt_of_le (show 1 ≤ m from hpos)
    · rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv L]
      exact le_mul_of_one_le_right (norm_nonneg L) (by linarith [norm_nonneg x])
    · have hfd : fderiv ℝ (fun x : E' => L x) = fun _ : E' => L := by
        funext y; exact ContinuousLinearMap.fderiv L
      have key : ‖iteratedFDeriv ℝ m (fun x : E' => L x) x‖
          = ‖iteratedFDeriv ℝ (m - 1) (fun _ : E' => L) x‖ := by
        have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun x : E' => L x) (x := x) (n := m - 1)
        rw [hfd, Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
        exact h.symm
      rw [key]
      have hz : ‖iteratedFDeriv ℝ (m - 1) (fun _ : E' => L) x‖ = 0 := by
        rw [iteratedFDeriv_const_of_ne (by omega : m - 1 ≠ 0) L]
        simp
      rw [hz]
      positivity

/-- All iterated derivatives of `x ↦ ‖x‖^2` (of any order) are bounded by `2 * (1 + ‖x‖)^2`. -/
lemma norm_iteratedFDeriv_norm_sq_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (fun x : E => ‖x‖ ^ 2) x‖ ≤ 2 * (1 + ‖x‖) ^ 2 := by
  obtain h0 | hpos := Nat.eq_zero_or_pos i
  · subst h0
    rw [norm_iteratedFDeriv_zero, Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg x]
  · have key : ‖iteratedFDeriv ℝ i (fun x : E => ‖x‖ ^ 2) x‖
        = ‖iteratedFDeriv ℝ (i - 1) (fun y => quadDerivCLM E y) x‖ := by
      have h := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun x : E => ‖x‖ ^ 2) (x := x) (n := i - 1)
      rw [fderiv_norm_sq_eq, Nat.sub_add_cancel (show 1 ≤ i from hpos)] at h
      exact h.symm
    rw [key]
    calc ‖iteratedFDeriv ℝ (i - 1) (fun y => quadDerivCLM E y) x‖
        ≤ ‖quadDerivCLM E‖ * (1 + ‖x‖) := norm_iteratedFDeriv_linearMap_le _ _ _
      _ ≤ 2 * (1 + ‖x‖) :=
          mul_le_mul_of_nonneg_right (norm_quadDerivCLM_le E) (by linarith [norm_nonneg x])
      _ ≤ 2 * (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]

lemma quad_iteratedFDeriv_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c : ℂ) (i : ℕ) (x : E) : ‖iteratedFDeriv ℝ i (fun x : E => c * (↑(‖x‖ ^ 2) : ℂ)) x‖ ≤ 2 * (‖c‖ + 1) * (1 + ‖x‖) ^ 2 := by
  have hfun : (fun x : E => c * (↑(‖x‖ ^ 2) : ℂ)) = c • (fun x : E => (↑(‖x‖ ^ 2) : ℂ)) := by
    funext y; rw [Pi.smul_apply, smul_eq_mul]
  have hψ : ContDiffAt ℝ i (fun x : E => (↑(‖x‖ ^ 2) : ℂ)) x := by
    have h := (Complex.ofRealLI.contDiff (n := (i : WithTop ℕ∞))).comp_contDiffAt x
      ((contDiff_norm_sq ℝ).contDiffAt (x := x) (n := (i : WithTop ℕ∞)))
    simpa [Function.comp_def] using h
  have hψn : ‖iteratedFDeriv ℝ i (fun x : E => (↑(‖x‖ ^ 2) : ℂ)) x‖
      = ‖iteratedFDeriv ℝ i (fun x : E => ‖x‖ ^ 2) x‖ := by
    have h := (Complex.ofRealLI).norm_iteratedFDeriv_comp_left
      (f := fun x : E => ‖x‖ ^ 2) (x := x) (n := (i : WithTop ℕ∞))
      ((contDiff_norm_sq ℝ).contDiffAt) (le_refl _)
    simpa [Function.comp_def] using h
  rw [hfun, iteratedFDeriv_const_smul_apply (a := c) hψ, norm_smul, hψn]
  calc ‖c‖ * ‖iteratedFDeriv ℝ i (fun x : E => ‖x‖ ^ 2) x‖
      ≤ ‖c‖ * (2 * (1 + ‖x‖) ^ 2) :=
        mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_norm_sq_le i x) (norm_nonneg c)
    _ ≤ 2 * (‖c‖ + 1) * (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg c, sq_nonneg (1 + ‖x‖)]

end Work.Radial
