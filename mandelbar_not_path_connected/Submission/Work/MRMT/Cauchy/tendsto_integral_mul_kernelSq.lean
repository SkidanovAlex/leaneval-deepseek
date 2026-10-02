import Mathlib
import Submission.Work.MRMT.Cauchy.integral_one_div_one_add_normSq_sq_eq_pi
import Submission.Work.MRMT.Cauchy.integrable_one_div_one_add_normSq_sq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Cauchy

open MeasureTheory Complex

/-!
### The mollified delta identity `ε²/(‖z‖²+ε²)² → π δ₀`

The `L¹` weight `w ↦ (1 + ‖w‖²)⁻²` (whose total integral is `π`) governs the behaviour
after the substitution `z = ε w`.
-/

/-- The `L¹` weight `(1 + ‖w‖²)⁻²`, viewed as a complex-valued function. -/
private noncomputable def kernelSq (w : ℂ) : ℂ := ((1 / (1 + ‖w‖ ^ 2) ^ 2 : ℝ) : ℂ)

private lemma integrable_kernelSq : Integrable (fun w => kernelSq w) volume := by
  simpa only [kernelSq] using integrable_one_div_one_add_normSq_sq

private lemma integral_kernelSq : ∫ w, kernelSq w = (Real.pi : ℂ) := by
  simpa only [kernelSq] using integral_one_div_one_add_normSq_sq_eq_pi

/-! #### The scalar identities behind the substitution `z = ε w` -/

/-- `‖ε⁻¹ z‖² = ‖z‖²/ε²`. -/
private lemma norm_inv_smul_sq {ε : ℝ} (z : ℂ) :
    ‖(ε⁻¹ : ℝ) • z‖ ^ 2 = ‖z‖ ^ 2 / ε ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, mul_pow, inv_pow, sq_abs]
  ring

/-- The elementary real identity `1/(1 + x²/ε²)² = ε⁴/(x² + ε²)²`. -/
private lemma real_scale_identity {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    (1 : ℝ) / (1 + x ^ 2 / ε ^ 2) ^ 2 = ε ^ 4 / (x ^ 2 + ε ^ 2) ^ 2 := by
  have h1 : (1 : ℝ) + x ^ 2 / ε ^ 2 = (x ^ 2 + ε ^ 2) / ε ^ 2 := by
    rw [add_div, div_self (pow_ne_zero 2 hε)]
    ring
  rw [h1, div_pow, one_div_div]
  ring

/-- The value of the weight at the rescaled point. -/
private lemma kernelSq_inv_smul {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    kernelSq ((ε⁻¹ : ℝ) • z)
      = ((ε ^ 4 : ℝ) : ℂ) / (((‖z‖ ^ 2 + ε ^ 2 : ℝ)) : ℂ) ^ 2 := by
  unfold kernelSq
  rw [norm_inv_smul_sq z, real_scale_identity hε ‖z‖]
  push_cast
  ring

/-- Pointwise form of the substitution `z = ε w`. -/
private lemma scaled_integrand (ψ : ℂ → ℂ) {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    ψ ((ε : ℝ) • ((ε⁻¹ : ℝ) • z)) * kernelSq ((ε⁻¹ : ℝ) • z)
      = (ε ^ 2 : ℝ) • (ψ z * ((ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2)) := by
  rw [smul_smul, mul_inv_cancel₀ hε, one_smul, kernelSq_inv_smul hε z]
  rw [Complex.real_smul]
  have h1 : ((ε : ℂ) ^ 2) = ((ε ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((ε ^ 4 : ℝ) : ℂ) = ((ε ^ 2 : ℝ) : ℂ) * ((ε ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, h2]
  ring

/-! #### The main limit -/

theorem tendsto_integral_mul_kernelSq (ψ : ℂ → ℂ) (hψc : Continuous ψ) (hs : HasCompactSupport ψ) :
    Filter.Tendsto (fun ε : ℝ => ∫ z, ψ z * ((ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((Real.pi : ℂ) * ψ 0)) := by
  -- A global bound on `ψ`.
  obtain ⟨C, hC⟩ := hs.isCompact.exists_bound_of_continuousOn
    (hψc.continuousOn.mono (Set.subset_univ _))
  set M : ℝ := max C 0 with hM
  have hψM : ∀ z : ℂ, ‖ψ z‖ ≤ M := by
    intro z
    rw [hM]
    by_cases hz : z ∈ tsupport ψ
    · exact le_trans (hC z hz) (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact le_max_right _ _
  -- The substitution `z = ε w`, valid for `ε ≠ 0`, hence on `Ioi 0`.
  have hstep : (fun ε : ℝ => ∫ z, ψ z * ((ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2))
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun ε : ℝ => ∫ w, ψ ((ε : ℝ) • w) * kernelSq w) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : ε ≠ 0 := ne_of_gt hε
    have hε2 : (ε : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hε0
    have hcoe : |(((ε⁻¹ : ℝ) ^ (Module.finrank ℝ ℂ))⁻¹)| = ε ^ 2 := by
      rw [Complex.finrank_real_complex, inv_pow, inv_inv]
      exact abs_of_nonneg (sq_nonneg ε)
    have hscale := MeasureTheory.Measure.integral_comp_smul (μ := (volume : Measure ℂ))
      (f := fun w : ℂ => ψ ((ε : ℝ) • w) * kernelSq w) (ε⁻¹)
    rw [hcoe] at hscale
    have hleft : (∫ z : ℂ, (fun w : ℂ => ψ ((ε : ℝ) • w) * kernelSq w) ((ε⁻¹ : ℝ) • z))
        = (ε ^ 2 : ℝ) •
            (∫ z, ψ z * ((ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2)) := by
      rw [show (∫ z : ℂ, (fun w : ℂ => ψ ((ε : ℝ) • w) * kernelSq w) ((ε⁻¹ : ℝ) • z))
            = ∫ z : ℂ, (ε ^ 2 : ℝ) •
                (ψ z * ((ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2)) from by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with z
          exact scaled_integrand ψ hε0 z]
      exact MeasureTheory.integral_smul _ _
    have hcomb : (ε ^ 2 : ℝ) •
          (∫ z, ψ z * ((ε : ℂ) ^ 2 / (((‖z‖ ^ 2 + ε ^ 2 : ℝ) : ℂ)) ^ 2))
        = (ε ^ 2 : ℝ) •
            (∫ w : ℂ, (fun w : ℂ => ψ ((ε : ℝ) • w) * kernelSq w) w) :=
      hleft.symm.trans hscale
    rw [Complex.real_smul, Complex.real_smul] at hcomb
    exact mul_left_cancel₀ (by rw [Complex.ofReal_ne_zero]; exact hε2) hcomb
  -- Dominated convergence for the rescaled integral.
  have hDCT : Filter.Tendsto (fun ε : ℝ => ∫ w, ψ ((ε : ℝ) • w) * kernelSq w)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (∫ w, ψ 0 * kernelSq w)) := by
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (bound := fun w : ℂ => M * ‖kernelSq w‖)
      (F := fun ε : ℝ => fun w : ℂ => ψ ((ε : ℝ) • w) * kernelSq w)
      (f := fun w : ℂ => ψ 0 * kernelSq w) ?_ ?_ ?_ ?_
    · filter_upwards with ε
      have hcont : Continuous (fun w : ℂ => ψ ((ε : ℝ) • w)) :=
        hψc.comp ((continuous_const : Continuous (fun _ : ℂ => (ε : ℝ))).smul
          (continuous_id : Continuous (fun w : ℂ => w)))
      exact hcont.aestronglyMeasurable.mul integrable_kernelSq.aestronglyMeasurable
    · filter_upwards with ε
      filter_upwards with w
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hψM (ε • w)) (norm_nonneg _)
    · exact integrable_kernelSq.norm.const_mul M
    · filter_upwards with w
      have hcont : Continuous (fun ε : ℝ => ε • w) := continuous_id.smul continuous_const
      have h1 : Filter.Tendsto (fun ε : ℝ => ε • w) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds ((0 : ℝ) • w)) := (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      rw [zero_smul] at h1
      have h2 : Filter.Tendsto (fun ε : ℝ => ψ (ε • w)) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds (ψ 0)) := (hψc.tendsto 0).comp h1
      simpa using h2.mul tendsto_const_nhds
  -- Value of the limiting integral.
  have hfinal : (∫ w, ψ 0 * kernelSq w) = (Real.pi : ℂ) * ψ 0 := by
    rw [MeasureTheory.integral_const_mul, integral_kernelSq]
    exact mul_comm _ _
  rw [hfinal] at hDCT
  exact Filter.Tendsto.congr' hstep.symm hDCT

end Work.MRMT.Cauchy
