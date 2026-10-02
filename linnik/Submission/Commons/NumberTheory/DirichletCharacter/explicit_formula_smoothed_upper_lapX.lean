import Mathlib

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open Complex MeasureTheory intervalIntegral Filter
open scoped Real Topology BigOperators

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The Laplace transform `F(z) = ∫_0^{x₀} e^{-zt} f(t) dt`. -/
def lapX (x₀ : ℝ) (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t


/-- `lapX x₀ f` is entire when `f` is continuous on `[0,x₀]`. -/
lemma differentiable_lapX {x₀ : ℝ} {f : ℝ → ℂ} (h0x : (0:ℝ) ≤ x₀)
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) :
    Differentiable ℂ (lapX x₀ f) := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ t ∈ Set.Icc (0:ℝ) x₀, ‖f t‖ ≤ C := by
    have hb : Bornology.IsBounded (f '' Set.Icc (0:ℝ) x₀) :=
      (isCompact_Icc (a := (0:ℝ)) (b := x₀)).image_of_continuousOn hcont |>.isBounded
    obtain ⟨C, hC⟩ := hb.exists_norm_le
    exact ⟨C, fun t ht => hC (f t) (Set.mem_image_of_mem f ht)⟩
  intro z
  rw [show lapX x₀ f = fun w => ∫ t in (0:ℝ)..x₀, Complex.exp (-(w * (t : ℂ))) * f t from rfl]
  have hfAE : AEStronglyMeasurable f (volume.restrict (Set.uIoc (0:ℝ) x₀)) :=
    (hcont.aestronglyMeasurable measurableSet_Icc).mono_measure
      (Measure.restrict_mono (fun t ht => by rw [Set.uIoc_of_le h0x] at ht; exact ⟨le_of_lt ht.1, ht.2⟩) le_rfl)
  have hmulAE : ∀ (g : ℝ → ℂ), Continuous g →
      AEStronglyMeasurable g (volume.restrict (Set.uIoc (0:ℝ) x₀)) := by
    intro g hg
    exact (hg.aestronglyMeasurable).mono_measure
      (Measure.restrict_le_self (μ := volume) (s := Set.uIoc (0:ℝ) x₀))
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := (0:ℝ)) (b := x₀)
    (F := fun w t => Complex.exp (-(w * (t : ℂ))) * f t)
    (F' := fun w t => (-(t : ℂ)) * Complex.exp (-(w * (t : ℂ))) * f t)
    (x₀ := z) (s := Metric.ball z 1)
    (bound := fun _ => x₀ * Real.exp ((‖z‖ + 1) * x₀) * C)
    (Metric.ball_mem_nhds z one_pos)
    (Filter.Eventually.of_forall (fun w =>
      (hmulAE (fun t : ℝ => Complex.exp (-(w * (t : ℂ)))) (by fun_prop)).mul hfAE))
    (by
      have hc : ContinuousOn (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * f t) (Set.uIcc 0 x₀) :=
        (Continuous.continuousOn (by fun_prop)).mul (hcont.mono (by rw [Set.uIcc_of_le h0x]))
      exact hc.intervalIntegrable)
    ((hmulAE (fun t : ℝ => (-(t : ℂ)) * Complex.exp (-(z * (t : ℂ)))) (by fun_prop)).mul hfAE)
    (by
      filter_upwards with t ht x hx
      rw [Set.uIoc_of_le h0x] at ht
      have ht' : t ∈ Set.Icc (0:ℝ) x₀ := ⟨le_of_lt ht.1, ht.2⟩
      have hnorm : ‖Complex.exp (-(x * (t : ℂ)))‖ ≤ Real.exp ((‖z‖ + 1) * x₀) := by
        rw [Complex.norm_exp]
        apply Real.exp_le_exp.mpr
        have hx1 : ‖x - z‖ < 1 := by rw [← dist_eq_norm]; exact hx
        have hxz : ‖x‖ ≤ ‖z‖ + 1 := by
          have hxx : ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
          rw [hxx]
          calc ‖(x - z) + z‖ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
            _ ≤ ‖z‖ + 1 := by linarith
        calc -(x * (t:ℂ)).re ≤ ‖x * (t:ℂ)‖ := le_trans (neg_le_abs _) (Complex.abs_re_le_norm _)
          _ = ‖x‖ * |t| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ (‖z‖ + 1) * x₀ := by
              apply mul_le_mul hxz _ (abs_nonneg t) (by linarith [norm_nonneg z])
              rw [abs_le]; exact ⟨by linarith [ht'.1], ht'.2⟩
      calc ‖(-(t : ℂ)) * Complex.exp (-(x * (t : ℂ))) * f t‖
          = |t| * ‖Complex.exp (-(x * (t : ℂ)))‖ * ‖f t‖ := by
            rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ x₀ * Real.exp ((‖z‖ + 1) * x₀) * C := by
            gcongr
            · rw [abs_le]; exact ⟨by linarith [ht'.1], ht'.2⟩
            · exact hC t ht')
    (by apply ContinuousOn.intervalIntegrable; apply continuousOn_const)
    (by
      filter_upwards with t ht x hx
      rw [Set.uIoc_of_le h0x] at ht
      have h1 : HasDerivAt (fun w : ℂ => w * (t : ℂ)) (t : ℂ) x := hasDerivAt_mul_const _
      have h1' : HasDerivAt (fun w : ℂ => -(w * (t : ℂ))) (-(t : ℂ)) x := h1.neg
      have h2 := (Complex.hasDerivAt_exp (-(x * (t : ℂ)))).comp x h1'
      have h2' : HasDerivAt (fun y : ℂ => Complex.exp (-(y * (t : ℂ))))
          (Complex.exp (-(x * (t : ℂ))) * (-(t : ℂ))) x := by
        simpa only [Function.comp_def] using h2
      have h3 : HasDerivAt (fun y : ℂ => Complex.exp (-(y * (t : ℂ))))
          ((-(t : ℂ)) * Complex.exp (-(x * (t : ℂ)))) x := h2'.congr_deriv (by ring)
      exact h3.mul_const (f t))
  exact hmain.2.differentiableAt




/-- The map `u ↦ lapX x₀ f ((s-u)L)` is entire. -/
lemma differentiable_lapX_affine {x₀ : ℝ} {f : ℝ → ℂ} (h0x : (0:ℝ) ≤ x₀)
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (s : ℂ) (L : ℝ) :
    Differentiable ℂ (fun u : ℂ => lapX x₀ f ((s - u) * (L : ℂ))) := by
  refine (differentiable_lapX h0x hcont).comp (fun z => ?_)
  exact (by fun_prop : DifferentiableAt ℂ (fun u : ℂ => (s - u) * (L : ℂ)) z)


/-- Measurability of `logDeriv` of the `L`-function. -/
lemma measurable_logDeriv_LFunction' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    Measurable (fun z : ℂ => logDeriv (DirichletCharacter.LFunction χ) z) := by
  have hdF : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hd : Measurable (deriv (DirichletCharacter.LFunction χ)) := hdF.deriv.continuous.measurable
  have hFm : Measurable (DirichletCharacter.LFunction χ) := hdF.continuous.measurable
  unfold logDeriv
  exact hd.div hFm


end
end Commons.NumberTheory.DirichletCharacter
