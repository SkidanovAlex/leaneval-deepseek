import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.cutoff

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory Filter
open scoped Topology

/-- As `ε ↓ 0` the plateau `plateau ε` increases to the indicator of the Nyquist band `[-1/2,1/2]`
pointwise off the two endpoints.  Consequently, for `m` supported in `[-1/2,1/2]` and `trig` bounded,
the inverse Fourier transforms of `m · trig · plateau ε` converge to that of `m · trig`. -/
theorem tendsto_fourierInv_plateau (m : ℝ → ℂ) (hmi : MeasureTheory.Integrable m)
    (hmsupp : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2):ℝ) (1/2) → m ξ = 0)
    {trig : ℝ → ℂ} (htrig : AEStronglyMeasurable trig MeasureTheory.volume)
    {c : ℝ} (hc : ∀ ξ : ℝ, ‖trig ξ‖ ≤ c) (hc0 : 0 ≤ c) (x : ℝ) :
    Filter.Tendsto (fun j : ℕ => FourierTransformInv.fourierInv
        (fun ξ : ℝ => m ξ * trig ξ * ((Work.BourgainPlan.IonescuWainger.plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ)) x)
      Filter.atTop (nhds (FourierTransformInv.fourierInv (fun ξ : ℝ => m ξ * trig ξ) x)) := by
  simp only [Real.fourierInv_eq', smul_eq_mul]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence (fun ξ => c * ‖m ξ‖)
  · intro j
    have h1 : AEStronglyMeasurable
        (fun ξ : ℝ => Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I)) volume := by
      apply Continuous.aestronglyMeasurable
      fun_prop
    have h2 : AEStronglyMeasurable (fun ξ : ℝ => m ξ * trig ξ) volume :=
      hmi.aestronglyMeasurable.mul htrig
    have h3 : AEStronglyMeasurable
        (fun ξ : ℝ => ((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ)) volume := by
      apply Continuous.aestronglyMeasurable
      exact Complex.continuous_ofReal.comp (plateau_continuous _)
    exact h1.mul (h2.mul h3)
  · exact hmi.norm.const_mul c
  · intro j
    filter_upwards with ξ
    have hε : 0 < (1/((j:ℝ)+2) : ℝ) := by positivity
    have hP0 : 0 ≤ plateau (1/((j:ℝ)+2)) ξ := plateau_nonneg _ _
    have hP1 : plateau (1/((j:ℝ)+2)) ξ ≤ 1 := plateau_le_one _ hε ξ
    have hPn : ‖((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ)‖ ≤ 1 := by
      rw [show ‖((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ)‖ = |plateau (1/((j:ℝ)+2)) ξ| from
        RCLike.norm_ofReal _]
      rw [abs_of_nonneg hP0]
      exact hP1
    have hexp : ‖Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I)‖ = 1 :=
      Complex.norm_exp_ofReal_mul_I _
    calc ‖Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I) *
            (m ξ * trig ξ * ((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ))‖
        = ‖Complex.exp (↑(2 * Real.pi * inner ℝ ξ x) * Complex.I)‖ *
            ‖m ξ * trig ξ * ((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ)‖ := norm_mul _ _
      _ = ‖m ξ * trig ξ * ((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ)‖ := by
            rw [hexp, one_mul]
      _ = ‖m ξ‖ * ‖trig ξ‖ * ‖((plateau (1/((j:ℝ)+2)) ξ : ℝ) : ℂ)‖ := by
            rw [norm_mul, norm_mul]
      _ ≤ ‖m ξ‖ * c * 1 := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left (hc ξ) (norm_nonneg _)
            · exact hPn
            · exact norm_nonneg _
            · exact mul_nonneg (norm_nonneg _) hc0
      _ = c * ‖m ξ‖ := by ring
  · have hzero : volume ({-(1/2:ℝ), (1/2:ℝ)} : Set ℝ) = 0 :=
      ((Set.finite_singleton (1/2:ℝ)).insert (-(1/2:ℝ))).measure_zero volume
    have hne : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ≠ -(1/2:ℝ) ∧ ξ ≠ (1/2:ℝ) := by
      rw [MeasureTheory.ae_iff]
      refine measure_mono_null ?_ hzero
      intro ξ hξ
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_contra hc
      rw [not_or] at hc
      exact hξ ⟨hc.1, hc.2⟩
    filter_upwards [hne] with ξ hξ
    obtain ⟨hξl, hξr⟩ := hξ
    by_cases hin : ξ ∈ Set.Icc (-(1/2:ℝ)) (1/2)
    · obtain ⟨hlo, hhi⟩ := hin
      have hlo' : -(1/2:ℝ) < ξ := lt_of_le_of_ne hlo (Ne.symm hξl)
      have hhi' : ξ < (1/2:ℝ) := lt_of_le_of_ne hhi hξr
      have hd : 0 < min (ξ + 1/2) ((1/2:ℝ) - ξ) := lt_min (by linarith) (by linarith)
      have h2 : Filter.Tendsto (fun j : ℕ => (j:ℝ) + 2) Filter.atTop Filter.atTop :=
        tendsto_atTop_add_const_right Filter.atTop (2:ℝ)
          (tendsto_natCast_atTop_atTop (R := ℝ))
      have htv : Filter.Tendsto (fun j : ℕ => (1:ℝ)/((j:ℝ)+2)) Filter.atTop (𝓝 0) :=
        h2.const_div_atTop 1
      have hev_lt : ∀ᶠ j : ℕ in Filter.atTop,
          (1:ℝ)/((j:ℝ)+2) < min (ξ + 1/2) ((1/2:ℝ) - ξ) :=
        (tendsto_order.1 htv).2 _ hd
      have hev1 : ∀ᶠ j : ℕ in Filter.atTop, plateau (1/((j:ℝ)+2)) ξ = 1 := by
        filter_upwards [hev_lt] with j hj
        exact plateau_eq_one_of_lt _ _ (by positivity) hj
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [hev1] with j hj
      rw [hj]
      simp
    · have hm0 : m ξ = 0 := hmsupp ξ hin
      simp only [hm0, zero_mul, mul_zero]
      exact tendsto_const_nhds

end Work.BourgainPlan.IonescuWainger
