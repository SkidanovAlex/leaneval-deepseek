import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.Harmonic.GammaDeriv

noncomputable section

open Filter Set MeasureTheory
open scoped Topology Interval

namespace Commons.Analysis.ExpLog

/-! # The limit of the tail integral `∫_c^∞ log u · e^{-u} du` as `c → 0⁺`

We prove that
`Tendsto (fun c => ∫ u in Ioi c, log u * exp (-u)) (𝓝[>0] 0) (𝓝 (-γ))`,
i.e. the (Lebesgue) improper integral `∫₀^∞ log u · e^{-u} du` is `-γ`
(Euler-Mascheroni), and the tail integrals are right-continuous at `0`.

The value `-γ` is obtained from the derivative of the complex Gamma function at `1`
(`Γ'(1) = ∫₀^∞ log t · e^{-t} dt = -γ`); right-continuity of the tail comes from
`IntegrableOn.continuousWithinAt_Ici_primitive_Ioi`. -/

/-! ## Integrability of `log u * exp (-u)` on `(0, ∞)` -/

private lemma log_integrableOn_Ioc_zero_one :
    IntegrableOn (fun u : ℝ => Real.log u) (Set.Ioc (0 : ℝ) 1) := by
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))

private lemma log_exp_continuousOn_Ioc_zero_one :
    ContinuousOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioc (0 : ℝ) 1) := by
  refine (Real.continuousOn_log.mono ?_).mul ?_
  · intro u hu
    simp only [mem_Ioc, mem_compl_iff, mem_singleton_iff] at hu ⊢
    exact ne_of_gt hu.1
  · exact (Real.continuousOn_exp : ContinuousOn Real.exp (Set.univ : Set ℝ)).comp
      (continuousOn_id.neg : ContinuousOn (fun u : ℝ => -u) (Set.Ioc (0 : ℝ) 1))
      (by intro u hu; exact trivial)

private lemma integrableOn_log_exp_neg_Ioc_zero_one :
    IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioc (0 : ℝ) 1) := by
  have hlog : IntegrableOn (fun u : ℝ => Real.log u) (Set.Ioc (0 : ℝ) 1) :=
    log_integrableOn_Ioc_zero_one
  have hmeas : AEStronglyMeasurable (fun u : ℝ => Real.log u * Real.exp (-u))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    exact ContinuousOn.aestronglyMeasurable log_exp_continuousOn_Ioc_zero_one measurableSet_Ioc
  have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)),
      ‖Real.log u * Real.exp (-u)‖ ≤ ‖Real.log u‖ := by
    apply (ae_restrict_mem measurableSet_Ioc).mono
    intro u hu
    have h1 : 0 ≤ Real.exp (-u) := (Real.exp_pos (-u)).le
    have h2 : Real.exp (-u) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr hu.1.le
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc
      |Real.log u * Real.exp (-u)| = |Real.log u| * |Real.exp (-u)| := abs_mul _ _
      _ = |Real.log u| * Real.exp (-u) := by rw [abs_of_nonneg h1]
      _ ≤ |Real.log u| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = |Real.log u| := by rw [mul_one]
  exact Integrable.mono hlog hmeas hbound

private lemma u_exp_neg_integrableOn_Ioi_one :
    IntegrableOn (fun u : ℝ => u * Real.exp (-u)) (Set.Ioi (1 : ℝ)) := by
  have h := Real.GammaIntegral_convergent (s := (2 : ℝ)) (by norm_num)
  have hm : IntegrableOn (fun u : ℝ => u * Real.exp (-u)) (Set.Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun_ae h ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    norm_num
    rw [mul_comm]
  exact hm.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))

private lemma log_le_u_of_one_lt {u : ℝ} (hu : 1 < u) : Real.log u ≤ u := by
  have h1 : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos (by linarith)
  linarith

private lemma integrableOn_log_exp_neg_Ioi_one :
    IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioi 1) := by
  have hb : IntegrableOn (fun u : ℝ => u * Real.exp (-u)) (Set.Ioi (1 : ℝ)) :=
    u_exp_neg_integrableOn_Ioi_one
  have hmeas : AEStronglyMeasurable (fun u : ℝ => Real.log u * Real.exp (-u))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (Real.continuousOn_log.mono ?_).mul ?_
    · intro u hu
      simp only [mem_Ioi, mem_compl_iff, mem_singleton_iff] at hu ⊢
      exact ne_of_gt (by linarith : (0 : ℝ) < u)
    · exact (Real.continuousOn_exp : ContinuousOn Real.exp (Set.univ : Set ℝ)).comp
        (continuousOn_id.neg : ContinuousOn (fun u : ℝ => -u) (Set.Ioi (1 : ℝ)))
        (by intro u hu; exact trivial)
  have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioi (1 : ℝ))),
      ‖Real.log u * Real.exp (-u)‖ ≤ ‖u * Real.exp (-u)‖ := by
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro u hu
    have hu1 : 1 < u := hu
    have hu0 : 0 < u := by linarith
    have habs : |Real.log u * Real.exp (-u)| = Real.log u * Real.exp (-u) := by
      rw [abs_mul, abs_of_nonneg (Real.log_nonneg (by linarith)),
        abs_of_nonneg (Real.exp_pos (-u)).le]
    have hineq : Real.log u * Real.exp (-u) ≤ u * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right (log_le_u_of_one_lt hu1) (Real.exp_pos (-u)).le
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [habs, abs_of_nonneg (mul_nonneg hu0.le (Real.exp_pos (-u)).le)]
    exact hineq
  exact Integrable.mono hb hmeas hbound

/-- `u ↦ log u * exp (-u)` is integrable on `(0, ∞)`. -/
private lemma integrableOn_log_exp_neg_Ioi_zero :
    IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioi (0 : ℝ)) := by
  have h1 : IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioc (0 : ℝ) 1) :=
    integrableOn_log_exp_neg_Ioc_zero_one
  have h2 : IntegrableOn (fun u : ℝ => Real.log u * Real.exp (-u)) (Set.Ioi 1) :=
    integrableOn_log_exp_neg_Ioi_one
  simpa [Set.Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)] using h1.union h2

/-! ## The value `∫₀^∞ log u · e^{-u} du = -γ` -/

/-- `Γ'(1) = ∫₀^∞ log t · e^{-t} dt` over the complex numbers, and both equal `-γ`. -/
private lemma integral_log_exp_neg_Ioi_complex :
    (∫ u : ℝ in Set.Ioi 0, (Real.log u * Real.exp (-u) : ℂ)) = -↑Real.eulerMascheroniConstant := by
  have hGI := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  have hsim : (∫ (t : ℝ) in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))) =
      (∫ (t : ℝ) in Ioi 0, (Real.log t * Real.exp (-t) : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    norm_num
  have hEq : Complex.Gamma =ᶠ[𝓝 (1 : ℂ)] Complex.GammaIntegral := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
    filter_upwards [hopen.mem_nhds (by norm_num : 0 < (1 : ℂ).re)] with z hz
    exact Complex.Gamma_eq_integral hz
  have hGamma : HasDerivAt Complex.Gamma
      (∫ (t : ℝ) in Ioi 0, (Real.log t * Real.exp (-t) : ℂ)) (1 : ℂ) := by
    have hGI' : HasDerivAt Complex.GammaIntegral
        (∫ (t : ℝ) in Ioi 0, (Real.log t * Real.exp (-t) : ℂ)) (1 : ℂ) := by
      simpa [hsim] using hGI
    exact hGI'.congr_of_eventuallyEq hEq
  have hone : HasDerivAt Complex.Gamma (-↑Real.eulerMascheroniConstant) (1 : ℂ) :=
    Complex.hasDerivAt_Gamma_one
  exact hGamma.deriv ▸ hone.deriv ▸ rfl

/-- `∫₀^∞ log u · e^{-u} du = -γ`, where `γ` is Euler-Mascheroni. -/
private lemma integral_log_exp_neg_Ioi_zero :
    (∫ u : ℝ in Set.Ioi 0, Real.log u * Real.exp (-u)) = -Real.eulerMascheroniConstant := by
  have hre : (∫ u : ℝ in Set.Ioi 0, (Real.log u * Real.exp (-u) : ℂ)) =
      ↑(∫ u : ℝ in Set.Ioi 0, Real.log u * Real.exp (-u)) := by
    simpa using (integral_ofReal (𝕜 := ℂ) (μ := volume.restrict (Set.Ioi 0))
      (f := fun u : ℝ => Real.log u * Real.exp (-u)))
  have hc := integral_log_exp_neg_Ioi_complex
  rw [hre] at hc
  rw [← Complex.ofReal_neg] at hc
  exact Complex.ofReal_inj.mp hc

/-! ## The main statement -/

/-- The tail integral `c ↦ ∫_c^∞ log u · e^{-u} du` tends to `-γ` as `c → 0⁺`.

This is the `∫₀^∞` Euler integral for `Γ'(1) = -γ`, expressed as a limit of Lebesgue
integrals over `Ioi c` (which make sense for `c > 0`). -/
lemma tendsto_integral_log_exp_neg_Ioi :
    Filter.Tendsto (fun c : ℝ => ∫ u : ℝ in Set.Ioi c, Real.log u * Real.exp (-u))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (-Real.eulerMascheroniConstant)) := by
  let f : ℝ → ℝ := fun u => Real.log u * Real.exp (-u)
  have hf : IntegrableOn f (Set.Ioi (0 : ℝ)) := by
    simpa [f] using integrableOn_log_exp_neg_Ioi_zero
  have hcont : ContinuousWithinAt (fun b : ℝ => ∫ x : ℝ in Set.Ioi b, f x)
      (Set.Ici (0 : ℝ)) (0 : ℝ) := by
    exact MeasureTheory.IntegrableOn.continuousWithinAt_Ici_primitive_Ioi (a₀ := (0 : ℝ)) hf
  have hfin : Tendsto (fun b : ℝ => ∫ x : ℝ in Set.Ioi b, f x)
      (𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ)) (𝓝 (∫ x : ℝ in Set.Ioi (0 : ℝ), f x)) := by
    exact hcont.mono_left (nhdsWithin_mono (0 : ℝ) Set.Ioi_subset_Ici_self)
  have hval : (∫ x : ℝ in Set.Ioi 0, f x) = -Real.eulerMascheroniConstant := by
    simpa [f] using integral_log_exp_neg_Ioi_zero
  rw [hval] at hfin
  simpa [f] using hfin

end Commons.Analysis.ExpLog