import Mathlib
import Submission.Work.ZeroDensity.Ingham.AfeSelf.oscillatoryIocBound

namespace Work.ZeroDensity.Ingham.AfeSelf

open MeasureTheory Set Filter
open scoped Topology

/-- The norm of a real number embedded in `ℂ` is its absolute value. -/
private lemma norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, show r * r = r ^ 2 by ring]
  exact Real.sqrt_sq_eq_abs r

/-- A uniform bound on all finite interval integrals `∫_A^B f` passes to the integral over
`Ioi A`. -/
lemma ioiIntervalBoundAux {f : ℝ → ℂ} {A K : ℝ}
    (hfi : MeasureTheory.IntegrableOn f (Set.Ioi A))
    (hb : ∀ B, A ≤ B → ‖∫ x in A..B, f x‖ ≤ K) :
    ‖∫ x in Set.Ioi A, f x‖ ≤ K := by
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (f := f) A hfi tendsto_id
  have hnorm : Filter.Tendsto (fun B => ‖∫ x in A..B, f x‖) Filter.atTop
      (nhds ‖∫ x in Set.Ioi A, f x‖) := hlim.norm
  exact le_of_tendsto hnorm (Filter.eventually_atTop.mpr ⟨A, hb⟩)

theorem oscillatoryIoiBound {φ ψ χ w w' : ℝ → ℝ} {a μ : ℝ} (hμ : 0 < μ)
    (hφ : ∀ x ∈ Set.Ici a, HasDerivAt φ (ψ x) x)
    (hψ : ∀ x ∈ Set.Ici a, HasDerivAt ψ (χ x) x) (hχc : ContinuousOn χ (Set.Ici a))
    (hχ : ∀ x ∈ Set.Ici a, 0 ≤ χ x)
    (hψμ : ∀ x ∈ Set.Ici a, μ ≤ |ψ x|)
    (hw : ∀ x ∈ Set.Ici a, HasDerivAt w (w' x) x) (hw'c : ContinuousOn w' (Set.Ici a))
    (hw0 : ∀ x ∈ Set.Ici a, 0 ≤ w x) (hw' : ∀ x ∈ Set.Ici a, w' x ≤ 0)
    (hwint : MeasureTheory.IntegrableOn w (Set.Ioi a))
    (hw'int : MeasureTheory.IntegrableOn w' (Set.Ioi a))
    (hwt : Filter.Tendsto w Filter.atTop (nhds 0)) :
    ‖∫ x in Set.Ioi a, ((w x : ℝ) : ℂ) * Complex.exp (Complex.I * ((φ x : ℝ) : ℂ))‖ ≤ 4 * w a / μ := by
  have hφc : ContinuousOn φ (Set.Ici a) := HasDerivAt.continuousOn hφ
  have hwc : ContinuousOn w (Set.Ici a) := HasDerivAt.continuousOn hw
  have hgcont : ContinuousOn (fun t : ℝ => Complex.exp (Complex.I * ((φ t : ℝ) : ℂ)))
      (Set.Ici a) := by
    have h1 : ContinuousOn (fun t : ℝ => Complex.I * ((φ t : ℝ) : ℂ)) (Set.Ici a) :=
      (Complex.continuous_ofReal.comp_continuousOn' hφc).const_mul Complex.I
    exact Complex.continuous_exp.comp_continuousOn h1
  have hIoiIci : Set.Ioi a ⊆ Set.Ici a := by
    intro y hy
    exact le_of_lt (Set.mem_Ioi.mp hy)
  have hfcont : ContinuousOn
      (fun x : ℝ => ((w x : ℝ) : ℂ) * Complex.exp (Complex.I * ((φ x : ℝ) : ℂ)))
      (Set.Ioi a) :=
    (Complex.continuous_ofReal.comp_continuousOn' (hwc.mono hIoiIci)).mul
      (hgcont.mono hIoiIci)
  have hfint : MeasureTheory.IntegrableOn
      (fun x : ℝ => ((w x : ℝ) : ℂ) * Complex.exp (Complex.I * ((φ x : ℝ) : ℂ)))
      (Set.Ioi a) := by
    refine Integrable.mono' hwint (hfcont.aestronglyMeasurable isOpen_Ioi.measurableSet) ?_
    filter_upwards [self_mem_ae_restrict isOpen_Ioi.measurableSet] with x hx
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, norm_ofReal_complex]
    exact le_of_eq (abs_of_nonneg (hw0 x (le_of_lt (Set.mem_Ioi.mp hx))))
  have hb : ∀ B, a ≤ B → ‖∫ x in a..B,
      ((w x : ℝ) : ℂ) * Complex.exp (Complex.I * ((φ x : ℝ) : ℂ))‖ ≤ 4 * w a / μ := by
    intro B hB
    exact oscillatoryIocBound hB hμ
      (fun x hx => hφ x hx.1) (fun x hx => hψ x hx.1)
      (hχc.mono (fun x hx => hx.1)) (fun x hx => hχ x hx.1) (fun x hx => hψμ x hx.1)
      (fun x hx => hw x hx.1) (hw'c.mono (fun x hx => hx.1))
      (fun x hx => hw0 x hx.1) (fun x hx => hw' x hx.1)
  exact ioiIntervalBoundAux hfint hb

end Work.ZeroDensity.Ingham.AfeSelf
