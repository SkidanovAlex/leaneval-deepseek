import Mathlib
import Submission.Work.TMComp.MAnalytic.deriv_bound

/-!
# Holomorphy of the interval integral `z ↦ ∫₀¹ F (z, x) · exp (-2πi k x) dx`

Proof that the Fourier-coefficient-type parametric integral
`z ↦ ∫₀¹ F (z, (x : ℂ)) * exp (-(2 * π * I * k * x)) dx` is holomorphic on `Δ`, where `F` is
complex differentiable on the tube `Δ × {|Im| < ρ}` (`ρ > 0`).

The argument is the classical differentiation-under-the-integral-sign for a holomorphic
parameter, applied with the parametric interval-integral theorem
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.  The uniform bound on the
derivatives is Cauchy's estimate (`Work.TMComp.MAnalytic.deriv_bound`), and measurability of the
differentiated integrand is obtained from the fact that `x ↦ fderiv ℂ F (z₀, x) (1,0)` is
measurable (`measurable_fderiv_apply_const`).

This is the Ten Martini Problem's component C11 auxiliary lemma
`differentiableOn_intervalIntegral_kernel`.
-/

open MeasureTheory intervalIntegral Metric
open scoped Topology Interval

noncomputable section

namespace Work.TMComp.RedProj

/-- The tube `Δ × {|Im| < ρ}` inside `ℂ × ℂ`. -/
def tube (Δ : Set ℂ) (ρ : ℝ) : Set (ℂ × ℂ) := {p | p.1 ∈ Δ ∧ |p.2.im| < ρ}

/-- The Fourier kernel `x ↦ exp (-(2πi k x))`, of modulus one. -/
def kern (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))

theorem kern_norm (k : ℤ) (x : ℝ) : ‖kern k x‖ = 1 := by
  rw [kern]
  have h : -(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ))
      = ((-(2 * Real.pi * (k : ℝ) * x) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem kern_continuous (k : ℤ) : Continuous (kern k) := by
  unfold kern
  fun_prop

theorem isOpen_tube {Δ : Set ℂ} (hΔ : IsOpen Δ) (ρ : ℝ) : IsOpen (tube Δ ρ) := by
  have h1 : IsOpen {p : ℂ × ℂ | p.1 ∈ Δ} := hΔ.preimage continuous_fst
  have h2 : IsOpen {p : ℂ × ℂ | |p.2.im| < ρ} :=
    isOpen_lt (f := fun p : ℂ × ℂ => |p.2.im|) (g := fun _ => ρ)
      (continuous_abs.comp (Complex.continuous_im.comp continuous_snd)) continuous_const
  have : tube Δ ρ = {p : ℂ × ℂ | p.1 ∈ Δ} ∩ {p : ℂ × ℂ | |p.2.im| < ρ} := by
    ext p; simp [tube]
  rw [this]; exact h1.inter h2

/-- The complexified real interval lies in the tube, provided `0 < ρ`. -/
theorem ofReal_mem_tube {Δ : Set ℂ} {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (hz : z ∈ Δ) (t : ℝ) :
    (z, (t : ℂ)) ∈ tube Δ ρ := by
  simp only [tube, Set.mem_ofPred_eq, Complex.ofReal_im, abs_zero]
  exact ⟨hz, hρ⟩

/-- For fixed `z ∈ Δ`, the slice `x ↦ F (z, x)` is continuous on `ℝ`. -/
theorem continuous_slice (F : ℂ × ℂ → ℂ) (Δ : Set ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hF : DifferentiableOn ℂ F (tube Δ ρ)) {z : ℂ} (hz : z ∈ Δ) :
    Continuous (fun x : ℝ => F (z, (x : ℂ))) :=
  hF.continuousOn.comp_continuous (by fun_prop) (fun x => ofReal_mem_tube hρ hz x)

/-- For fixed `c` with `|Im c| < ρ`, the slice `z ↦ F (z, c)` is holomorphic on `Δ`. -/
theorem differentiableOn_slice (F : ℂ × ℂ → ℂ) (Δ : Set ℂ) (ρ : ℝ)
    (hF : DifferentiableOn ℂ F (tube Δ ρ)) {c : ℂ} (hc : |c.im| < ρ) :
    DifferentiableOn ℂ (fun z : ℂ => F (z, c)) Δ := by
  intro z hz
  have hU : (z, c) ∈ tube Δ ρ := by
    simp only [tube, Set.mem_ofPred_eq]
    exact ⟨hz, hc⟩
  have h1 : DifferentiableWithinAt ℂ (fun w : ℂ => (w, c)) Δ z := by
    simpa using (differentiableWithinAt_id.prodMk (differentiableWithinAt_const (x := z) (s := Δ) c))
  refine (hF (z, c) hU).comp z h1 (fun w hw => ?_)
  simp only [tube, Set.mem_ofPred_eq]
  exact ⟨hw, hc⟩

/-- Pointwise version of `differentiableOn_slice`. -/
theorem differentiableAt_slice (F : ℂ × ℂ → ℂ) (Δ : Set ℂ) (ρ : ℝ) (hΔ : IsOpen Δ)
    (hF : DifferentiableOn ℂ F (tube Δ ρ)) {z c : ℂ} (hz : z ∈ Δ) (hc : |c.im| < ρ) :
    DifferentiableAt ℂ (fun w : ℂ => F (w, c)) z :=
  (differentiableOn_slice F Δ ρ hF hc).differentiableAt (hΔ.mem_nhds hz)

/-- Derivative of a slice, computed through the Fréchet derivative of `F`. -/
theorem deriv_slice_eq (F : ℂ × ℂ → ℂ) {z c : ℂ} (h : DifferentiableAt ℂ F (z, c)) :
    deriv (fun w : ℂ => F (w, c)) z = (fderiv ℂ F (z, c)) (1, 0) := by
  have h1 : HasDerivAt (fun w : ℂ => (w, c)) (1, 0) z :=
    (hasDerivAt_id z).prodMk (hasDerivAt_const z c)
  have h2 : HasDerivAt (fun w : ℂ => F (w, c)) ((fderiv ℂ F (z, c)) (1, 0)) z :=
    h.hasFDerivAt.comp_hasDerivAt z h1
  exact h2.deriv

/-- The derivative of the `z`-slice of `F` at `z₀` is a measurable function of the real
parameter `x` (the second coordinate is `(x : ℂ)`). -/
theorem measurable_deriv_slice (F : ℂ × ℂ → ℂ) (Δ : Set ℂ) (ρ : ℝ) (hΔ : IsOpen Δ) (hρ : 0 < ρ)
    (hF : DifferentiableOn ℂ F (tube Δ ρ)) (z₀ : ℂ) (hz₀ : z₀ ∈ Δ) :
    Measurable (fun x : ℝ => deriv (fun w : ℂ => F (w, (x : ℂ))) z₀) := by
  have hreal : ∀ x : ℝ, |((x : ℂ)).im| < ρ := fun x => by
    rw [Complex.ofReal_im, abs_zero]; exact hρ
  have h1 : Measurable (fun x : ℝ => (fderiv ℂ F (z₀, (x : ℂ))) (1, 0)) :=
    (measurable_fderiv_apply_const ℂ F (1, 0)).comp
      ((continuous_const.prodMk Complex.continuous_ofReal).measurable)
  have hfun : (fun x : ℝ => deriv (fun w : ℂ => F (w, (x : ℂ))) z₀)
      = fun x : ℝ => (fderiv ℂ F (z₀, (x : ℂ))) (1, 0) :=
    funext fun x => deriv_slice_eq F
      ((hF (z₀, (x : ℂ)) (ofReal_mem_tube hρ hz₀ x)).differentiableAt
        ((isOpen_tube hΔ ρ).mem_nhds (ofReal_mem_tube hρ hz₀ x)))
  rw [hfun]
  exact h1

/-- **Holomorphy of the parametric Fourier integral.** -/
theorem differentiableOn_intervalIntegral_kernel (F : ℂ × ℂ → ℂ) (Δ : Set ℂ) (ρ : ℝ)
    (hΔ : IsOpen Δ) (hρ : 0 < ρ)
    (hF : DifferentiableOn ℂ F {p : ℂ × ℂ | p.1 ∈ Δ ∧ |p.2.im| < ρ}) (k : ℤ) :
    DifferentiableOn ℂ
      (fun z : ℂ => ∫ x in (0 : ℝ)..1,
        F (z, (x : ℂ)) * Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * (x : ℂ)))) Δ := by
  intro z₀ hz₀
  show DifferentiableWithinAt ℂ
    (fun z : ℂ => ∫ x in (0 : ℝ)..1, F (z, (x : ℂ)) * kern k x) Δ z₀
  -- A uniform bound on the slice derivatives near `z₀`, by Cauchy's estimate.
  have hg : ContinuousOn (fun p : ℂ × ℝ => F (p.1, ((p.2 : ℝ) : ℂ))) (Δ ×ˢ Set.univ) := by
    refine hF.continuousOn.comp ?_ ?_
    · fun_prop
    · rintro ⟨z, x⟩ ⟨hz, -⟩
      exact ofReal_mem_tube hρ hz x
  have hhol : ∀ x : ℝ, DifferentiableOn ℂ (fun z : ℂ => F (z, ((x : ℝ) : ℂ))) Δ := fun x =>
    differentiableOn_slice F Δ ρ hF (by rw [Complex.ofReal_im, abs_zero]; exact hρ)
  obtain ⟨r, hr, hsub, K, _hK0, hK⟩ := Work.TMComp.MAnalytic.deriv_bound hΔ hg hhol hz₀
  have hεr : (0 : ℝ) < r / 2 := by linarith
  have hball : Metric.ball z₀ (r / 2) ⊆ Δ := by
    intro z hz
    refine hsub ?_
    rw [Metric.mem_closedBall]
    have := Metric.mem_ball.mp hz
    linarith
  -- Measurability of the integrand for `z` near `z₀`.
  have hFmeas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (fun t : ℝ => F (z, (t : ℂ)) * kern k t)
        (volume.restrict (Ι (0 : ℝ) 1)) := by
    filter_upwards [Metric.ball_mem_nhds z₀ hεr] with z hz
    exact ((continuous_slice F Δ ρ hρ hF (hball hz)).mul (kern_continuous k)).aestronglyMeasurable
  -- Integrability of the integrand at `z₀`.
  have hFint : IntervalIntegrable (fun t : ℝ => F (z₀, (t : ℂ)) * kern k t) volume 0 1 :=
    ((continuous_slice F Δ ρ hρ hF hz₀).mul (kern_continuous k)).intervalIntegrable 0 1
  -- Measurability of the differentiated integrand.
  have hF'meas : AEStronglyMeasurable
      (fun t : ℝ => deriv (fun w : ℂ => F (w, (t : ℂ))) z₀ * kern k t)
      (volume.restrict (Ι (0 : ℝ) 1)) :=
    ((measurable_deriv_slice F Δ ρ hΔ hρ hF z₀ hz₀).mul
      (kern_continuous k).measurable).aestronglyMeasurable
  -- The uniform bound.
  have hbound : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 →
      ∀ z ∈ Metric.ball z₀ (r / 2),
        ‖deriv (fun w : ℂ => F (w, (t : ℂ))) z * kern k t‖ ≤ K := by
    filter_upwards with t ht z hz
    rw [norm_mul, kern_norm k t, mul_one]
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := by
      have h1 : t ∈ Set.uIoc (0 : ℝ) 1 := ht
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h1
      exact Set.Ioc_subset_Icc_self h1
    refine hK t htI z ?_
    rw [Metric.mem_closedBall]
    exact (Metric.mem_ball.mp hz).le
  have hbint : IntervalIntegrable (fun _ : ℝ => K) volume (0 : ℝ) 1 := intervalIntegrable_const
  -- Differentiability of the integrand in `z`.
  have hdiff : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) 1 → ∀ z ∈ Metric.ball z₀ (r / 2),
      HasDerivAt (fun z : ℂ => F (z, (t : ℂ)) * kern k t)
        (deriv (fun w : ℂ => F (w, (t : ℂ))) z * kern k t) z := by
    filter_upwards with t ht z hz
    have hc : |((t : ℂ)).im| < ρ := by rw [Complex.ofReal_im, abs_zero]; exact hρ
    exact (differentiableAt_slice F Δ ρ hΔ hF (hball hz) hc).hasDerivAt.mul_const (kern k t)
  have key : HasDerivAt
      (fun z : ℂ => ∫ t in (0 : ℝ)..1, F (z, (t : ℂ)) * kern k t)
      (∫ t in (0 : ℝ)..1, deriv (fun w : ℂ => F (w, (t : ℂ))) z₀ * kern k t) z₀ :=
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := (0 : ℝ)) (b := 1) (bound := fun _ => K) (x₀ := z₀)
      (s := Metric.ball z₀ (r / 2))
      (F := fun z t => F (z, (t : ℂ)) * kern k t)
      (F' := fun z t => deriv (fun w : ℂ => F (w, (t : ℂ))) z * kern k t)
      (Metric.ball_mem_nhds z₀ hεr) hFmeas hFint hF'meas hbound hbint hdiff).2
  exact key.differentiableAt.differentiableWithinAt

end Work.TMComp.RedProj
