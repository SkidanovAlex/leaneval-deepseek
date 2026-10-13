/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/Jeps_tendsto.lean` — `J_ε f → f` as `ε → 0⁺`

The mollifier `Jeps` of `StrongEps/Basic.lean` is, in the log coordinates
`s = log z`, `ζ = log tan θ`, the convolution with the rescaled kernel
`Jker ρ ε p = ε⁻¹ ^ 2 * ρ (ε⁻¹ • p)`:

  `Jeps ρ ε f z θ = ∫ p, Jker ρ ε p * f (Φ p)`,  `Φ p = (z e^{-p₁}, arctan (tan θ · e^{-p₂}))`.

`Φ` is a diffeomorphism of `ℝ²` onto the open region `(0,∞) × (0,π/2)`, with inverse

  `Ψ (u,v) = (log (z/u), log (tan θ / tan v))`.

The content of this module is that **`Φ` is quasi-measure-preserving** for Lebesgue measure.
Indeed, `Ψ` is differentiable on the whole open region, so by the Lusin `N` property of
differentiable maps (`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`) the image
of a null set under `Ψ` is null; splitting `ℝ²` into the balls of radius `n` and using
`Ψ ∘ Φ = id` gives `volume (Φ ⁻¹' N) = 0` for every null `N`.

Consequently `p ↦ f (Φ p)` is a.e. strongly measurable whenever `f` is, and the standard
peak-function argument applies: since `Jker ρ ε` is supported in the ball of radius `ε`,
nonnegative and has total mass one, and `f` is continuous at `(z,θ)`, the integral converges
to `f z θ`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Jker_integral_eq_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The shift `Φ` of the mollifier and its inverse `Ψ` -/

/-- The shift `p ↦ (z e^{-p₁}, arctan (tan θ · e^{-p₂}))` defining the point at which the profile
is evaluated in `Jeps`. -/
def sPhi (z θ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (zShift z p.1, thShift θ p.2)

/-- The inverse of `sPhi`, valid on the region `(0,∞) × (0,π/2)`.  (Written with `⁻¹` rather
than `/` so that its differentiability is stated in the same normal form.) -/
def sPsi (z θ : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  (Real.log (z * y.1⁻¹), Real.log (Real.tan θ * (Real.tan y.2)⁻¹))

theorem sPhi_apply (z θ : ℝ) (p : ℝ × ℝ) :
    sPhi z θ p = (z * Real.exp (-p.1), Real.arctan (Real.tan θ * Real.exp (-p.2))) := rfl

theorem continuous_sPhi (z θ : ℝ) : Continuous (sPhi z θ) :=
  continuous_shift_pair z θ

theorem sPhi_zero {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : sPhi z θ 0 = (z, θ) := by
  refine Prod.ext ?_ ?_
  · simp only [sPhi, zShift, Prod.fst_zero, neg_zero, Real.exp_zero, mul_one]
  · simp only [sPhi, thShift, Prod.snd_zero, neg_zero, Real.exp_zero, mul_one]
    exact Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2

/-- The shift maps every point into the open region `(0,∞) × (0,π/2)`. -/
theorem sPhi_mem {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (p : ℝ × ℝ) :
    (sPhi z θ p).1 ∈ Set.Ioi 0 ∧ (sPhi z θ p).2 ∈ Set.Ioo 0 (π / 2) :=
  ⟨zShift_pos hz, thShift_mem hθ⟩

/-! ## `Ψ ∘ Φ = id` -/

theorem sPsi_sPhi {z θ : ℝ} (hz : 0 < z) (ht : 0 < Real.tan θ) (p : ℝ × ℝ) :
    sPsi z θ (sPhi z θ p) = p := by
  have h1 : Real.log (z * ((sPhi z θ p).1)⁻¹) = p.1 := by
    have h : z * ((sPhi z θ p).1)⁻¹ = Real.exp p.1 := by
      simp only [sPhi, zShift]
      field_simp
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [h, Real.log_exp]
  have h2 : Real.log (Real.tan θ * (Real.tan ((sPhi z θ p).2))⁻¹) = p.2 := by
    have h : Real.tan θ * (Real.tan ((sPhi z θ p).2))⁻¹ = Real.exp p.2 := by
      simp only [sPhi, thShift, Real.tan_arctan]
      field_simp
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [h, Real.log_exp]
  exact Prod.ext h1 h2

/-! ## Differentiability of `Ψ` -/

theorem differentiableAt_sPsi {z θ : ℝ} (hz : 0 < z) (ht : 0 < Real.tan θ) {y : ℝ × ℝ}
    (hy1 : 0 < y.1) (hy2 : y.2 ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (sPsi z θ) y := by
  have hy1' : y.1 ≠ 0 := hy1.ne'
  have hty : Real.tan y.2 ≠ 0 := (Real.tan_pos_of_pos_of_lt_pi_div_two hy2.1 hy2.2).ne'
  have htz : Real.tan θ ≠ 0 := ht.ne'
  have hcos : Real.cos y.2 ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hy2.1, Real.pi_pos], by linarith [hy2.2]⟩).ne'
  have htan : DifferentiableAt ℝ (fun y : ℝ × ℝ => Real.tan y.2) y :=
    (Real.differentiableAt_tan.mpr hcos).comp y differentiableAt_snd
  have h1 : DifferentiableAt ℝ (fun y : ℝ × ℝ => z * (y.1)⁻¹) y :=
    (differentiableAt_const z).mul (differentiableAt_fst.inv hy1')
  have h2 : DifferentiableAt ℝ (fun y : ℝ × ℝ => Real.tan θ * (Real.tan y.2)⁻¹) y :=
    (differentiableAt_const (Real.tan θ)).mul (htan.inv hty)
  have h3 : DifferentiableAt ℝ (fun y : ℝ × ℝ => Real.log (z * (y.1)⁻¹)) y :=
    h1.log (mul_ne_zero hz.ne' (inv_ne_zero hy1'))
  have h4 : DifferentiableAt ℝ (fun y : ℝ × ℝ => Real.log (Real.tan θ * (Real.tan y.2)⁻¹)) y :=
    h2.log (mul_ne_zero htz (inv_ne_zero hty))
  exact h3.prodMk h4

/-! ## `Φ` is quasi-measure-preserving -/

theorem qmp_sPhi {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Measure.QuasiMeasurePreserving (sPhi z θ) volume volume := by
  have ht : 0 < Real.tan θ := Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2
  refine ⟨(continuous_sPhi z θ).measurable, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun s hs hvol => ?_
  rw [Measure.map_apply (continuous_sPhi z θ).measurable hs]
  have hsub : sPhi z θ ⁻¹' s ⊆
      ⋃ n : ℕ, sPsi z θ '' (s ∩ sPhi z θ '' Metric.closedBall (0 : ℝ × ℝ) (n : ℝ)) := by
    intro p hp
    refine mem_iUnion.mpr ⟨⌈‖p‖⌉₊, ?_⟩
    refine ⟨sPhi z θ p, ⟨hp, ⟨p, ?_, rfl⟩⟩, sPsi_sPhi hz ht p⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact Nat.le_ceil ‖p‖
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun n => ?_
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero (μ := volume) ?_ ?_
  · intro y hy
    obtain ⟨-, p, -, rfl⟩ := hy
    exact (differentiableAt_sPsi hz ht (sPhi_mem hz hθ p).1
      (sPhi_mem hz hθ p).2).differentiableWithinAt
  · exact measure_mono_null inter_subset_left hvol

/-! ## The peak-function argument in the `p`-coordinates -/

/-- **A fixed profile against the shrinking kernel.**  If `A` is a.e. strongly measurable, has a
limit `w` at `0` and `A 0 = w`, then `∫ p, Jker ρ ε p * A p → w` as `ε → 0⁺`. -/
theorem tendsto_integral_Jker_mul (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {A : ℝ × ℝ → ℝ}
    {w : ℝ} (hA : AEStronglyMeasurable A volume) (h0 : A 0 = w)
    (hAc : Filter.Tendsto A (𝓝 0) (𝓝 w)) :
    Filter.Tendsto (fun ε : ℝ => ∫ p : ℝ × ℝ, Jker ρ ε p * A p) (nhdsWithin 0 (Set.Ioi 0))
      (nhds w) := by
  have hAc' : ContinuousAt A 0 := by
    change Filter.Tendsto A (𝓝 0) (𝓝 (A 0))
    rw [h0]
    exact hAc
  rw [← h0]
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨r, hr, hbd⟩ := Metric.continuousAt_iff.mp hAc' (η / 2) (by linarith)
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < r / 2 by linarith)] with ε hε
  have hεpos : 0 < ε := hε.1
  have hεle : ε ≤ r / 2 := hε.2
  rw [Real.dist_eq]
  have hJint : Integrable (Jker ρ ε) := Jker_integrable hρ hεpos
  have hJmass : ∫ p : ℝ × ℝ, Jker ρ ε p = 1 := Jker_integral_eq_one ρ hρ hεpos
  have hJnn : ∀ p : ℝ × ℝ, 0 ≤ Jker ρ ε p := fun p => by
    simp only [Jker]
    exact mul_nonneg (by positivity) (hρ.nonneg (ε⁻¹ • p))
  have hclose : ∀ p : ℝ × ℝ, Jker ρ ε p ≠ 0 → |A p - A 0| < η / 2 := by
    intro p hp
    have hmem : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε := by
      by_contra hc
      exact hp (Jker_eq_zero_of_not_mem hρ hεpos hc)
    have hd : dist p 0 < r :=
      lt_of_le_of_lt (Metric.mem_closedBall.mp hmem) (by linarith)
    have h := hbd hd
    rwa [Real.dist_eq] at h
  have hInt : Integrable (fun p : ℝ × ℝ => Jker ρ ε p * A p) := by
    refine Integrable.mono' (hJint.mul_const (‖A 0‖ + η / 2)) ?_ ?_
    · exact ((Jker_continuous hρ ε).aestronglyMeasurable).mul hA
    · filter_upwards with p
      by_cases hp : Jker ρ ε p = 0
      · simp [hp]
      · have hp' := hclose p hp
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hJnn p)]
        have hb : ‖A p‖ ≤ ‖A 0‖ + η / 2 := by
          have h1 : ‖A p‖ ≤ ‖A p - A 0‖ + ‖A 0‖ := by
            simpa only [sub_add_cancel] using norm_add_le (A p - A 0) (A 0)
          have h2 : ‖A p - A 0‖ ≤ η / 2 := by
            rw [Real.norm_eq_abs]; exact hp'.le
          linarith
        exact mul_le_mul_of_nonneg_left hb (hJnn p)
  have hsplit : ∫ p : ℝ × ℝ, Jker ρ ε p * (A p - A 0)
      = (∫ p : ℝ × ℝ, Jker ρ ε p * A p) - A 0 := by
    have heq : (fun p : ℝ × ℝ => Jker ρ ε p * (A p - A 0))
        = fun p : ℝ × ℝ => Jker ρ ε p * A p - Jker ρ ε p * A 0 := by
      funext p
      ring
    rw [heq, integral_sub hInt (hJint.mul_const _), integral_mul_const, hJmass, one_mul]
  rw [← hsplit, ← Real.norm_eq_abs]
  have hbound_eq : ∫ p : ℝ × ℝ, Jker ρ ε p * (η / 2) = η / 2 := by
    rw [integral_mul_const, hJmass, one_mul]
  have hae : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      ‖Jker ρ ε p * (A p - A 0)‖ ≤ Jker ρ ε p * (η / 2) := by
    filter_upwards with p
    by_cases hp : Jker ρ ε p = 0
    · simp [hp]
    · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hJnn p)]
      exact mul_le_mul_of_nonneg_left (le_of_lt (hclose p hp)) (hJnn p)
  have hb : ‖∫ p : ℝ × ℝ, Jker ρ ε p * (A p - A 0)‖ ≤ η / 2 :=
    (norm_integral_le_of_norm_le (hJint.mul_const (η / 2)) hae).trans (le_of_eq hbound_eq)
  linarith

/-! ## The target -/

theorem Jeps_tendsto (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hfc : ContinuousAt (Function.uncurry f) (z, θ))
    (hfm : MeasureTheory.AEStronglyMeasurable (Function.uncurry f) volume) :
    Filter.Tendsto (fun ε : ℝ => Jeps ρ ε f z θ) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (f z θ)) := by
  have hAesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => f (z * Real.exp (-p.1))
        (Real.arctan (Real.tan θ * Real.exp (-p.2)))) volume := by
    have h := hfm.comp_quasiMeasurePreserving (qmp_sPhi hz hθ)
    simpa only [Function.comp_def, Function.uncurry, sPhi, zShift, thShift] using h
  have hAc : Filter.Tendsto
      (fun p : ℝ × ℝ => f (z * Real.exp (-p.1))
        (Real.arctan (Real.tan θ * Real.exp (-p.2)))) (𝓝 0) (𝓝 (f z θ)) := by
    have hcont : Filter.Tendsto (sPhi z θ) (𝓝 0) (𝓝 (z, θ)) := by
      have h : Filter.Tendsto (sPhi z θ) (𝓝 0) (𝓝 (sPhi z θ 0)) :=
        (continuous_sPhi z θ).continuousAt
      rwa [sPhi_zero hθ] at h
    have h : Filter.Tendsto (Function.uncurry f) (𝓝 (z, θ)) (𝓝 (f z θ)) := hfc
    have h' := h.comp hcont
    simpa only [Function.comp_def, Function.uncurry, sPhi, zShift, thShift] using h'
  have h0 : (fun p : ℝ × ℝ => f (z * Real.exp (-p.1))
      (Real.arctan (Real.tan θ * Real.exp (-p.2)))) 0 = f z θ := by
    simp only [Prod.fst_zero, Prod.snd_zero, neg_zero, Real.exp_zero, mul_one]
    rw [Real.arctan_tan (by linarith [hθ.1, Real.pi_pos]) hθ.2]
  refine (tendsto_integral_Jker_mul ρ hρ hAesm h0 hAc).congr' ?_
  filter_upwards with ε
  rw [Jeps_eq_integral ρ ε f hz hθ]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [zShift, thShift]

end Work.FTS.StrongEps
