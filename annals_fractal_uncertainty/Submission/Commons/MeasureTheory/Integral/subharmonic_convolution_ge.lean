import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.RingTheory.Finiteness.Prod

namespace Commons.MeasureTheory.Integral

set_option autoImplicit false

open _root_.MeasureTheory _root_.Metric _root_.Set _root_.Filter _root_.Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace

noncomputable section

/-! ## Auxiliary lemmas -/

/-- `Complex.exp (θ * I)` is `-1`-periodic in the sense used for the substitution
`θ ↦ θ + π`. -/
lemma complex_exp_add_pi (θ : ℝ) :
    Complex.exp ((θ + Real.pi : ℝ) * Complex.I) = - Complex.exp (θ * Complex.I) := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- The polar-coordinate parametrisation of `ℂ` (as a function of `(r, θ)`) coincides with
`r * exp (θ * I)`. -/
lemma complex_polarCoord_symm_eq (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = (p.1 : ℂ) * Complex.exp (p.2 * Complex.I) := by
  rw [Complex.polarCoord_symm_apply, Complex.exp_ofReal_mul_I]

/-- The linear shear of the polar parametrisation of `ℝ²` written in `ℂ`. -/
lemma measurableEquivRealProd_polarCoord_symm (p : ℝ × ℝ) :
    Complex.measurableEquivRealProd.symm (polarCoord.symm p)
      = (p.1 : ℂ) * Complex.exp (p.2 * Complex.I) := by
  rw [polarCoord_symm_apply, Complex.measurableEquivRealProd_symm_apply,
    Complex.exp_ofReal_mul_I]
  show (Complex.mk (p.1 * Real.cos p.2) (p.1 * Real.sin p.2)) = _
  rw [Complex.ext_iff]
  constructor <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  · ring
  · ring

/-- **Integrability transfer through the polar homeomorphism.**  If `F : ℂ → ℝ` is
integrable, then `(r, θ) ↦ r * F (r * exp (θ * I))` is integrable on the fundamental
domain `(0, ∞) × (-π, π)`. -/
lemma integrableOn_polar_of_integrable {F : ℂ → ℝ} (hF : Integrable F volume) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * F (p.1 * Complex.exp (p.2 * Complex.I)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) volume := by
  have ht' : (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi : Set (ℝ × ℝ)) = polarCoord.target :=
    polarCoord_target.symm
  set F' : ℝ × ℝ → ℝ := fun q => F (Complex.measurableEquivRealProd.symm q) with hF'def
  have hF'int : Integrable F' volume := by
    have h := (Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding (g := F))
    exact h.mpr hF
  have hF'src : IntegrableOn F' polarCoord.source volume := by
    have h := (integrableOn_congr_set_ae (f := F') polarCoord_source_ae_eq_univ).mpr
    exact h (by simpa using hF'int)
  have hinj : Set.InjOn (⇑polarCoord.symm) polarCoord.target := by
    simpa using polarCoord.symm.injOn
  have hkey := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (μ := volume)
      (f := ⇑polarCoord.symm) (f' := fderivPolarCoordSymm) (s := polarCoord.target)
      polarCoord.open_target.measurableSet
      (fun x hx => (hasFDerivAt_polarCoord_symm x).hasFDerivWithinAt)
      hinj (g := F'))
  have himg : ⇑polarCoord.symm '' polarCoord.target = polarCoord.source := by
    have h := PartialEquiv.image_source_eq_target polarCoord.symm.toPartialEquiv
    simpa using h
  rw [himg] at hkey
  have hres : IntegrableOn (fun x : ℝ × ℝ => |(fderivPolarCoordSymm x).det| • F' (polarCoord.symm x))
      polarCoord.target volume := hkey.mp hF'src
  have hres' : IntegrableOn (fun p : ℝ × ℝ => p.1 * F (p.1 * Complex.exp (p.2 * Complex.I)))
      polarCoord.target volume := by
    refine hres.congr_fun ?_ polarCoord.open_target.measurableSet
    intro p hp
    change |(fderivPolarCoordSymm p).det| • F' (polarCoord.symm p)
      = p.1 * F (p.1 * Complex.exp (p.2 * Complex.I))
    rw [det_fderivPolarCoordSymm, abs_of_pos hp.1, smul_eq_mul]
    congr 1
    rw [hF'def]
    simp only []
    congr 1
    exact measurableEquivRealProd_polarCoord_symm p
  rwa [← ht'] at hres'

/-- **Polar-coordinate change of variables in `ℂ`.**  For an integrable `F : ℂ → ℝ`, the
integral of `F` over `ℂ` is the iterated integral over `(r, θ) ∈ (0, ∞) × (-π, π)` of
`r * F (r * exp (θ * I))`. -/
lemma integral_complex_eq_integral_angle {F : ℂ → ℝ} (hF : Integrable F volume) :
    (∫ z : ℂ, F z) = ∫ r in Set.Ioi (0:ℝ), r * ∫ θ in (-Real.pi)..Real.pi,
        F ((r:ℂ) * Complex.exp (θ * Complex.I)) := by
  rw [← Complex.integral_comp_polarCoord_symm F]
  rw [polarCoord_target]
  have hfun : (fun p : ℝ × ℝ => p.1 • F (Complex.polarCoord.symm p))
      = (fun p : ℝ × ℝ => p.1 * F (p.1 * Complex.exp (p.2 * Complex.I))) := by
    funext p
    rw [complex_polarCoord_symm_eq p, smul_eq_mul]
  rw [hfun]
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 * F (p.1 * Complex.exp (p.2 * Complex.I)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact integrableOn_polar_of_integrable hF
  rw [Measure.volume_eq_prod ℝ ℝ]
  rw [setIntegral_prod _ hint]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp only []
  rw [integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_of_le (a := -Real.pi) (b := Real.pi)
      (by linarith [Real.pi_pos])]
  exact setIntegral_congr_set Ioo_ae_eq_Ioc

/-- The `Ioo`-form of the polar-coordinate change of variables in `ℂ`. -/
lemma integral_complex_eq_integral_angle_Ioo {F : ℂ → ℝ} (hF : Integrable F volume) :
    (∫ z : ℂ, F z) = ∫ r in Set.Ioi (0:ℝ), ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * F ((r:ℂ) * Complex.exp (θ * Complex.I)) := by
  rw [integral_complex_eq_integral_angle hF]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_of_le (a := -Real.pi) (b := Real.pi)
      (by linarith [Real.pi_pos])]
  exact (setIntegral_congr_set Ioo_ae_eq_Ioc).symm

/-- Fubini for set integrals: the outer integral of an integrable function on a product
of sets with values in `ℝ` is integrable. -/
lemma integrableOn_integral_prod_right {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {s : Set α} {t : Set β} {f : α × β → ℝ}
    (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    IntegrableOn (fun x => ∫ y in t, f (x, y) ∂ν) s μ := by
  rw [IntegrableOn] at hf
  rw [← MeasureTheory.Measure.prod_restrict] at hf
  rw [IntegrableOn]
  exact hf.integral_prod_left

/-- Integrability of the radial part of the polar decomposition. -/
lemma integrableOn_integral_angle_Ioo {F : ℂ → ℝ} (hF : Integrable F volume) :
    IntegrableOn (fun r : ℝ => ∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * F ((r:ℂ) * Complex.exp (θ * Complex.I))) (Set.Ioi (0:ℝ)) volume := by
  have h := integrableOn_polar_of_integrable hF
  have h2 : IntegrableOn (fun p : ℝ × ℝ => p.1 * F (p.1 * Complex.exp (p.2 * Complex.I)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact h
  exact integrableOn_integral_prod_right h2

/-- **The circle sub-mean-value inequality bounds the angular integral.** -/
lemma angular_ge {v : ℂ → ℝ}
    (hsmv : ∀ z w : ℂ, v z ≤ (∫ θ in (0 : ℝ)..(2 * Real.pi),
      v (z + Complex.exp (θ * Complex.I) * w)) / (2 * Real.pi))
    (z : ℂ) (r : ℝ) :
    2 * Real.pi * v z ≤ ∫ θ in (-Real.pi)..Real.pi,
      v (z - (r : ℂ) * Complex.exp (θ * Complex.I)) := by
  have hfuneq : (fun θ : ℝ => v (z - (r : ℂ) * Complex.exp (θ * Complex.I)))
      = (fun θ : ℝ => (fun x : ℝ => v (z + (r:ℂ) * Complex.exp (x * Complex.I))) (θ + Real.pi)) := by
    funext θ
    simp only
    congr 1
    rw [complex_exp_add_pi θ]
    ring
  have hmain : ∫ θ in (-Real.pi)..Real.pi, v (z - (r : ℂ) * Complex.exp (θ * Complex.I))
      = ∫ ψ in (0:ℝ)..(2 * Real.pi), v (z + (r:ℂ) * Complex.exp (ψ * Complex.I)) := by
    rw [hfuneq]
    simp only []
    rw [intervalIntegral.integral_comp_add_right
      (fun x : ℝ => v (z + (r:ℂ) * Complex.exp (x * Complex.I))) Real.pi]
    ring_nf
  have hpt : ∀ θ : ℝ, v (z + Complex.exp (θ * Complex.I) * (r:ℂ))
      = v (z + (r:ℂ) * Complex.exp (θ * Complex.I)) := by
    intro θ
    congr 1
    ring
  have hint : (∫ θ in (0:ℝ)..(2 * Real.pi), v (z + Complex.exp (θ * Complex.I) * (r:ℂ)))
      = ∫ θ in (0:ℝ)..(2 * Real.pi), v (z + (r:ℂ) * Complex.exp (θ * Complex.I)) :=
    intervalIntegral.integral_congr (fun θ _ => hpt θ)
  have hsmv' := hsmv z (r:ℂ)
  rw [hint] at hsmv'
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  rw [le_div_iff₀ h2π] at hsmv'
  rw [hmain]
  linarith

/-- The radial condition `k (c * s) = k s` makes `k` invariant under the polar parametrisation. -/
lemma radial_kernel_eval {k : ℂ → ℝ}
    (hkrad : ∀ s c : ℂ, ‖c‖ = 1 → k (c * s) = k s) (r θ : ℝ) :
    k ((r:ℂ) * Complex.exp (θ * Complex.I)) = k (r:ℂ) := by
  rw [mul_comm (r:ℂ)]
  exact hkrad (r:ℂ) (Complex.exp (θ * Complex.I)) (Complex.norm_exp_ofReal_mul_I θ)

/-- The Lebesgue measure of the interval `(-π, π)`. -/
lemma volume_real_Ioo_negpi_pi : (volume : Measure ℝ).real (Set.Ioo (-Real.pi) Real.pi)
    = 2 * Real.pi := by
  rw [Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

/-- **The mean value inequality survives convolution with a radial kernel.**  If `v : ℂ → ℝ`
satisfies the circle sub-mean-value inequality `v z ≤ ⨍_θ v (z + e^{iθ}w) dθ` and `k : ℂ → ℝ` is
a smooth nonnegative compactly supported radial kernel (`k (c * s) = k s` for `‖c‖ = 1`), then
`v z * ∫ k ≤ ∫ s, v (z - s) * k s`. -/
theorem subharmonic_convolution_ge {v k : ℂ → ℝ}
    (hk : ContDiff ℝ ⊤ k) (hk0 : ∀ s, 0 ≤ k s) (hkc : HasCompactSupport k)
    (hkrad : ∀ s c : ℂ, ‖c‖ = 1 → k (c * s) = k s)
    (hsmv : ∀ z w : ℂ, v z ≤ (∫ θ in (0 : ℝ)..(2 * Real.pi),
      v (z + Complex.exp (θ * Complex.I) * w)) / (2 * Real.pi))
    (hint : ∀ z : ℂ, MeasureTheory.Integrable (fun s : ℂ => v (z - s) * k s) MeasureTheory.volume)
    (z : ℂ) :
    v z * (∫ s : ℂ, k s) ≤ ∫ s : ℂ, v (z - s) * k s := by
  have hk_int : Integrable k volume := hk.continuous.integrable_of_hasCompactSupport hkc
  set G : ℂ → ℝ := fun s => v (z - s) * k s with hGdef
  have hG_int : Integrable G volume := hint z
  set φ : ℝ → ℝ := fun r => ∫ θ in Set.Ioo (-Real.pi) Real.pi,
      r * G ((r:ℂ) * Complex.exp (θ * Complex.I)) with hφdef
  set ψ : ℝ → ℝ := fun r => ∫ θ in Set.Ioo (-Real.pi) Real.pi,
      r * k ((r:ℂ) * Complex.exp (θ * Complex.I)) with hψdef
  set A : ℝ → ℝ := fun r => ∫ θ in Set.Ioo (-Real.pi) Real.pi,
      v (z - (r:ℂ) * Complex.exp (θ * Complex.I)) with hAdef
  have hGpol : (∫ s : ℂ, G s) = ∫ r in Set.Ioi (0:ℝ), φ r := by
    simpa only [hφdef] using integral_complex_eq_integral_angle_Ioo hG_int
  have hkpol : (∫ s : ℂ, k s) = ∫ r in Set.Ioi (0:ℝ), ψ r := by
    simpa only [hψdef] using integral_complex_eq_integral_angle_Ioo hk_int
  have hGint : IntegrableOn φ (Set.Ioi (0:ℝ)) volume :=
    integrableOn_integral_angle_Ioo hG_int
  have hkint : IntegrableOn ψ (Set.Ioi (0:ℝ)) volume :=
    integrableOn_integral_angle_Ioo hk_int
  -- explicit forms of `φ r` and `ψ r`
  have hφr : ∀ r : ℝ, φ r = r * (A r * k (r:ℂ)) := by
    intro r
    rw [hφdef, hAdef]
    simp only
    have hpt : ∀ θ : ℝ, r * G ((r:ℂ) * Complex.exp (θ * Complex.I))
        = r * (v (z - (r:ℂ) * Complex.exp (θ * Complex.I)) * k (r:ℂ)) := by
      intro θ
      rw [hGdef]
      simp only
      rw [radial_kernel_eval hkrad r θ]
    simp_rw [hpt]
    rw [integral_const_mul, integral_mul_const]
  have hψr : ∀ r : ℝ, ψ r = r * (k (r:ℂ) * (2 * Real.pi)) := by
    intro r
    rw [hψdef]
    simp only
    have hpt : ∀ θ : ℝ, r * k ((r:ℂ) * Complex.exp (θ * Complex.I)) = r * k (r:ℂ) := by
      intro θ; rw [radial_kernel_eval hkrad r θ]
    simp_rw [hpt]
    rw [integral_const_mul, setIntegral_const, volume_real_Ioo_negpi_pi, smul_eq_mul]
    ring
  have hAr : ∀ r : ℝ, 2 * Real.pi * v z ≤ A r := by
    intro r
    rw [hAdef]
    dsimp only
    have hconv : (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          v (z - (r:ℂ) * Complex.exp (θ * Complex.I)))
        = ∫ θ in (-Real.pi)..Real.pi, v (z - (r:ℂ) * Complex.exp (θ * Complex.I)) := by
      rw [intervalIntegral.integral_of_le (a := -Real.pi) (b := Real.pi)
        (by linarith [Real.pi_pos])]
      exact setIntegral_congr_set Ioo_ae_eq_Ioc
    rw [hconv]
    exact angular_ge hsmv z r
  have hpoint : ∀ r ∈ Set.Ioi (0:ℝ), v z * ψ r ≤ φ r := by
    intro r hr
    have hrpos : 0 < r := hr
    have hknn : 0 ≤ k (r:ℂ) := hk0 _
    rw [hφr r, hψr r]
    have h1 : (2 * Real.pi * v z) * k (r:ℂ) ≤ A r * k (r:ℂ) :=
      mul_le_mul_of_nonneg_right (hAr r) hknn
    have h2 : r * ((2 * Real.pi * v z) * k (r:ℂ)) ≤ r * (A r * k (r:ℂ)) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hrpos)
    calc v z * (r * (k (r:ℂ) * (2 * Real.pi)))
        = r * ((2 * Real.pi * v z) * k (r:ℂ)) := by ring
      _ ≤ r * (A r * k (r:ℂ)) := h2
  have hconst : IntegrableOn (fun r => v z * ψ r) (Set.Ioi (0:ℝ)) volume :=
    hkint.const_mul (v z)
  have hmono : ∫ r in Set.Ioi (0:ℝ), v z * ψ r ≤ ∫ r in Set.Ioi (0:ℝ), φ r := by
    apply integral_mono_ae
    · exact hconst
    · exact hGint
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with r hr
      exact hpoint r hr
  calc v z * (∫ s : ℂ, k s) = v z * ∫ r in Set.Ioi (0:ℝ), ψ r := by rw [hkpol]
    _ = ∫ r in Set.Ioi (0:ℝ), v z * ψ r := by rw [integral_const_mul]
    _ ≤ ∫ r in Set.Ioi (0:ℝ), φ r := hmono
    _ = ∫ s : ℂ, G s := hGpol.symm
    _ = ∫ s : ℂ, v (z - s) * k s := by rw [hGdef]

end

end Commons.MeasureTheory.Integral