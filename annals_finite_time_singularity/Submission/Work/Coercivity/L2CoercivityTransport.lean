import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Coercivity.slice_ibp_eta
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology RealInnerProductSpace
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Cauchy–Schwarz on `L²` -/

/-- The Cauchy–Schwarz inequality `(∫ f g)² ≤ (∫ f²)(∫ g²)` for `L²` functions on an
arbitrary measure space.  (The one-dimensional version is
`Work.Spaces.cs_integral`.) -/
theorem cs_integral_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hB : (∫ x, f x * g x ∂μ) = ∫ x, (hf.toLp f) x * (hg.toLp g) x ∂μ :=
    integral_congr_ae (by
      filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
      rw [hx, hy])
  have hA : (∫ x, f x ^ 2 ∂μ) = ∫ x, (hf.toLp f) x * (hf.toLp f) x ∂μ :=
    integral_congr_ae (by
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx, sq])
  have hC : (∫ x, g x ^ 2 ∂μ) = ∫ x, (hg.toLp g) x * (hg.toLp g) x ∂μ :=
    integral_congr_ae (by
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [hx, sq])
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  simp only [L2.inner_def, Real.inner_apply] at h
  rw [hB, hA, hC]
  simpa [sq] using h

/-! ## The Fubini bridge and the quadrant -/

/-- The restricted product measure `volume.restrict (Iz ×ˢ Iθ)` is the product of the two
restricted measures. -/
theorem volume_restrict_prod :
    volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)
      = (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) := by
  rw [Measure.volume_eq_prod]
  exact (Measure.prod_restrict _ _).symm

theorem integrableOn_prod {g : ℝ → ℝ → ℝ}
    (h : IntegrableOn (Function.uncurry g) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    Integrable (fun p : ℝ × ℝ => g p.1 p.2)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
  rw [IntegrableOn, volume_restrict_prod] at h
  exact h

/-- Almost every point of the product measure lies in the quadrant. -/
theorem ae_prod_quadrant :
    ∀ᵐ p ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)),
      p.1 ∈ Spaces.Iz ∧ p.2 ∈ Spaces.Iθ := by
  rw [← volume_restrict_prod]
  exact ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)

/-- Almost every point of the product measure has `0 < p.1`. -/
theorem ae_prod_pos :
    ∀ᵐ p ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)), 0 < p.1 := by
  rw [Measure.prod_restrict]
  have hset : (Spaces.Iz ×ˢ Spaces.Iθ : Set (ℝ × ℝ))
      =ᵐ[volume.prod volume] (Set.Ioi 0 ×ˢ Spaces.Iθ) :=
    Measure.set_prod_ae_eq (Ioi_ae_eq_Ici.symm) Filter.EventuallyEq.rfl
  rw [Measure.restrict_congr_set hset]
  exact (ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Icc)).mono
    (fun p hp => hp.1)

/-- The angular interval has measure at most `2`. -/
theorem volumeReal_Iθ_le_two : volume.real Spaces.Iθ ≤ 2 := by
  have hsub : Spaces.Iθ ⊆ Set.Icc (0 : ℝ) 2 := fun θ hθ =>
    ⟨hθ.1, by linarith [hθ.2, Real.pi_le_four]⟩
  calc volume.real Spaces.Iθ ≤ volume.real (Set.Icc (0 : ℝ) 2) :=
        measureReal_mono hsub (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    _ = 2 := by rw [Real.volume_real_Icc_of_le (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

/-- A product integral of separated functions factorises. -/
theorem integral_prod_sep (a b : ℝ → ℝ)
    (ha : Integrable a (volume.restrict Spaces.Iz))
    (hb : Integrable b (volume.restrict Spaces.Iθ)) :
    ∫ p : ℝ × ℝ, a p.1 * b p.2
        ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ))
      = (∫ z in Spaces.Iz, a z) * (∫ θ in Spaces.Iθ, b θ) := by
  rw [MeasureTheory.integral_prod _ (ha.mul_prod hb)]
  have hinner : ∀ z : ℝ, (∫ θ in Spaces.Iθ, a z * b θ)
      = a z * (∫ θ in Spaces.Iθ, b θ) := fun z => MeasureTheory.integral_const_mul _ _
  simp_rw [hinner]
  rw [MeasureTheory.integral_mul_const]

/-! ## The elementary integrals `∫₀^∞ dz/(1+z)² = 1` and `∫_θ sin(2θ) = 1` -/

theorem hasDerivAt_neg_inv_add (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun t : ℝ => -1 / (1 + t)) (1 / (1 + x) ^ 2) x := by
  have hx1 : (1 : ℝ) + x ≠ 0 := by positivity
  simpa using Work.FM.hasDerivAt_div_add_const (-1) 1 x hx1

theorem tendsto_neg_inv_add :
    Tendsto (fun t : ℝ => -1 / (1 + t)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
  have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h1
  have h3 : Tendsto (fun t : ℝ => -1 * ((1 : ℝ) + t)⁻¹) atTop (𝓝 (-1 * 0)) :=
    h2.const_mul (-1)
  simpa [div_eq_mul_inv] using h3

/-- `∫_0^∞ dz/(1+z)² = 1`. -/
theorem integral_Iz_one_div_sq : ∫ z in Spaces.Iz, 1 / (1 + z) ^ 2 = 1 := by
  rw [Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ)) (l := (0 : ℝ))
    (g := fun t : ℝ => -1 / (1 + t)) (g' := fun x : ℝ => 1 / (1 + x) ^ 2)
    (fun x hx => hasDerivAt_neg_inv_add x hx) (fun x hx => by positivity) tendsto_neg_inv_add
  rw [key]
  norm_num

/-- `z ↦ 1/(1+z)²` is integrable on `Iz`. -/
theorem integrable_Iz_one_div_sq :
    Integrable (fun z : ℝ => 1 / (1 + z) ^ 2) (volume.restrict Spaces.Iz) := by
  have key := MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (a := (0 : ℝ)) (l := (0 : ℝ))
    (g := fun t : ℝ => -1 / (1 + t)) (g' := fun x : ℝ => 1 / (1 + x) ^ 2)
    (fun x hx => hasDerivAt_neg_inv_add x hx) (fun x hx => by positivity) tendsto_neg_inv_add
  change Integrable (fun z : ℝ => 1 / (1 + z) ^ 2) (volume.restrict Spaces.Iz)
  rw [Spaces.Iz, ← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  exact key

theorem hasDerivAt_antideriv_six (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt (fun t : ℝ => -1 / 3 * ((1 + t) ^ 3)⁻¹ + 1 / 2 * ((1 + t) ^ 4)⁻¹
        - 1 / 5 * ((1 + t) ^ 5)⁻¹) (x ^ 2 / (1 + x) ^ 6) x := by
  have hx1 : (1 : ℝ) + x ≠ 0 := by positivity
  have hbase : HasDerivAt (fun t : ℝ => (1 : ℝ) + t) 1 x := by
    simpa using (hasDerivAt_id x).const_add (1 : ℝ)
  have h3 : HasDerivAt (fun t : ℝ => (1 + t) ^ 3) (3 * (1 + x) ^ 2) x := by
    have := hbase.pow 3
    convert this using 1
    ring
  have h4 : HasDerivAt (fun t : ℝ => (1 + t) ^ 4) (4 * (1 + x) ^ 3) x := by
    have := hbase.pow 4
    convert this using 1
    ring
  have h5 : HasDerivAt (fun t : ℝ => (1 + t) ^ 5) (5 * (1 + x) ^ 4) x := by
    have := hbase.pow 5
    convert this using 1
    ring
  have h3' : HasDerivAt (fun t : ℝ => -1 / 3 * ((1 + t) ^ 3)⁻¹)
      (-1 / 3 * (-(3 * (1 + x) ^ 2) / ((1 + x) ^ 3) ^ 2)) x :=
    (h3.inv (by positivity)).const_mul (-1 / 3)
  have h4' : HasDerivAt (fun t : ℝ => 1 / 2 * ((1 + t) ^ 4)⁻¹)
      (1 / 2 * (-(4 * (1 + x) ^ 3) / ((1 + x) ^ 4) ^ 2)) x :=
    (h4.inv (by positivity)).const_mul (1 / 2)
  have h5' : HasDerivAt (fun t : ℝ => -1 / 5 * ((1 + t) ^ 5)⁻¹)
      (-1 / 5 * (-(5 * (1 + x) ^ 4) / ((1 + x) ^ 5) ^ 2)) x :=
    (h5.inv (by positivity)).const_mul (-1 / 5)
  have hsum := (h3'.add h4').add h5'
  have hfun : (((fun t : ℝ => -1 / 3 * ((1 + t) ^ 3)⁻¹)
        + fun t : ℝ => 1 / 2 * ((1 + t) ^ 4)⁻¹) + fun t : ℝ => -1 / 5 * ((1 + t) ^ 5)⁻¹)
      = fun t : ℝ => -1 / 3 * ((1 + t) ^ 3)⁻¹ + 1 / 2 * ((1 + t) ^ 4)⁻¹
        - 1 / 5 * ((1 + t) ^ 5)⁻¹ := by
    funext t; simp only [Pi.add_apply]; ring
  rw [hfun] at hsum
  have hderiv : (-1 / 3 * (-(3 * (1 + x) ^ 2) / ((1 + x) ^ 3) ^ 2)
      + 1 / 2 * (-(4 * (1 + x) ^ 3) / ((1 + x) ^ 4) ^ 2)
      + -1 / 5 * (-(5 * (1 + x) ^ 4) / ((1 + x) ^ 5) ^ 2)) = x ^ 2 / (1 + x) ^ 6 := by
    field_simp
    ring
  rwa [hderiv] at hsum

theorem tendsto_antideriv_six :
    Tendsto (fun t : ℝ => -1 / 3 * ((1 + t) ^ 3)⁻¹ + 1 / 2 * ((1 + t) ^ 4)⁻¹
        - 1 / 5 * ((1 + t) ^ 5)⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => (1 : ℝ) + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id
  have h2 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h1
  have h3 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹ ^ 3) atTop (𝓝 0) := by
    simpa using h2.pow 3
  have h4 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹ ^ 4) atTop (𝓝 0) := by
    simpa using h2.pow 4
  have h5 : Tendsto (fun t : ℝ => ((1 : ℝ) + t)⁻¹ ^ 5) atTop (𝓝 0) := by
    simpa using h2.pow 5
  have h6 := ((h3.const_mul (-1 / 3)).add (h4.const_mul (1 / 2))).sub (h5.const_mul (1 / 5))
  have heq : (fun t : ℝ => -1 / 3 * ((1 : ℝ) + t)⁻¹ ^ 3 + 1 / 2 * ((1 : ℝ) + t)⁻¹ ^ 4
        - 1 / 5 * ((1 : ℝ) + t)⁻¹ ^ 5)
      = fun t : ℝ => -1 / 3 * ((1 + t) ^ 3)⁻¹ + 1 / 2 * ((1 + t) ^ 4)⁻¹
        - 1 / 5 * ((1 + t) ^ 5)⁻¹ := by
    funext t; rw [inv_pow, inv_pow, inv_pow]
  rw [heq] at h6
  simpa using h6

/-- `∫_0^∞ z²/(1+z)⁶ dz = 1/30`. -/
theorem integral_Iz_zsq_div_six : ∫ z in Spaces.Iz, z ^ 2 / (1 + z) ^ 6 = 1 / 30 := by
  rw [Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]
  have key := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := (0 : ℝ)) (l := (0 : ℝ))
    (g := fun t : ℝ => -1 / 3 * ((1 + t) ^ 3)⁻¹ + 1 / 2 * ((1 + t) ^ 4)⁻¹
        - 1 / 5 * ((1 + t) ^ 5)⁻¹)
    (g' := fun x : ℝ => x ^ 2 / (1 + x) ^ 6)
    (fun x hx => hasDerivAt_antideriv_six x hx) (fun x hx => by positivity) tendsto_antideriv_six
  rw [key]
  norm_num

/-- `z ↦ z²/(1+z)⁶` is integrable on `Iz`. -/
theorem integrable_Iz_zsq_div_six :
    Integrable (fun z : ℝ => z ^ 2 / (1 + z) ^ 6) (volume.restrict Spaces.Iz) := by
  rw [Spaces.Iz, ← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
    (a := (0 : ℝ)) (l := (0 : ℝ))
    (g := fun t : ℝ => -1 / 3 * ((1 + t) ^ 3)⁻¹ + 1 / 2 * ((1 + t) ^ 4)⁻¹
        - 1 / 5 * ((1 + t) ^ 5)⁻¹)
    (g' := fun x : ℝ => x ^ 2 / (1 + x) ^ 6)
    (fun x hx => hasDerivAt_antideriv_six x hx) (fun x hx => by positivity) tendsto_antideriv_six

/-! ## Integrability on `Iθ` -/

instance : IsFiniteMeasure (volume.restrict Spaces.Iθ) := by
  rw [MeasureTheory.isFiniteMeasure_restrict]
  rw [show Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl, Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

theorem continuousOn_Kθ : ContinuousOn (fun θ : ℝ => Spaces.K θ) Spaces.Iθ := by
  have h : Continuous fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 := by fun_prop
  simpa [Spaces.K] using h.continuousOn

theorem integrableOn_Kθ_sq : IntegrableOn (fun θ : ℝ => (Spaces.K θ) ^ 2) Spaces.Iθ := by
  have h : ContinuousOn (fun θ : ℝ => (Spaces.K θ) ^ 2) Spaces.Iθ := (continuousOn_Kθ).pow 2
  simpa [Spaces.Iθ] using h.integrableOn_Icc

theorem integrableOn_sin_two : IntegrableOn (fun θ : ℝ => Real.sin (2 * θ)) Spaces.Iθ := by
  have h : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) Spaces.Iθ :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  simpa [Spaces.Iθ] using h.integrableOn_Icc

/-- `∫_θ sin(2θ) dθ = 1` on `Iθ`. -/
theorem integral_Iθ_sin_two : ∫ θ in Spaces.Iθ, Real.sin (2 * θ) = 1 := by
  rw [Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => -Real.cos (2 * t) / 2) (Real.sin (2 * x)) x := by
    intro x hx
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    have h2 := (Real.hasDerivAt_cos (2 * x)).comp x h1
    have h3 : HasDerivAt (fun t : ℝ => -Real.cos (2 * t) / 2)
        (-(-Real.sin (2 * x) * 2) / 2) x := h2.neg.div_const 2
    convert h3 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by continuity : Continuous fun t : ℝ => Real.sin (2 * t)).intervalIntegrable 0 (Real.pi / 2))]
  rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring]
  simp only [mul_zero, Real.cos_pi, Real.cos_zero]
  norm_num

/-- `∫_θ K(θ)² dθ ≤ 9/4` on `Iθ`. -/
theorem integral_Iθ_Ksq_le : ∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2 ≤ 9 / 4 := by
  have hIntSin : IntegrableOn (fun θ : ℝ => (9 / 4) * Real.sin (2 * θ)) Spaces.Iθ :=
    integrableOn_sin_two.const_mul (9 / 4)
  have hpt : ∀ θ ∈ Spaces.Iθ, (Spaces.K θ) ^ 2 ≤ (9 / 4) * Real.sin (2 * θ) := by
    intro θ hθ
    have hs0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hc0 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have hsc : Real.sin θ * Real.cos θ ≤ 1 / 2 := by
      nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ - Real.cos θ)]
    have hc1 : Real.cos θ ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
    have hkey : Real.sin θ * Real.cos θ ^ 3 ≤ 1 / 2 := by
      calc Real.sin θ * Real.cos θ ^ 3 = (Real.sin θ * Real.cos θ) * Real.cos θ ^ 2 := by ring
        _ ≤ (1 / 2) * 1 := mul_le_mul hsc hc1 (sq_nonneg _) (by norm_num)
        _ = 1 / 2 := by norm_num
    have hmain : Real.sin θ ^ 2 * Real.cos θ ^ 4 ≤ (1 / 4) * Real.sin (2 * θ) := by
      rw [Real.sin_two_mul]
      calc Real.sin θ ^ 2 * Real.cos θ ^ 4
          = (Real.sin θ * Real.cos θ) * (Real.sin θ * Real.cos θ ^ 3) := by ring
        _ ≤ (Real.sin θ * Real.cos θ) * (1 / 2) :=
            mul_le_mul_of_nonneg_left hkey (mul_nonneg hs0 hc0)
        _ = (1 / 4) * (2 * Real.sin θ * Real.cos θ) := by ring
    show (Spaces.K θ) ^ 2 ≤ (9 / 4) * Real.sin (2 * θ)
    rw [Spaces.K]
    nlinarith [hmain]
  calc ∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2
      ≤ ∫ θ in Spaces.Iθ, (9 / 4) * Real.sin (2 * θ) :=
        integral_mono_ae integrableOn_Kθ_sq hIntSin
          (by filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ; exact hpt θ hθ)
    _ = (9 / 4) * ∫ θ in Spaces.Iθ, Real.sin (2 * θ) := integral_const_mul _ _
    _ = 9 / 4 := by rw [integral_Iθ_sin_two]; norm_num

/-! ## Almost everywhere strong measurability -/


/-- `(z,θ) ↦ w(z) = (1+z)²/z²` is continuous on the open quadrant. -/
theorem continuousOn_w_quad :
    ContinuousOn (fun p : ℝ × ℝ => Spaces.w p.1) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hwz : ContinuousOn (fun z : ℝ => Spaces.w z) (Set.Ioi 0) := by
    have hnum : ContinuousOn (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) := by fun_prop
    have hden : ContinuousOn (fun z : ℝ => z ^ 2) (Set.Ioi 0) := by fun_prop
    have hdiv := hnum.div hden (fun z hz => pow_ne_zero 2 (ne_of_gt hz))
    change ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0)
    exact hdiv
  exact hwz.comp continuous_fst.continuousOn (fun p hp => hp.1)






/-! ## The bound `(C0 f)² ≤ EDthW f` -/


/-! ## The bound on the projector term -/


/-! ## The final numerical inequality -/


/-! ## The main theorem -/


end Work.Coercivity
