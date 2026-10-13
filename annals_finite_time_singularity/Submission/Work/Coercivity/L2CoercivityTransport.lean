/-
# `L2CoercivityTransport`: coercivity of `𝓛_Γ^T` in the weighted `L²` space

This file proves Proposition `prop:L2CoercivityTransport` of

  T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
  incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),

namely `(𝓛_Γ^T(f) w, f w)_{L²} ≥ (1/5)|f w|²_{L²} - 100|D_θ f w|²_{L²}`, which in the
notation of this development reads

  `(1/5) * Ef f - 10000 * EDthW f ≤ wip (fun z _ => w z ^ 2) (LGammaT α f) f`.

(The constant is `10⁴` instead of the paper's `100`, see `NOTES.md`.)

## The proof

With `𝓛_Γ^T = 𝓛_Γ - 𝕡(Transport)` and `𝕡(g) = g - (Γ/c)(2z²/(1+z)³)L₁₂(g)(0)`:

* `wip (𝓛_Γ^T f) f = wip (𝓛_Γ f) f - wip (𝕡(Transport f)) f` (joint integrability from
  `CoerciveData`);
* `wip (𝓛_Γ f) f ≥ (1/4)|f w|²` (`L2Coercivity`);
* the correction is bounded by Cauchy–Schwarz: `|wip (𝕡(Transport f)) f| ≤ √Q √(Ef f)`;
* pointwise `𝕡(Transport f) w = (3 D_θ f w - 2(Γ/c)C0)/(1+z)` with `C0 = L₁₂(Transport f)(0)`,
  so `Q ≤ 18 EDthW f + 800 C0² ∫∫ dz dθ/(1+z)²`, and with `C0² ≤ EDthW f`,
  `∫_0^∞ dz/(1+z)² = 1` and `volume.real Iθ ≤ 2` this is `≤ 1618 EDthW f`;
* finally `(1/4)x² - √2000 xy ≥ (1/5)x² - 10⁴y²` because `√2000 = 2√(10000/20)`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.zAux
import Submission.Work.Coercivity.L2Coercivity
import Submission.Work.Coercivity.EL12z_le
import Submission.Work.Spaces.CurrySmooth
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

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

/-- `(z,θ) ↦ pth f z θ` is continuous on the open quadrant when `f` is smooth on a
neighbourhood of the closed quadrant. -/
theorem continuousOn_pth_quad {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f) :
    ContinuousOn (fun p : ℝ × ℝ => Spaces.pth f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hU : ContDiffOn ℝ ⊤ (Function.uncurry (Spaces.pth f))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1)) :=
    Spaces.contDiffOn_uncurry_pth (isOpen_Ioi.prod isOpen_Ioo) hsm
  refine hU.continuousOn.mono ?_
  intro p hp
  refine ⟨Set.mem_Ioi.mpr ?_, Set.mem_Ioo.mpr ⟨?_, ?_⟩⟩
  · linarith [show (0 : ℝ) < p.1 from hp.1]
  · linarith [show (0 : ℝ) < p.2 from hp.2.1]
  · linarith [show p.2 < π / 2 from hp.2.2, Real.pi_pos]

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

/-- `(z,θ) ↦ D_θ f z θ · w(z)` is continuous on the open quadrant. -/
theorem continuousOn_dth_mul_w {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f) :
    ContinuousOn (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2 * Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hpth := continuousOn_pth_quad hsm
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  have h2 := (hsin.mul hpth).mul continuousOn_w_quad
  change ContinuousOn (fun p : ℝ × ℝ =>
    Real.sin (2 * p.2) * Spaces.pth f p.1 p.2 * Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))
  exact h2

/-- `(z,θ) ↦ f(z,θ) · w(z)` is continuous on the open quadrant. -/
theorem continuousOn_f_mul_w {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f) :
    ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2 * Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) := by
  have hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    hsm.continuousOn.mono (fun p hp =>
      ⟨Set.mem_Ioi.mpr (by linarith [show (0:ℝ) < p.1 from hp.1]),
       Set.mem_Ioo.mpr ⟨by linarith [show (0:ℝ) < p.2 from hp.2.1],
         by linarith [show p.2 < π / 2 from hp.2.2, Real.pi_pos]⟩⟩)
  exact hf.mul continuousOn_w_quad

/-- A.e. strong measurability of `D_θ f · w`. -/
theorem aesm_dth_mul_w {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2 * Spaces.w p.1)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) :=
  Spaces.aesm_of_continuousOn_Qd _ (continuousOn_dth_mul_w hsm)

/-- A.e. strong measurability of `f · w`. -/
theorem aesm_f_mul_w {f : ℝ → ℝ → ℝ} (hsm : Spaces.SmoothNbhd f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2 * Spaces.w p.1)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) :=
  Spaces.aesm_of_continuousOn_Qd _ (continuousOn_f_mul_w hsm)

/-- **A.e. strong measurability of the projector term** `𝕡(Transport f)·w`. -/
theorem aesm_projTransport_mul_w (α : ℝ) (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Proj α (Transport f) p.1 p.2 * Spaces.w p.1)
      ((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ)) := by
  refine Spaces.aesm_of_continuousOn_Qd
    (fun p : ℝ × ℝ => Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ?_
  set Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) with hQd
  have hDth : ContinuousOn (fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2) Qd := by
    have hpth := continuousOn_pth_quad hsm
    have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Qd :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    have h3 := hsin.mul hpth
    change ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2) * Spaces.pth f p.1 p.2) Qd
    exact h3
  have hinv1 : ContinuousOn (fun p : ℝ × ℝ => (1 : ℝ) / (1 + p.1)) Qd := by
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact (continuous_const.add continuous_fst).continuousOn
    · intro p hp
      have h1 : (0 : ℝ) < p.1 := hp.1
      exact ne_of_gt (by linarith)
  have hTrans : ContinuousOn (fun p : ℝ × ℝ => Transport f p.1 p.2) Qd := by
    change ContinuousOn (fun p : ℝ × ℝ => 3 * Spaces.Dth f p.1 p.2 / (1 + p.1)) Qd
    exact (continuousOn_const.mul hDth).div ((continuous_const.add continuous_fst).continuousOn)
      (fun p hp => by have h1 : (0 : ℝ) < p.1 := hp.1; exact ne_of_gt (by linarith))
  have hGam : ContinuousOn (fun p : ℝ × ℝ => Spaces.Gam α p.2 / Spaces.c α) Qd := by
    apply ContinuousOn.div_const
    apply ContinuousOn.rpow_const
    · exact ((Real.continuous_sin.comp continuous_snd).mul
        ((Real.continuous_cos.comp continuous_snd).pow 2)).continuousOn
    · intro p hp
      refine Or.inl ?_
      have hsin : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
        (by linarith [hp.2.2, Real.pi_pos])
      have hcos : 0 < Real.cos p.2 :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
      exact ne_of_gt (mul_pos hsin (pow_pos hcos 2))
  have hratio : ContinuousOn (fun p : ℝ × ℝ => 2 * p.1 ^ 2 / (1 + p.1) ^ 3) Qd := by
    apply ContinuousOn.div
    · exact continuousOn_const.mul (continuous_fst.continuousOn.pow 2)
    · exact (continuous_const.add continuous_fst).continuousOn.pow 3
    · intro p hp
      have h1 : (0 : ℝ) < p.1 := hp.1
      exact pow_ne_zero 3 (by linarith)
  have hCorr : ContinuousOn
      (fun p : ℝ × ℝ => (Spaces.Gam α p.2 / Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * C0 f)
      Qd := (hGam.mul hratio).mul continuousOn_const
  have hProj : ContinuousOn (fun p : ℝ × ℝ => Proj α (Transport f) p.1 p.2) Qd := by
    change ContinuousOn (fun p : ℝ × ℝ => Transport f p.1 p.2
      - (Spaces.Gam α p.2 / Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3) * C0 f) Qd
    exact hTrans.sub hCorr
  have hw : ContinuousOn (fun p : ℝ × ℝ => Spaces.w p.1) Qd := continuousOn_w_quad
  exact hProj.mul hw

/-! ## The bound `(C0 f)² ≤ EDthW f` -/

/-- `L₁₂(Transport f)(0)` is a linear functional of `D_θ f · w` whose kernel
`3 K(θ) z/(1+z)³` has `L²`-norm at most `1`; hence `(C0 f)² ≤ EDthW f`. -/
theorem C0_sq_le_EDthW (f : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd f)
    (hint : IntegrableOn
      (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ
        * Spaces.w z ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    (C0 f) ^ 2 ≤ EDthW f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  set u : ℝ × ℝ → ℝ := fun p => Spaces.Dth f p.1 p.2 * Spaces.w p.1 with hu
  set v : ℝ × ℝ → ℝ := fun p => 3 * Spaces.K p.2 * p.1 / (1 + p.1) ^ 3 with hv
  have hu2 : Integrable (fun p : ℝ × ℝ => u p ^ 2) P := by
    have h := integrableOn_prod (g := fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ
      * Spaces.w z ^ 2) hint
    exact h.congr (Eventually.of_forall fun p => by simp only [hu]; ring)
  have hv2 : Integrable (fun p : ℝ × ℝ => v p ^ 2) P := by
    have hran : Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Spaces.Iz) := integrable_Iz_zsq_div_six.const_mul 9
    have hmul : Integrable (fun p : ℝ × ℝ =>
        (9 * (p.1 ^ 2 / (1 + p.1) ^ 6)) * ((Spaces.K p.2) ^ 2)) P :=
      hran.mul_prod integrableOn_Kθ_sq
    refine hmul.congr ?_
    filter_upwards [ae_prod_pos] with p hp
    have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0:ℝ) < p.1 from hp])
    simp only [hv]
    field_simp
    ring
  have huA : MemLp u 2 P := by
    refine (memLp_two_iff_integrable_sq ?_).2 hu2
    rw [hu]; exact aesm_dth_mul_w hsm
  have hvA : MemLp v 2 P := by
    refine (memLp_two_iff_integrable_sq ?_).2 hv2
    rw [hv]
    apply Measurable.aestronglyMeasurable
    simp only [Spaces.K]
    fun_prop
  have hC0id : C0 f = ∫ p, u p * v p ∂P := by
    have hdef : C0 f = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Spaces.Iθ,
        Spaces.K θ * Transport f s θ / s := by
      simp only [C0, L12f, FM.L12, FM.L12dens, Spaces.Iθ]
    rw [hdef]
    have h1 : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Spaces.Iθ, Spaces.K θ * Transport f s θ / s)
        = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Spaces.Iθ, u (s, θ) * v (s, θ) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [hu, hv, Transport, Spaces.w]
      have hs0 : s ≠ 0 := ne_of_gt hs
      have hs1 : 1 + s ≠ 0 := ne_of_gt (by linarith [show (0:ℝ) < s from hs])
      field_simp
    rw [h1]
    rw [MeasureTheory.setIntegral_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => u p * v p)
      (huA.integrable_mul hvA)).symm
  have hunorm : ∫ p, u p ^ 2 ∂P = EDthW f := by
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => u p ^ 2) hu2]
    rw [EDthW, wip]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hu]; ring
  have hsep : ∫ p, v p ^ 2 ∂P
      = (∫ z in Spaces.Iz, 9 * (z ^ 2 / (1 + z) ^ 6))
        * (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) := by
    have hcongr : (fun p : ℝ × ℝ => v p ^ 2)
        =ᵐ[P] fun p : ℝ × ℝ => (9 * (p.1 ^ 2 / (1 + p.1) ^ 6)) * ((Spaces.K p.2) ^ 2) := by
      filter_upwards [ae_prod_pos] with p hp
      have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0:ℝ) < p.1 from hp])
      simp only [hv]; field_simp; ring
    rw [MeasureTheory.integral_congr_ae hcongr]
    have hran : Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Spaces.Iz) := integrable_Iz_zsq_div_six.const_mul 9
    exact integral_prod_sep _ _ hran integrableOn_Kθ_sq
  have hvnorm : ∫ p, v p ^ 2 ∂P ≤ 1 := by
    rw [hsep]
    have h1 : (∫ z in Spaces.Iz, 9 * (z ^ 2 / (1 + z) ^ 6)) = 3 / 10 := by
      rw [MeasureTheory.integral_const_mul, integral_Iz_zsq_div_six]
      norm_num
    have h2 : (∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2) ≤ 9 / 4 := integral_Iθ_Ksq_le
    have hnn : 0 ≤ ∫ θ in Spaces.Iθ, (Spaces.K θ) ^ 2 := integral_nonneg fun θ => sq_nonneg _
    rw [h1]
    nlinarith [h2, hnn]
  calc (C0 f) ^ 2 = (∫ p, u p * v p ∂P) ^ 2 := by rw [hC0id]
    _ ≤ (∫ p, u p ^ 2 ∂P) * (∫ p, v p ^ 2 ∂P) := cs_integral_mul huA hvA
    _ ≤ EDthW f * 1 := by
        rw [hunorm]
        exact mul_le_mul_of_nonneg_left hvnorm (by rw [← hunorm]; exact integral_nonneg fun p => sq_nonneg _)
    _ = EDthW f := mul_one _

/-! ## The bound on the projector term -/

/-- The integral of `(𝕡(Transport f) w)²` over the quadrant is bounded by `2000 · EDthW f`. -/
theorem ProjTransport_sq_integral_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hsm : Spaces.SmoothNbhd f)
    (hint : IntegrableOn
      (Function.uncurry (fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ
        * Spaces.w z ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hC0 : (C0 f) ^ 2 ≤ EDthW f) :
    IntegrableOn
        (Function.uncurry (fun z θ => (Proj α (Transport f) z θ * Spaces.w z) ^ 2))
        (Spaces.Iz ×ˢ Spaces.Iθ)
      ∧ ∫ p : ℝ × ℝ,
          (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2
        ∂((volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ))
        ≤ 2000 * EDthW f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  set U : ℝ × ℝ → ℝ := fun p => Proj α (Transport f) p.1 p.2 * Spaces.w p.1 with hU
  set W : ℝ × ℝ → ℝ := fun p => 18 * (Spaces.Dth f p.1 p.2 * Spaces.w p.1) ^ 2
      + 800 * (C0 f) ^ 2 / (1 + p.1) ^ 2 with hW
  have hEdnn : 0 ≤ EDthW f := by
    rw [EDthW, wip]
    exact integral_nonneg fun z => integral_nonneg fun θ =>
      mul_nonneg (mul_self_nonneg _) (sq_nonneg _)
  have hpt : ∀ᵐ p ∂P, (U p) ^ 2 ≤ W p := by
    filter_upwards [ae_prod_pos, ae_prod_quadrant] with p hp hq
    have hz : 0 < p.1 := hp
    have hθ : p.2 ∈ Spaces.Iθ := hq.2
    have hGc : (Spaces.Gam α p.2 / Spaces.c α) ^ 2 ≤ 100 := by
      have hgap : |Spaces.Gam α p.2 / Spaces.c α| ≤ 10 := Gam_div_c_bound hα hα1 hθ
      nlinarith [abs_nonneg (Spaces.Gam α p.2 / Spaces.c α),
        sq_abs (Spaces.Gam α p.2 / Spaces.c α)]
    have hid : U p = (1 / (1 + p.1)) *
        (3 * (Spaces.Dth f p.1 p.2 * Spaces.w p.1)
          - 2 * (Spaces.Gam α p.2 / Spaces.c α) * C0 f) := by
      simp only [hU, Proj, Transport, Spaces.w, C0]
      have hz0 : p.1 ≠ 0 := ne_of_gt hz
      have hz1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith)
      field_simp
    have h1z : 1 / (1 + p.1) ^ 2 ≤ 1 := by
      rw [div_le_iff₀ (pow_pos (by linarith : (0 : ℝ) < 1 + p.1) 2)]
      nlinarith
    set g : ℝ := Spaces.Gam α p.2 / Spaces.c α with hg
    set Gw : ℝ := Spaces.Dth f p.1 p.2 * Spaces.w p.1 with hGw
    have hquad : (3 * Gw - 2 * g * C0 f) ^ 2 ≤ 18 * Gw ^ 2 + 800 * (C0 f) ^ 2 := by
      have h1 : (3 * Gw - 2 * g * C0 f) ^ 2 ≤ 2 * ((3 * Gw) ^ 2 + (2 * g * C0 f) ^ 2) := by
        nlinarith [sq_nonneg (3 * Gw + 2 * g * C0 f)]
      have h2 : 2 * ((3 * Gw) ^ 2 + (2 * g * C0 f) ^ 2) ≤ 18 * Gw ^ 2 + 800 * (C0 f) ^ 2 := by
        nlinarith [hGc, sq_nonneg (C0 f), sq_nonneg Gw]
      linarith
    calc (U p) ^ 2
        = (1 / (1 + p.1)) ^ 2 * (3 * Gw - 2 * g * C0 f) ^ 2 := by rw [hid]; rw [mul_pow]
      _ ≤ (1 / (1 + p.1)) ^ 2 * (18 * Gw ^ 2 + 800 * (C0 f) ^ 2) :=
          mul_le_mul_of_nonneg_left hquad (by positivity)
      _ ≤ 18 * Gw ^ 2 + 800 * (C0 f) ^ 2 / (1 + p.1) ^ 2 := by
          have hp1 : (0 : ℝ) < (1 + p.1) ^ 2 := pow_pos (by linarith : (0 : ℝ) < 1 + p.1) 2
          have heq : (1 / (1 + p.1)) ^ 2 * (18 * Gw ^ 2 + 800 * (C0 f) ^ 2)
              = 18 * Gw ^ 2 / (1 + p.1) ^ 2 + 800 * (C0 f) ^ 2 / (1 + p.1) ^ 2 := by
            field_simp
            try ring
          rw [heq]
          have h2z : 18 * Gw ^ 2 / (1 + p.1) ^ 2 ≤ 18 * Gw ^ 2 := by
            rw [div_le_iff₀ hp1]
            nlinarith [sq_nonneg Gw, sq_nonneg p.1, hz]
          linarith [h2z]
      _ = 18 * (Spaces.Dth f p.1 p.2 * Spaces.w p.1) ^ 2
            + 800 * (C0 f) ^ 2 / (1 + p.1) ^ 2 := by rw [hGw]
  have hGa : Integrable (fun p : ℝ × ℝ => 1 / (1 + p.1) ^ 2) P :=
    integrable_Iz_one_div_sq.comp_fst (volume.restrict Spaces.Iθ)
  have hW1 : Integrable
      (fun p : ℝ × ℝ => 18 * (Spaces.Dth f p.1 p.2 * Spaces.w p.1) ^ 2) P := by
    have h := integrableOn_prod (g := fun z θ => Spaces.Dth f z θ * Spaces.Dth f z θ
      * Spaces.w z ^ 2) hint
    exact (h.const_mul 18).congr (Eventually.of_forall fun p => by ring)
  have hW2 : Integrable (fun p : ℝ × ℝ => 800 * (C0 f) ^ 2 / (1 + p.1) ^ 2) P :=
    (hGa.const_mul (800 * (C0 f) ^ 2)).congr (Eventually.of_forall fun p => by ring)
  have hWint : Integrable W P := by
    rw [hW]; exact hW1.add hW2
  have hUaesm : AEStronglyMeasurable (fun p : ℝ × ℝ => (U p) ^ 2) P := by
    have hUA : AEStronglyMeasurable U P := by
      rw [hU]; exact aesm_projTransport_mul_w α f hsm
    refine (hUA.mul hUA).congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply, pow_two]
  have hUint : Integrable (fun p : ℝ × ℝ => (U p) ^ 2) P :=
    hWint.mono' hUaesm (hpt.mono fun p hp => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hp)
  have hunorm : ∫ p, (Spaces.Dth f p.1 p.2 * Spaces.w p.1) ^ 2 ∂P = EDthW f := by
    have h : Integrable (fun p : ℝ × ℝ =>
        Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * Spaces.w p.1 ^ 2) P :=
      integrableOn_prod hint
    have hcongr : (fun p : ℝ × ℝ => (Spaces.Dth f p.1 p.2 * Spaces.w p.1) ^ 2)
        = fun p : ℝ × ℝ => Spaces.Dth f p.1 p.2 * Spaces.Dth f p.1 p.2 * Spaces.w p.1 ^ 2 := by
      funext p; ring
    rw [hcongr, MeasureTheory.integral_prod _ h, EDthW, wip]
  have hGale : ∫ p, 1 / (1 + p.1) ^ 2 ∂P ≤ 2 := by
    rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => 1 / (1 + p.1) ^ 2) hGa]
    have hInner : Integrable (fun z : ℝ => ∫ θ in Spaces.Iθ, 1 / (1 + z) ^ 2)
        (volume.restrict Spaces.Iz) := hGa.integral_prod_left
    have hRHS : Integrable (fun z : ℝ => 2 * (1 / (1 + z) ^ 2)) (volume.restrict Spaces.Iz) :=
      integrable_Iz_one_div_sq.const_mul 2
    calc ∫ z in Spaces.Iz, ∫ θ in Spaces.Iθ, 1 / (1 + z) ^ 2
        ≤ ∫ z in Spaces.Iz, 2 * (1 / (1 + z) ^ 2) := by
          refine integral_mono hInner hRHS (fun z => ?_)
          rw [MeasureTheory.setIntegral_const]
          exact mul_le_mul_of_nonneg_right volumeReal_Iθ_le_two
            (div_nonneg zero_le_one (sq_nonneg _))
      _ = 2 * ∫ z in Spaces.Iz, 1 / (1 + z) ^ 2 := MeasureTheory.integral_const_mul _ _
      _ = 2 := by rw [integral_Iz_one_div_sq]; norm_num
  have hWle : ∫ p, W p ∂P ≤ 2000 * EDthW f := by
    have hWexp : ∫ p, W p ∂P
        = 18 * (∫ p, (Spaces.Dth f p.1 p.2 * Spaces.w p.1) ^ 2 ∂P)
          + (800 * (C0 f) ^ 2) * (∫ p, 1 / (1 + p.1) ^ 2 ∂P) := by
      rw [hW, MeasureTheory.integral_add hW1 hW2, MeasureTheory.integral_const_mul]
      congr 1
      rw [show (fun p : ℝ × ℝ => 800 * (C0 f) ^ 2 / (1 + p.1) ^ 2)
          = fun p => (800 * (C0 f) ^ 2) * (1 / (1 + p.1) ^ 2) from by funext p; ring]
      rw [MeasureTheory.integral_const_mul]
    rw [hWexp, hunorm]
    have hC0nn : 0 ≤ (C0 f) ^ 2 := sq_nonneg _
    have hgam : (800 * (C0 f) ^ 2) * (∫ p, 1 / (1 + p.1) ^ 2 ∂P) ≤ (800 * (C0 f) ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left hGale (by positivity)
    have hkey : (800 * (C0 f) ^ 2) * 2 ≤ 1600 * EDthW f := by
      nlinarith [hC0, hC0nn]
    nlinarith [hkey, hgam, hEdnn]
  constructor
  · rw [IntegrableOn, volume_restrict_prod]
    exact hUint
  · calc ∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2 ∂P
        = ∫ p, (U p) ^ 2 ∂P := by rw [hU]
      _ ≤ ∫ p, W p ∂P := integral_mono_ae hUint hWint hpt
      _ ≤ 2000 * EDthW f := hWle

/-! ## The final numerical inequality -/

/-- `√2000 · A · B ≤ A²/20 + 10⁴ B²` for `A, B ≥ 0`: with `A/√20` and `100 B`, this is
AM–GM, using `√2000 = 200/√20`. -/
theorem sqrt2000_amgm (A B : ℝ) (_hA : 0 ≤ A) (_hB : 0 ≤ B) :
    Real.sqrt 2000 * A * B ≤ A ^ 2 / 20 + 10000 * B ^ 2 := by
  have h20 : Real.sqrt 20 ^ 2 = 20 := Real.sq_sqrt (by norm_num)
  have h20pos : 0 < Real.sqrt 20 := Real.sqrt_pos_of_pos (by norm_num)
  have hsqrt : Real.sqrt 2000 = 200 / Real.sqrt 20 := by
    rw [eq_div_iff (ne_of_gt h20pos)]
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2000) 20]
    rw [show (2000 : ℝ) * 20 = 200 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 200)]
  have hkey : 0 ≤ (A / Real.sqrt 20 - 100 * B) ^ 2 := sq_nonneg _
  have hAM : 2 * (A / Real.sqrt 20) * (100 * B) ≤ (A / Real.sqrt 20) ^ 2 + (100 * B) ^ 2 := by
    nlinarith [hkey]
  have h1 : (A / Real.sqrt 20) ^ 2 = A ^ 2 / 20 := by rw [div_pow, h20]
  have h2 : (100 * B) ^ 2 = 10000 * B ^ 2 := by ring
  rw [h1, h2] at hAM
  have h3 : 2 * (A / Real.sqrt 20) * (100 * B) = Real.sqrt 2000 * A * B := by
    rw [hsqrt]
    field_simp
    ring
  rwa [h3] at hAM

/-! ## The main theorem -/

theorem L2CoercivityTransport (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f : ℝ → ℝ → ℝ)
    (hf : IBP f) (hfH : HardyHyp f) (hΓ : GammaL2Bnd α) (hi : CoerciveData α f) :
    (1 / 5) * Ef f - 10000 * EDthW f
      ≤ wip (fun z _ => Spaces.w z ^ 2) (LGammaT α f) f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Spaces.Iz).prod (volume.restrict Spaces.Iθ) with hP
  have hbase : (1 / 4) * Ef f ≤ wip (fun z _ => Spaces.w z ^ 2) (LGamma α f) f :=
    L2Coercivity α hα hα1 f hf hfH hΓ hi
  have hAeq : wip (fun z _ => Spaces.w z ^ 2) (LGamma α f) f
      = ∫ p, LGamma α f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P := by
    rw [hP]
    exact wip_eq_integral_prod _ _ _ (by simpa using hi.intLG)
  have hT : wip (fun z _ => Spaces.w z ^ 2) (LGammaT α f) f
      = ∫ p, LGammaT α f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P := by
    rw [hP]
    exact wip_eq_integral_prod _ _ _ (by simpa using hi.intLGT)
  have hIntA : Integrable
      (fun p : ℝ × ℝ => LGamma α f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) P :=
    integrableOn_prod hi.intLG
  have hIntB : Integrable (fun p : ℝ × ℝ =>
      Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2) P :=
    integrableOn_prod hi.intP
  have hsplit : (∫ p, LGammaT α f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
      = (∫ p, LGamma α f p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
        - (∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P) := by
    rw [← MeasureTheory.integral_sub hIntA hIntB]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [LGammaT]; ring
  have hEfnn : 0 ≤ Ef f := by
    rw [Ef, Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hEdnn : 0 ≤ EDthW f := by
    rw [EDthW, wip]
    exact integral_nonneg fun z => integral_nonneg fun θ =>
      mul_nonneg (mul_self_nonneg _) (sq_nonneg _)
  have hV2int : Integrable (fun p : ℝ × ℝ => (f p.1 p.2 * Spaces.w p.1) ^ 2) P := by
    have h := integrableOn_prod (f_sq_w_sq_integrable α f hi)
    exact h.congr (Eventually.of_forall fun p => by ring)
  have hEfint : (∫ p, (f p.1 p.2 * Spaces.w p.1) ^ 2 ∂P) = Ef f := by
    rw [hP, Ef_eq_wip, wip_eq_integral_prod (fun z _ => Spaces.w z ^ 2) f f
      (by simpa using f_sq_w_sq_integrable α f hi)]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_)
    ring
  have hC0 : (C0 f) ^ 2 ≤ EDthW f := C0_sq_le_EDthW f hf.smooth hi.intDth
  obtain ⟨hU2intOn, hQle⟩ :=
    ProjTransport_sq_integral_le α hα hα1 f hf.smooth hi.intDth hC0
  have hU2int : Integrable
      (fun p : ℝ × ℝ => (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2) P := by
    rw [show P = volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) from hP.trans volume_restrict_prod.symm]
    exact hU2intOn
  have hUA : MemLp (fun p : ℝ × ℝ => Proj α (Transport f) p.1 p.2 * Spaces.w p.1) 2 P :=
    (memLp_two_iff_integrable_sq (aesm_projTransport_mul_w α f hf.smooth)).2 hU2int
  have hVA : MemLp (fun p : ℝ × ℝ => f p.1 p.2 * Spaces.w p.1) 2 P :=
    (memLp_two_iff_integrable_sq (aesm_f_mul_w hf.smooth)).2 hV2int
  have habsuv : (∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P) ^ 2
      ≤ (∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2 ∂P) * Ef f := by
    have huv : (∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
        = ∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1)
            * (f p.1 p.2 * Spaces.w p.1) ∂P := by
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun p => ?_); ring
    rw [huv]
    have := cs_integral_mul hUA hVA
    rwa [hEfint] at this
  have hQnn : 0 ≤ ∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2 ∂P :=
    integral_nonneg fun p => sq_nonneg _
  have hproj_int_le :
      (∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
        ≤ Real.sqrt 2000 * Real.sqrt (EDthW f) * Real.sqrt (Ef f) := by
    have h1 : |∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P|
        ≤ Real.sqrt ((∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2 ∂P) * Ef f) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt habsuv
    have h2 : Real.sqrt ((∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2 ∂P) * Ef f)
        ≤ Real.sqrt 2000 * Real.sqrt (EDthW f) * Real.sqrt (Ef f) := by
      rw [Real.sqrt_mul hQnn]
      have h3 : Real.sqrt (∫ p, (Proj α (Transport f) p.1 p.2 * Spaces.w p.1) ^ 2 ∂P)
          ≤ Real.sqrt 2000 * Real.sqrt (EDthW f) := by
        have h := Real.sqrt_le_sqrt hQle
        rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2000)] at h
      have h4 := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg (Ef f))
      linarith
    calc (∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P)
        ≤ |∫ p, Proj α (Transport f) p.1 p.2 * f p.1 p.2 * Spaces.w p.1 ^ 2 ∂P| :=
          le_abs_self _
      _ ≤ Real.sqrt 2000 * Real.sqrt (EDthW f) * Real.sqrt (Ef f) := le_trans h1 h2
  have hnum : (1 / 4) * Ef f - Real.sqrt 2000 * Real.sqrt (EDthW f) * Real.sqrt (Ef f)
      ≥ (1 / 5) * Ef f - 10000 * EDthW f := by
    have h := sqrt2000_amgm (Real.sqrt (Ef f)) (Real.sqrt (EDthW f))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt hEfnn, Real.sq_sqrt hEdnn] at h
    linarith
  calc (1 / 5) * Ef f - 10000 * EDthW f
      ≤ (1 / 4) * Ef f - Real.sqrt 2000 * Real.sqrt (EDthW f) * Real.sqrt (Ef f) := hnum
    _ ≤ wip (fun z _ => Spaces.w z ^ 2) (LGammaT α f) f := by
        rw [hT, hsplit, ← hAeq]
        linarith [hbase, hproj_int_le]

end Work.Coercivity
