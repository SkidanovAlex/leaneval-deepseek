import Mathlib
import Submission.Commons.Analysis.Fourier.convolution_kernel_fubini
import Submission.Commons.Analysis.Fourier.lintegral_fourierInv_eq
import Submission.Commons.Analysis.Fourier.nested_scales_maximal_l2_real

namespace Commons.Analysis.Fourier

open MeasureTheory Filter
open scoped BigOperators ENNReal FourierTransform Topology

noncomputable section

set_option maxHeartbeats 1600000

/-! ## Elementary helpers -/

/-- The complex number `2π`, forced through `ℝ`. -/
def twoPiC : ℂ := ((2 * Real.pi : ℝ) : ℂ)

lemma twoPiC_coe : twoPiC = ((2 * Real.pi : ℝ) : ℂ) := rfl

lemma mul_twoPiC_eq (z : ℂ) : 2 * Real.pi * z = twoPiC * z := by
  rw [twoPiC]; push_cast; ring

/-- The `enorm` of a complex number to the power `2` is the `ofReal` of the square of its
norm. -/
lemma enorm_pow_two_eq (z : ℂ) : ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := by
  have h : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
    rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq]; norm_cast
  rw [h, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  exact (ENNReal.ofReal_pow (norm_nonneg z) 2).symm

/-- Substitution `θ = -2π ξ` in the oscillatory integral defining a band kernel. -/
lemma kernel_change_of_variables (M : ℝ → ℂ) (t : ℝ) :
    (∫ θ : ℝ, M θ * Complex.exp (-(Complex.I * (t : ℂ) * (θ : ℂ))))
      = 2 * Real.pi *
        ∫ ξ : ℝ, Complex.exp ((↑(2 * Real.pi * ξ * t) : ℂ) * Complex.I) *
          M (-(2 * Real.pi) * ξ) := by
  have h := Measure.integral_comp_mul_left
    (fun ξ : ℝ => Complex.exp ((↑(2 * Real.pi * ξ * t) : ℂ) * Complex.I) *
      M (-(2 * Real.pi) * ξ))
    (-(1/(2*Real.pi)))
  rw [show (-(1/(2*Real.pi)) : ℝ)⁻¹ = -(2*Real.pi) by field_simp] at h
  rw [abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi), Complex.real_smul] at h
  rw [show (↑(2*Real.pi) : ℂ) = 2 * (↑Real.pi : ℂ) by push_cast; ring] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with θ
  have h1 : (2 * Real.pi * ((-(1/(2*Real.pi))) * θ) * t : ℝ) = -(θ * t) := by field_simp
  have h2 : (-(2 * Real.pi) * ((-(1/(2*Real.pi))) * θ) : ℝ) = θ := by field_simp
  rw [h1, h2, mul_comm (Complex.exp _) (M θ)]
  congr 1
  congr 1
  push_cast
  ring

/-- The band kernel with symbol `m`, in the convention `K z = ∫ θ, m θ · e^{-i z θ}`. -/
def bandKernel (m : ℝ → ℂ) (z : ℝ) : ℂ :=
  ∫ θ : ℝ, m θ * Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ)))

/-- The band kernel is `2π` times the inverse Fourier integral of `ξ ↦ m (-2π ξ)`. -/
lemma bandKernel_eq (m : ℝ → ℂ) (z : ℝ) :
    bandKernel m z = twoPiC * 𝓕⁻ (fun ξ => m (-(2 * Real.pi) * ξ)) z := by
  have h2 : 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) z
      = ∫ v : ℝ, Complex.exp ((↑(2 * Real.pi * (v * z)) : ℂ) * Complex.I) *
          m (-(2 * Real.pi) * v) := by
    rw [Real.fourierInv_eq']
    simp only [Real.inner_apply, smul_eq_mul]
  rw [bandKernel, h2, kernel_change_of_variables m z]
  rw [show (∫ ξ : ℝ, Complex.exp ((↑(2 * Real.pi * ξ * z) : ℂ) * Complex.I) *
        m (-(2 * Real.pi) * ξ))
      = ∫ v : ℝ, Complex.exp ((↑(2 * Real.pi * (v * z)) : ℂ) * Complex.I) *
        m (-(2 * Real.pi) * v) from by
    apply integral_congr_ae
    filter_upwards with v
    rw [show (2 * Real.pi * v * z : ℝ) = 2 * Real.pi * (v * z) from by ring]]
  rw [mul_twoPiC_eq]

/-- The `ℝ≥0∞`-valued `L²` integral of a constant multiple. -/
lemma lintegral_enorm_sq_const_mul (c : ℂ) (w : ℝ → ℂ) :
    (∫⁻ x : ℝ, ‖c * w x‖ₑ ^ (2 : ℝ)) = ENNReal.ofReal (‖c‖ ^ 2) * ∫⁻ x : ℝ, ‖w x‖ₑ ^ (2 : ℝ) := by
  rw [show (∫⁻ x : ℝ, ‖c * w x‖ₑ ^ (2 : ℝ))
      = ∫⁻ x : ℝ, ENNReal.ofReal (‖c‖ ^ 2) * ‖w x‖ₑ ^ (2 : ℝ) from
    lintegral_congr (fun x => by
      rw [enorm_pow_two_eq (c * w x), norm_mul, mul_pow, ENNReal.ofReal_mul (by positivity),
        ← enorm_pow_two_eq (w x)])]
  exact lintegral_const_mul' (ENNReal.ofReal (‖c‖ ^ 2)) (fun x => ‖w x‖ₑ ^ (2 : ℝ))
    ENNReal.ofReal_ne_top

/-- Continuity of the Fourier integral of an `L¹` function. -/
lemma continuous_fourier_of_integrable (H : ℝ → ℂ) (hH : Integrable H) :
    Continuous (fun x : ℝ => 𝓕 H x) :=
  VectorFourier.fourierIntegral_continuous (μ := volume) (L := innerₗ ℝ)
    Real.continuous_fourierChar (by fun_prop) hH

/-- Continuity of `x ↦ ‖g x‖ₑ ^ 2` for a continuous `g`. -/
lemma continuous_enorm_pow_two_comp {g : ℝ → ℂ} (hg : Continuous g) :
    Continuous (fun x => ‖g x‖ₑ ^ (2 : ℝ)) :=
  ENNReal.continuous_rpow_const.comp hg.enorm

/-- Continuity of `z ↦ ‖z‖ₑ ^ 2` on `ℂ`. -/
lemma continuous_enorm_pow_two : Continuous (fun z : ℂ => ‖z‖ₑ ^ (2 : ℝ)) :=
  ENNReal.continuous_rpow_const.comp continuous_enorm

/-- Compact support is preserved by multiplication of the argument by a nonzero constant. -/
lemma hasCompactSupport_comp_mul (m : ℝ → ℂ) (hsupp : HasCompactSupport m) (a : ℝ) (ha : a ≠ 0) :
    HasCompactSupport (fun ξ => m (a * ξ)) := by
  have h := hsupp.comp_homeomorph (Homeomorph.smul (Units.mk0 a ha))
  rw [show (m ∘ ⇑(Homeomorph.smul (Units.mk0 a ha))) = (fun ξ => m (a * ξ)) from by
        funext ξ; simp [Homeomorph.smul_apply, Units.smul_def, Units.val_mk0, smul_eq_mul]] at h
  exact h

/-- A square-integrable function has finite `ℝ≥0∞`-valued squared integral. -/
lemma lintegral_enorm_sq_lt_top_of_memLp {g : ℝ → ℂ} (hg : MemLp g 2 (volume : Measure ℝ)) :
    ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 : ℝ) < ⊤ := by
  have h := hg.eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg.aestronglyMeasurable] at h
  rw [show ((2:ℝ≥0∞).toReal) = 2 by norm_num, show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num] at h
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < (2:ℝ)⁻¹)).mp h

/-- A measurable function with a finite `ℝ≥0∞`-valued squared integral is square-integrable. -/
lemma memLp_two_of_lintegral_enorm_lt_top {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume)
    (h : ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2 : ℝ) < ⊤) : MemLp g 2 (volume : Measure ℝ) := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg]
  rw [show ((2:ℝ≥0∞).toReal) = 2 by norm_num, show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num]
  exact (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < (2:ℝ)⁻¹)).mpr h

/-- The band kernel of a bounded, measurable, compactly supported symbol is square-integrable. -/
lemma bandKernel_memLp (m : ℝ → ℂ) (hm : Measurable m) (hbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) : MemLp (bandKernel m) 2 (volume : Measure ℝ) := by
  have hne : (-(2 * Real.pi) : ℝ) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have h0supp : HasCompactSupport (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) :=
    hasCompactSupport_comp_mul m hsupp _ hne
  have h0as : AEStronglyMeasurable (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) volume :=
    (hm.comp (by fun_prop)).aestronglyMeasurable
  have h0bd : ∀ᵐ ξ : ℝ ∂volume, ‖m (-(2 * Real.pi) * ξ)‖ ≤ 1 :=
    Filter.Eventually.of_forall (fun ξ => hbd _)
  have h0_1 : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) 1 volume :=
    h0supp.memLp_of_bound h0as 1 h0bd
  have h0_2 : MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) 2 volume :=
    h0supp.memLp_of_bound h0as 1 h0bd
  have h0_int : Integrable (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) volume :=
    memLp_one_iff_integrable.mp h0_1
  have hcont : Continuous (fun z : ℝ => 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) z) :=
    continuous_fourierInv_of_integrable _ h0_int
  have hEq : bandKernel m
      = fun z => twoPiC * 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) z := by
    funext z
    rw [bandKernel_eq m z]
  have hFmem : MemLp (fun z : ℝ => 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) z) 2 volume :=
    memLp_two_of_lintegral_enorm_lt_top hcont.aestronglyMeasurable (by
      rw [lintegral_enorm_fourierInv_eq h0_1 h0_2]
      exact lintegral_enorm_sq_lt_top_of_memLp h0_2)
  have hKmem : MemLp (fun z => twoPiC
      * 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) z) 2 volume := hFmem.const_mul _
  rwa [← hEq] at hKmem

/-- The symbol `ξ ↦ m (-2π ξ) · 𝓕 f ξ` of the band operator is `L¹ ∩ L²` when `m` is a bounded,
measurable, compactly supported symbol and `f` is integrable. -/
lemma symbol_memLp (m f : ℝ → ℂ) (hm : Measurable m) (hbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (hf1 : MemLp f 1 (volume : Measure ℝ)) :
    MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 f ξ) 1 (volume : Measure ℝ) ∧
    MemLp (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 f ξ) 2 (volume : Measure ℝ) := by
  have hne : (-(2 * Real.pi) : ℝ) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have h0supp : HasCompactSupport (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) :=
    hasCompactSupport_comp_mul m hsupp _ hne
  have h0as : AEStronglyMeasurable (fun ξ : ℝ => m (-(2 * Real.pi) * ξ)) volume :=
    (hm.comp (by fun_prop)).aestronglyMeasurable
  have hfsupp : HasCompactSupport (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 f ξ) :=
    h0supp.mul_right
  have hfas : AEStronglyMeasurable (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 f ξ) volume :=
    h0as.mul (continuous_fourier_of_integrable f (memLp_one_iff_integrable.mp hf1)).aestronglyMeasurable
  have hbd' : ∀ᵐ ξ : ℝ ∂volume, ‖m (-(2 * Real.pi) * ξ) * 𝓕 f ξ‖ ≤ ∫ x, ‖f x‖ :=
    Filter.Eventually.of_forall (fun ξ => by
      rw [norm_mul]
      calc ‖m (-(2 * Real.pi) * ξ)‖ * ‖𝓕 f ξ‖ ≤ 1 * ‖𝓕 f ξ‖ :=
            mul_le_mul_of_nonneg_right (hbd _) (norm_nonneg _)
        _ = ‖𝓕 f ξ‖ := one_mul _
        _ ≤ ∫ x, ‖f x‖ := norm_fourier_le f ξ)
  exact ⟨hfsupp.memLp_of_bound hfas _ hbd', hfsupp.memLp_of_bound hfas _ hbd'⟩

/-- Pointwise identification of the band operator with `2π` times the inverse Fourier integral
of the product of the symbol with the Fourier transform (the `L¹ ∩ L²` case). -/
lemma bandOp_pointwise (m f : ℝ → ℂ) (hm : Measurable m) (hm1 : MemLp m 1 (volume : Measure ℝ))
    (hm2 : MemLp m 2 (volume : Measure ℝ)) (hmtop : MemLp m ⊤ (volume : Measure ℝ))
    (hf1 : MemLp f 1 (volume : Measure ℝ)) (hf2 : MemLp f 2 (volume : Measure ℝ)) (x : ℝ) :
    (∫ y : ℝ, f y * bandKernel m (x - y))
      = twoPiC * 𝓕⁻ (fun ξ => m (-(2 * Real.pi) * ξ) * 𝓕 f ξ) x := by
  rw [show (∫ y : ℝ, f y * bandKernel m (x - y))
        = ∫ y : ℝ, f y * (∫ θ : ℝ, m θ *
            Complex.exp (-(Complex.I * ((x - y : ℝ) : ℂ) * (θ : ℂ)))) from by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
      simp only [bandKernel]]
  rw [convolution_kernel_fubini m f hm hm1 hm2 hmtop hf1 hf2 x, mul_twoPiC_eq]

/-- **The `L¹ ∩ L²` case of the band-pass `L²` bound.** -/
theorem bandOp_l2_le_of_memLp_one (m : ℝ → ℂ) (hm : Measurable m) (hbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (f : ℝ → ℂ) (hf1 : MemLp f 1 (volume : Measure ℝ))
    (hf2 : MemLp f 2 (volume : Measure ℝ)) :
    ∫⁻ x, ‖∫ y : ℝ, f y *
        (∫ θ : ℝ, m θ * Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ ^ (2 : ℝ)
      ∂(volume : Measure ℝ) ≤ ENNReal.ofReal 400 * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂volume := by
  have hm1 : MemLp m 1 (volume : Measure ℝ) :=
    hsupp.memLp_of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbd)
  have hm2 : MemLp m 2 (volume : Measure ℝ) :=
    hsupp.memLp_of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbd)
  have hmtop : MemLp m ⊤ (volume : Measure ℝ) :=
    hsupp.memLp_of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbd)
  obtain ⟨hsym1, hsym2⟩ := symbol_memLp m f hm hbd hsupp hf1
  have hpt : ∀ x : ℝ, (∫ y : ℝ, f y *
      (∫ θ : ℝ, m θ * Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))))
      = twoPiC * 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 f ξ) x := by
    intro x
    rw [← bandOp_pointwise m f hm hm1 hm2 hmtop hf1 hf2 x]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only [bandKernel]
  have hbound : ∫⁻ x, ‖𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 f ξ) x‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ x, ‖𝓕 f x‖ₑ ^ (2 : ℝ) := by
    rw [lintegral_enorm_fourierInv_eq hsym1 hsym2]
    refine lintegral_mono (fun x => ?_)
    rw [enorm_pow_two_eq, enorm_pow_two_eq, norm_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (‖m (-(2 * Real.pi) * x)‖ * ‖𝓕 f x‖) ^ 2 ≤ (1 * ‖𝓕 f x‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (hbd _) (norm_nonneg _)) 2
      _ = ‖𝓕 f x‖ ^ 2 := by ring
  calc ∫⁻ x, ‖∫ y : ℝ, f y *
        (∫ θ : ℝ, m θ * Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ ^ (2 : ℝ)
      = ∫⁻ x, ‖twoPiC * 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 f ξ) x‖ₑ ^ (2 : ℝ) :=
        lintegral_congr (fun x => by rw [hpt x])
    _ = ENNReal.ofReal (‖twoPiC‖ ^ 2)
          * ∫⁻ x, ‖𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 f ξ) x‖ₑ ^ (2 : ℝ) :=
        lintegral_enorm_sq_const_mul _ _
    _ ≤ ENNReal.ofReal (‖twoPiC‖ ^ 2) * ∫⁻ x, ‖𝓕 f x‖ₑ ^ (2 : ℝ) :=
        mul_le_mul_right hbound (ENNReal.ofReal (‖twoPiC‖ ^ 2))
    _ = ENNReal.ofReal (4 * Real.pi ^ 2) * ∫⁻ x, ‖𝓕 f x‖ₑ ^ (2 : ℝ) := by
        rw [show ‖twoPiC‖ ^ 2 = 4 * Real.pi ^ 2 from by
          rw [Complex.sq_norm, twoPiC, Complex.normSq_ofReal]; ring]
    _ = ENNReal.ofReal (4 * Real.pi ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_enorm_fourier_eq (memLp_one_iff_integrable.mp hf1) hf2]
    _ ≤ ENNReal.ofReal 400 * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
          (by nlinarith [Real.pi_lt_four, Real.pi_pos])) (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ))

/-- **`L²` bound for a band-pass operator with a bounded, compactly supported symbol.**  For a
measurable symbol `m` with `‖m θ‖ ≤ 1` for all `θ` and compact support, and for `f ∈ L²(ℝ)`, the
iterated-integral band operator is bounded on `L²` by an absolute constant (Plancherel: the
operator is the Fourier multiplier by `m`). -/
theorem bandOp_l2_multiplier_bound (m : ℝ → ℂ) (hm : Measurable m) (hbd : ∀ θ : ℝ, ‖m θ‖ ≤ 1)
    (hsupp : HasCompactSupport m) (f : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ)) :
    ∫⁻ x, ‖∫ y : ℝ, f y *
        (∫ θ : ℝ, m θ * Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ ^ (2 : ℝ)
      ∂(volume : Measure ℝ) ≤ ENNReal.ofReal 400 * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂volume := by
  have hm1 : MemLp m 1 (volume : Measure ℝ) :=
    hsupp.memLp_of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbd)
  have hm2 : MemLp m 2 (volume : Measure ℝ) :=
    hsupp.memLp_of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbd)
  have hmtop : MemLp m ⊤ (volume : Measure ℝ) :=
    hsupp.memLp_of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbd)
  have hK : MemLp (bandKernel m) 2 (volume : Measure ℝ) := bandKernel_memLp m hm hbd hsupp
  set C₀ : ℝ≥0∞ := ENNReal.ofReal 400 * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) with hC₀
  -- Truncations of `f`
  let S : ℕ → Set ℝ := fun n => Set.Icc (-(n : ℝ)) (n : ℝ)
  let ind : ℕ → ℝ → ℂ := fun n x => Set.indicator (S n) (fun _ => (1 : ℂ)) x
  let fN : ℕ → ℝ → ℂ := fun n x => f x * ind n x
  have hSmeas : ∀ n, MeasurableSet (S n) := fun n => measurableSet_Icc
  have hSfin : ∀ n, volume (S n) ≠ ⊤ := fun n =>
    (isCompact_Icc.measure_lt_top (μ := volume)).ne
  have hindtop : ∀ n, MemLp (ind n) ⊤ (volume : Measure ℝ) := fun n =>
    memLp_indicator_const ⊤ (hSmeas n) 1 (Or.inr (hSfin n))
  have hind2 : ∀ n, MemLp (ind n) 2 (volume : Measure ℝ) := fun n =>
    memLp_indicator_const 2 (hSmeas n) 1 (Or.inr (hSfin n))
  have hswap : ∀ n, (fun x => ind n x * f x) = fN n := fun n => by
    funext x; simp only [fN, ind]; ring
  have hfN2 : ∀ n, MemLp (fN n) 2 (volume : Measure ℝ) := fun n =>
    (hswap n) ▸ (hindtop n).mul hf
  have hfN1 : ∀ n, MemLp (fN n) 1 (volume : Measure ℝ) := fun n =>
    memLp_one_iff_integrable.mpr ((hswap n) ▸ (hind2 n).integrable_mul hf)
  -- Bound for each truncation
  have hleN : ∀ n, ∫⁻ x, ‖fN n x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := fun n =>
    lintegral_mono (fun x => by
      rw [enorm_pow_two_eq, enorm_pow_two_eq]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : ‖fN n x‖ ≤ ‖f x‖ := by
        simp only [fN]
        rw [norm_mul]
        calc ‖f x‖ * ‖ind n x‖ ≤ ‖f x‖ * 1 :=
              mul_le_mul_of_nonneg_left (by
                simp only [ind, Set.indicator_apply]; split_ifs <;> simp) (norm_nonneg _)
          _ = ‖f x‖ := mul_one _
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2)
  have hb : ∀ n, ∫⁻ x, ‖∫ y : ℝ, fN n y * bandKernel m (x - y)‖ₑ ^ (2 : ℝ) ≤ C₀ := by
    intro n
    rw [show (∫⁻ x, ‖∫ y : ℝ, fN n y * bandKernel m (x - y)‖ₑ ^ (2 : ℝ))
        = ∫⁻ x, ‖∫ y : ℝ, fN n y * (∫ θ : ℝ, m θ *
            Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ ^ (2 : ℝ) from by
      refine lintegral_congr (fun x => ?_); simp only [bandKernel]]
    refine le_trans (bandOp_l2_le_of_memLp_one m hm hbd hsupp (fN n) (hfN1 n) (hfN2 n)) ?_
    rw [hC₀]
    exact mul_le_mul_right (hleN n) (ENNReal.ofReal 400)
  -- Pointwise convergence of the truncations
  have hconv : ∀ x, Tendsto (fun n => ∫ y : ℝ, fN n y * bandKernel m (x - y) ∂volume) atTop
      (𝓝 (∫ y : ℝ, f y * bandKernel m (x - y) ∂volume)) := by
    intro x
    have hKx : MemLp (fun y : ℝ => bandKernel m (x - y)) 2 (volume : Measure ℝ) :=
      hK.comp_measurePreserving (Measure.measurePreserving_sub_left (volume : Measure ℝ) x)
    have hbnd : Integrable (fun y : ℝ => ‖f y * bandKernel m (x - y)‖) volume :=
      (hf.integrable_mul hKx).norm
    refine tendsto_integral_of_dominated_convergence
      (fun y : ℝ => ‖f y * bandKernel m (x - y)‖) ?_ hbnd ?_ ?_
    · intro n
      exact (hfN2 n).aestronglyMeasurable.mul hKx.aestronglyMeasurable
    · intro n
      filter_upwards with y
      have h1 : ‖fN n y‖ ≤ ‖f y‖ := by
        simp only [fN]
        rw [norm_mul]
        calc ‖f y‖ * ‖ind n y‖ ≤ ‖f y‖ * 1 :=
              mul_le_mul_of_nonneg_left (by
                simp only [ind, Set.indicator_apply]; split_ifs <;> simp) (norm_nonneg _)
          _ = ‖f y‖ := mul_one _
      calc ‖fN n y * bandKernel m (x - y)‖ = ‖fN n y‖ * ‖bandKernel m (x - y)‖ := norm_mul _ _
        _ ≤ ‖f y‖ * ‖bandKernel m (x - y)‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = ‖f y * bandKernel m (x - y)‖ := by rw [norm_mul]
    · filter_upwards with y
      have hev : ∀ᶠ n : ℕ in atTop, fN n y = f y := by
        filter_upwards [Filter.eventually_ge_atTop (Nat.ceil |y|)] with n hn
        have hy : y ∈ S n := by
          rw [Set.mem_Icc]
          exact abs_le.mp (Nat.ceil_le.mp hn)
        simp only [fN, ind, Set.indicator_of_mem hy, mul_one]
      refine (tendsto_const_nhds (x := f y * bandKernel m (x - y))).congr' ?_
      filter_upwards [hev] with n hn
      rw [hn]
  -- Measurability for Fatou
  have hmeas : ∀ n, Measurable
      (fun x => ‖∫ y : ℝ, fN n y * bandKernel m (x - y)‖ₑ ^ (2 : ℝ)) := by
    intro n
    obtain ⟨hs1, _⟩ := symbol_memLp m (fN n) hm hbd hsupp (hfN1 n)
    have hint : Integrable (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 (fN n) ξ) volume :=
      memLp_one_iff_integrable.mp hs1
    have hcont := continuous_fourierInv_of_integrable _ hint
    rw [show (fun x => ‖∫ y : ℝ, fN n y * bandKernel m (x - y)‖ₑ ^ (2 : ℝ))
        = fun x => ‖twoPiC * 𝓕⁻ (fun ξ : ℝ => m (-(2 * Real.pi) * ξ) * 𝓕 (fN n) ξ) x‖ₑ ^ (2 : ℝ)
        from funext (fun x => by
          rw [bandOp_pointwise m (fN n) hm hm1 hm2 hmtop (hfN1 n) (hfN2 n) x])]
    exact (continuous_enorm_pow_two_comp
      ((continuous_const : Continuous fun _ : ℝ => twoPiC).mul hcont)).measurable
  -- Fatou
  have hmain : ∫⁻ x, ‖∫ y : ℝ, f y * bandKernel m (x - y)‖ₑ ^ (2 : ℝ) ≤ C₀ := by
    have h1 : ∫⁻ x, ‖∫ y : ℝ, f y * bandKernel m (x - y)‖ₑ ^ (2 : ℝ)
        = ∫⁻ x, liminf
            (fun n => ‖∫ y : ℝ, fN n y * bandKernel m (x - y)‖ₑ ^ (2 : ℝ)) atTop := by
      refine lintegral_congr (fun x => ?_)
      refine (Filter.Tendsto.liminf_eq ?_).symm
      exact (continuous_enorm_pow_two.tendsto _).comp (hconv x)
    rw [h1]
    refine le_trans (lintegral_liminf_le hmeas) ?_
    exact Filter.liminf_le_of_frequently_le (Filter.Frequently.of_forall hb)
      ⟨0, Filter.Eventually.of_forall (fun n => bot_le)⟩
  -- Convert the statement
  rw [hC₀] at hmain
  rwa [show (∫⁻ x, ‖∫ y : ℝ, f y * (∫ θ : ℝ, m θ *
        Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ ^ (2 : ℝ))
      = ∫⁻ x, ‖∫ y : ℝ, f y * bandKernel m (x - y)‖ₑ ^ (2 : ℝ) from by
    refine lintegral_congr (fun x => ?_); simp only [bandKernel]]

end

end Commons.Analysis.Fourier
