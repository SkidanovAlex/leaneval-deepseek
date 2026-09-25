/-
Progress notes for `Commons.Analysis.Fourier.one_sided_geometric_maximal_l2`.

# Strategy (fully worked out; formalisation partially done)

Write `h_j = 2^{-(j:ℝ)-1}`, `a_j = h_j/(2π)`, and
`T_j f x = ∫ y, f y * (∫_{θ=0}^{h_j} e^{-i (x-y) θ} dθ)` (the operator of the statement).

1. **Reduction to a Fourier multiplier** (DONE: `sharp_identity`).
   `∫ θ in 0..h_j, e^{-i (x-y) θ} = ∫ θ, 1_{[0,h_j]}(θ) · e^{-i(x-y)θ}`; apply
   `Commons.Analysis.Fourier.convolution_kernel_fubini` with `M = 1_{[0,h_j]}` to get
   for `f ∈ L¹ ∩ L²`:
   `T_j f x = 2π · 𝓕⁻ (fun ξ => 1_{[-a_j,0]}(ξ) · 𝓕 f ξ) x`  (pointwise, all `x`).

2. **Smooth/boundary split.**  With the Gaussian symbol `m_j ξ = exp(-π (ξ/a_j)²)` and the
   Gaussian kernel `sig_j y = 2π a_j · exp(-π (a_j y)²)` (whose Fourier integral equals
   `2π m_j`, DONE modulo one algebra step in `sig_fourier`), and
   `b_j = 1_{[-a_j,0]} - m_j · 1_{(-∞,0]}`:
   `1_{[-a_j,0]} = (m_j · 1_{≤0}) + b_j`.

   * **Smooth term** `∫ ξ, m_j ξ · 1_{≤0}(ξ) · 𝓕f ξ · e^{2π i x ξ} dξ`: substituting the Fourier
     integral of `sig_j` and applying Fubini (legitimate because `𝓕f ∈ L¹` for `f` Schwartz)
     gives `(1/2π) ∫ y, sig_j y · g(x-y) dy` where `g := 𝓕⁻(1_{≤0}·𝓕f)`.  Since `sig_j/(2π)` is a
     positive approximate identity at spatial scale `1/a_j`, the elementary shell estimate gives
     `|(1/2π)·(sig_j * g)(x)| ≤ C · M g x` where `M` is the Hardy–Littlewood maximal function.
     (An abstract form of this shell estimate is the requested commons lemma
      `Commons.Analysis.HardyLittlewood.lintegral_comp_mul_kernel_le_hlMax`; it can also be
      proved directly.)

   * **Boundary term** `∫ ξ, b_j ξ · 𝓕f ξ · e^{2π i x ξ} dξ`: pointwise
     `sup_j |...| ≤ (∑_j |...|²)^{1/2}`, and by `Commons.Analysis.Fourier.lintegral_fourierInv_eq`
     (Plancherel for the pointwise inverse FT of an `L¹ ∩ L²` function)
     `∑_j ∫ |𝓕⁻(b_j · 𝓕f)|² = ∑_j ∫ |b_j|² |𝓕f|² = ∫ (∑_j |b_j|²) |𝓕f|² ≤ C ‖f‖²`,
     using the one-dimensional bound `∑_j |b_j(ξ)|² ≤ C` (the requested commons lemma
     `Commons.Analysis.Fourier.geometric_gaussian_complement_tsum_le`).

3. **Assembly.**  `|T_j f x| ≤ 2π (|smooth_j x| + |boundary_j x|)`, so
   `sup_j |T_j f x| ≤ 2π (C M g x + (∑_j |boundary_j x|²)^{1/2})`; integrating and using the
   Hardy–Littlewood strong `(2,2)` bound `Commons.Analysis.Maximal.real_maximal_strong_type`
   (applied to `‖g‖`) plus `‖g‖ ≤ ‖f‖` gives the inequality for `f` Schwartz.

4. **Extension to `f ∈ L²` by Fatou.**  Approximate `f ∈ L²` by Schwartz functions `f_n → f`
   (`SchwartzMap.denseRange_toLpCLM`).  For each `j`, `T_j f_n → T_j f` uniformly in `x`
   (Cauchy–Schwarz, `‖K_j‖₂ < ∞`), hence `⨆_j ‖T_j f_n x‖ → ⨆_j ‖T_j f x‖` pointwise; Fatou's
   lemma gives the inequality for `f`.

## Why this does not need Carleson
The `sup_j` is only over the *geometric* family of cutoffs `[-a_j,0]` (ratio 2); the boundary
layers of consecutive scales are disjoint, so `∑_j |b_j|²` is bounded — the crux of the
"geometric maximal" estimate.  This is exactly why the smooth/boundary decomposition of the
sharp cutoff converges.
-/

import Mathlib
import Submission.Commons.Analysis.Fourier.convolution_kernel_fubini
import Submission.Commons.Analysis.Fourier.lintegral_fourierInv_eq
import Submission.Commons.Analysis.Maximal.real_maximal_strong_type
import Submission.Commons.Analysis.HardyLittlewood.lintegral_convolution_radial_decreasing_measurable_le_hlMax

open MeasureTheory
open Commons.Analysis.Maximal
open Filter
open scoped ENNReal FourierTransform RealInnerProductSpace

set_option maxHeartbeats 1600000

namespace Commons.Analysis.Fourier

noncomputable section

namespace OneSided

def hj (j : ℕ) : ℝ := (2:ℝ)^(-(j:ℝ)-1)
def aj (j : ℕ) : ℝ := hj j / (2*Real.pi)

lemma hj_pos (j : ℕ) : 0 < hj j := Real.rpow_pos_of_pos (by norm_num) _
lemma aj_pos (j : ℕ) : 0 < aj j := div_pos (hj_pos j) (by positivity)
lemma aj_ne (j : ℕ) : aj j ≠ 0 := ne_of_gt (aj_pos j)

/-- The Gaussian kernel. -/
def sig (j : ℕ) (y : ℝ) : ℝ := (2*Real.pi*aj j) * Real.exp (-(Real.pi*(aj j*y)^2))
/-- The Gaussian symbol. -/
def mj (j : ℕ) (ξ : ℝ) : ℝ := Real.exp (-(Real.pi*(ξ/aj j)^2))

lemma icc_measure_ne_top (a b : ℝ) : volume (Set.Icc a b) ≠ ⊤ := by
  rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

lemma indicator_memLp_one (a b : ℝ) :
    MemLp ((Set.Icc a b).indicator (fun _ : ℝ => (1:ℂ))) 1 volume :=
  memLp_indicator_const 1 measurableSet_Icc (1:ℂ) (Or.inr (icc_measure_ne_top a b))

lemma indicator_memLp_top (a b : ℝ) :
    MemLp ((Set.Icc a b).indicator (fun _ : ℝ => (1:ℂ))) ⊤ volume := by
  refine memLp_top_of_bound (measurable_const.indicator measurableSet_Icc).aestronglyMeasurable 1 ?_
  filter_upwards with x
  rw [Set.indicator_apply]; split_ifs <;> simp

lemma indicator_memLp_two (a b : ℝ) :
    MemLp ((Set.Icc a b).indicator (fun _ : ℝ => (1:ℂ))) 2 volume :=
  memLp_indicator_const 2 measurableSet_Icc (1:ℂ) (Or.inr (icc_measure_ne_top a b))

/-- The Gauss–Weierstrass integral identity `∫ e^{-πu²} e^{-2πitu} du = e^{-πt²}`. -/
lemma gauss_ft (t : ℝ) :
    (∫ u : ℝ, Complex.exp (-(Real.pi * (u:ℂ)^2)) * Complex.exp (-(2*Real.pi*Complex.I*(t:ℂ)*(u:ℂ))))
      = Complex.exp (-(Real.pi * (t:ℂ)^2)) := by
  have h := fourier_gaussian_pi (b := (1:ℂ)) (by norm_num)
  have hfun := congrFun h t
  rw [Real.fourier_eq'] at hfun
  simp only [one_div, Complex.one_cpow, one_mul, div_one, Real.inner_apply,
    smul_eq_mul] at hfun
  rw [show (-(Real.pi * (t:ℂ)^2)) = -Real.pi * (t:ℂ)^2 from by ring]
  rw [← hfun]
  apply integral_congr_ae; filter_upwards with u
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- The Fourier integral of the Gaussian kernel equals `2π` times the symbol
(up to the final algebra step, which is an instance of `field_simp`/`ring`). -/
lemma sig_fourier (j : ℕ) (ξ : ℝ) :
    (∫ y : ℝ, (sig j y : ℂ) * Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ))))
      = 2*Real.pi * (mj j ξ : ℂ) := by
  have ha : 0 < aj j := aj_pos j
  have hL : (∫ y : ℝ, (sig j y : ℂ) * Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ))))
      = ((2*Real.pi*aj j : ℝ) : ℂ) *
          ∫ y : ℝ, Complex.exp (-(Real.pi * ((aj j * y : ℝ):ℂ)^2))
            * Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ))) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae; filter_upwards with y
    have heq : (sig j y : ℂ) = ((2*Real.pi*aj j:ℝ):ℂ) * Complex.exp (-(Real.pi * ((aj j*y:ℝ):ℂ)^2)) := by
      rw [sig, Complex.ofReal_mul, Complex.ofReal_exp]
      congr 1; congr 1; push_cast; ring
    rw [heq]; ring
  rw [hL]
  have hsub : (∫ y : ℝ, Complex.exp (-(Real.pi * ((aj j * y : ℝ):ℂ)^2))
        * Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ))))
      = (aj j)⁻¹ * (∫ u : ℝ, Complex.exp (-(Real.pi * (u:ℂ)^2))
          * Complex.exp (-(2*Real.pi*Complex.I*((ξ/aj j:ℝ):ℂ)*(u:ℂ)))) := by
    set g : ℝ → ℂ := fun u => Complex.exp (-(Real.pi*(u:ℂ)^2))
        * Complex.exp (-(2*Real.pi*Complex.I*((ξ/aj j:ℝ):ℂ)*(u:ℂ))) with hg
    have h := MeasureTheory.Measure.integral_comp_mul_left g (aj j)
    have hconv : (∫ x : ℝ, g (aj j * x))
        = ∫ y : ℝ, Complex.exp (-(Real.pi * ((aj j * y : ℝ):ℂ)^2))
            * Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ))) := by
      apply integral_congr_ae; filter_upwards with x
      simp only [hg]
      rw [show (((aj j)*x:ℝ):ℂ) = (aj j:ℂ)*(x:ℂ) by push_cast; ring]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp [show ((aj j:ℝ):ℂ) ≠ 0 by simpa using aj_ne j]
    rw [← hconv, h, abs_of_pos (inv_pos.mpr ha), Complex.real_smul, Complex.ofReal_inv]
  rw [hsub, gauss_ft (ξ/aj j), mj, Complex.ofReal_exp]
  have ha' : ((aj j:ℝ):ℂ) ≠ 0 := by simpa using aj_ne j
  rw [show (↑(2*Real.pi*aj j) : ℂ) = 2*↑Real.pi*↑(aj j) by push_cast; ring]
  rw [show (-(↑Real.pi * ↑(ξ/aj j)^2)) = (↑(-(Real.pi*(ξ/aj j)^2)):ℂ) by push_cast; ring]
  rw [Complex.ofReal_inv]
  rw [show 2 * ↑Real.pi * (↑(aj j)) * ((↑(aj j))⁻¹ * Complex.exp (↑(-(Real.pi*(ξ/aj j)^2))))
      = 2 * ↑Real.pi * ((↑(aj j)) * (↑(aj j))⁻¹) * Complex.exp (↑(-(Real.pi*(ξ/aj j)^2)))
      from by ring]
  rw [mul_inv_cancel₀ ha', mul_one]

/-- **Key reduction.**  The operator of the statement is `2π` times the Fourier multiplier by
`1_{[-a_j,0]}`, for `f ∈ L¹ ∩ L²`. -/
theorem sharp_identity {f : ℝ → ℂ} (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume)
    (j : ℕ) (x : ℝ) :
    (∫ y, f y * (∫ θ in (0:ℝ)..(hj j), Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))))
      = 2 * Real.pi * FourierTransformInv.fourierInv
          (fun ξ => (Set.Icc (0:ℝ) (hj j)).indicator (fun _ => (1:ℂ)) (-(2*Real.pi)*ξ)
            * FourierTransform.fourier f ξ) x := by
  have hinner : ∀ y : ℝ,
      (∫ θ in (0:ℝ)..(hj j), Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))
        = ∫ θ, (Set.Icc (0:ℝ) (hj j)).indicator (fun _ => (1:ℂ)) θ
            * Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))) := by
    intro y
    rw [intervalIntegral.integral_of_le (le_of_lt (hj_pos j))]
    conv_lhs => rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    have h : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simpa using MeasureTheory.measure_singleton (0:ℝ)
    filter_upwards [h] with θ hθ0
    by_cases hI : θ ∈ Set.Ioc (0:ℝ) (hj j)
    · have hIcc : θ ∈ Set.Icc (0:ℝ) (hj j) := ⟨le_of_lt hI.1, hI.2⟩
      rw [Set.indicator_of_mem hI, Set.indicator_of_mem hIcc]; ring
    · rw [Set.indicator_of_notMem hI]
      have hIcc : θ ∉ Set.Icc (0:ℝ) (hj j) := by
        intro hc
        exact hI ⟨lt_of_le_of_ne hc.1 (Ne.symm hθ0), hc.2⟩
      rw [Set.indicator_of_notMem hIcc]; ring
  rw [show (∫ y, f y * (∫ θ in (0:ℝ)..(hj j),
        Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))))
      = ∫ y, f y * (∫ θ, (Set.Icc (0:ℝ) (hj j)).indicator (fun _ => (1:ℂ)) θ
          * Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) from by
    apply integral_congr_ae; filter_upwards with y; rw [hinner y]]
  exact convolution_kernel_fubini ((Set.Icc (0:ℝ) (hj j)).indicator (fun _ : ℝ => (1:ℂ)))
      f (measurable_const.indicator measurableSet_Icc) (indicator_memLp_one 0 (hj j))
      (indicator_memLp_two 0 (hj j)) (indicator_memLp_top 0 (hj j)) hf1 hf2 x


/-! ## Gaussian kernel facts -/

lemma hj_eq (j : ℕ) : hj j = 2*Real.pi * aj j := by
  rw [aj]; field_simp

lemma sig_even (j : ℕ) (y : ℝ) : sig j (-y) = sig j y := by
  simp only [sig]
  rw [show (aj j * -y)^2 = (aj j * y)^2 by ring]

lemma sig_nonneg (j : ℕ) (y : ℝ) : 0 ≤ sig j y := by
  rw [sig]; exact mul_nonneg (mul_nonneg (by positivity) (le_of_lt (aj_pos j))) (Real.exp_nonneg _)

lemma sig_antitone (j : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : sig j y ≤ sig j x := by
  have ha : 0 < aj j := aj_pos j
  have hxy' : aj j * x ≤ aj j * y := by nlinarith
  have habs : |aj j * x| ≤ |aj j * y| := by
    rw [abs_of_nonneg (mul_nonneg ha.le hx), abs_of_nonneg (mul_nonneg ha.le (hx.trans hxy))]
    exact hxy'
  have hsq : (aj j * x)^2 ≤ (aj j * y)^2 := by
    have h2 := pow_le_pow_left₀ (abs_nonneg (aj j*x)) habs 2
    rwa [sq_abs, sq_abs] at h2
  have hexp : Real.exp (-(Real.pi * (aj j * y)^2)) ≤ Real.exp (-(Real.pi*(aj j*x)^2)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hsq])
  rw [sig, sig]; exact mul_le_mul_of_nonneg_left hexp (by positivity)

lemma integral_exp_neg_pi_sq_mul (a : ℝ) (ha : 0 < a) :
    (∫ y : ℝ, Real.exp (-(Real.pi * (a*y)^2))) = 1/a := by
  have hone : (∫ u : ℝ, Real.exp (-(Real.pi * u^2))) = 1 := by
    have h := integral_gaussian Real.pi
    rw [div_self (ne_of_gt Real.pi_pos), Real.sqrt_one] at h
    rw [← h]
    apply integral_congr_ae; filter_upwards with u
    rw [show -(Real.pi * (u:ℝ)^2) = -Real.pi * u^2 from by ring]
  have h2 := MeasureTheory.Measure.integral_comp_mul_left
    (fun u : ℝ => Real.exp (-(Real.pi*u^2))) a
  rw [hone, smul_eq_mul, mul_one, abs_of_pos (inv_pos.mpr ha)] at h2
  rw [show (∫ y : ℝ, Real.exp (-(Real.pi*(a*y)^2)))
        = ∫ y : ℝ, (fun u : ℝ => Real.exp (-(Real.pi*u^2))) (a*y) from rfl, h2, one_div]

lemma integral_sig (j : ℕ) : ∫ y : ℝ, sig j y = 2*Real.pi := by
  have ha : 0 < aj j := aj_pos j
  rw [show (∫ y : ℝ, sig j y)
      = ∫ y : ℝ, (2*Real.pi*aj j) * Real.exp (-(Real.pi*(aj j*y)^2)) from rfl]
  rw [integral_const_mul, integral_exp_neg_pi_sq_mul (aj j) ha]
  field_simp

lemma integrable_sig (j : ℕ) : Integrable (sig j) volume := by
  have hg : Integrable (fun u : ℝ => Real.exp (-Real.pi * u^2)) volume :=
    integrable_exp_neg_mul_sq Real.pi_pos
  have hf1 : Integrable (fun x : ℝ => Real.exp (-Real.pi * (aj j * x)^2)) volume :=
    (integrable_comp_mul_left_iff (fun u : ℝ => Real.exp (-Real.pi * u^2)) (aj_ne j)).mpr hg
  have hfun : (fun x : ℝ => Real.exp (-Real.pi * (aj j * x)^2))
      = fun y : ℝ => Real.exp (-(Real.pi * (aj j * y)^2)) := by
    funext y; congr 1; ring
  rw [hfun] at hf1
  exact hf1.const_mul (2*Real.pi*aj j)

lemma lintegral_ofReal_sig (j : ℕ) :
    ∫⁻ y, ENNReal.ofReal (sig j y) = ENNReal.ofReal (2*Real.pi) := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (integrable_sig j)
    (Filter.Eventually.of_forall (sig_nonneg j)), integral_sig]

/-! ## The inverse Fourier integral and the multiplier symbols -/

/-- The pointwise inverse Fourier integral, written explicitly. -/
def FI (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ ξ : ℝ, Complex.exp ((↑(2*Real.pi*ξ*x) : ℂ) * Complex.I) * h ξ

lemma FI_eq_fourierInv (h : ℝ → ℂ) (x : ℝ) : FI h x = FourierTransformInv.fourierInv h x := by
  rw [Real.fourierInv_eq, FI]
  apply integral_congr_ae; filter_upwards with ξ
  rw [Real.inner_apply, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  congr 1; ring

/-- The indicator of `[a,0]`, as a `ℂ`-valued function. -/
def IccInd (a : ℝ) : ℝ → ℂ := (Set.Icc a 0).indicator (fun _ => (1:ℂ))

/-- The indicator of `(-∞,0]`, as a `ℂ`-valued function. -/
def IicInd : ℝ → ℂ := (Set.Iic 0).indicator (fun _ => (1:ℂ))

/-- The Gaussian symbol `m_j` as a `ℂ`-valued function. -/
def mjC (j : ℕ) : ℝ → ℂ := fun ξ => (mj j ξ : ℂ)

/-- The boundary symbol `b_j = 1_{[-a_j,0]} - m_j 1_{≤ 0}`. -/
def bjC (j : ℕ) : ℝ → ℂ := fun ξ => IccInd (-(aj j)) ξ - IicInd ξ * mjC j ξ

lemma measurable_IccInd (a : ℝ) : Measurable (IccInd a) :=
  measurable_const.indicator measurableSet_Icc
lemma measurable_IicInd : Measurable IicInd := measurable_const.indicator measurableSet_Iic
lemma measurable_mjC (j : ℕ) : Measurable (mjC j) := by
  change Measurable (fun ξ : ℝ => (mj j ξ : ℂ))
  unfold mj
  fun_prop
lemma measurable_bjC (j : ℕ) : Measurable (bjC j) :=
  (measurable_IccInd _).sub (measurable_IicInd.mul (measurable_mjC j))

lemma norm_IccInd_le (a : ℝ) (ξ : ℝ) : ‖IccInd a ξ‖ ≤ 1 := by
  rw [IccInd, Set.indicator_apply]; split_ifs <;> simp
lemma norm_IicInd_le (ξ : ℝ) : ‖IicInd ξ‖ ≤ 1 := by
  rw [IicInd, Set.indicator_apply]; split_ifs <;> simp
lemma norm_ofReal_eq_abs (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

lemma norm_mjC_le (j : ℕ) (ξ : ℝ) : ‖mjC j ξ‖ ≤ 1 := by
  show ‖(mj j ξ : ℂ)‖ ≤ 1
  rw [norm_ofReal_eq_abs, mj, abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg (ξ/aj j)])
lemma norm_bjC_le (j : ℕ) (ξ : ℝ) : ‖bjC j ξ‖ ≤ 2 := by
  rw [bjC]
  calc ‖IccInd (-(aj j)) ξ - IicInd ξ * mjC j ξ‖
      ≤ ‖IccInd (-(aj j)) ξ‖ + ‖IicInd ξ * mjC j ξ‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := by
        have h2 : ‖IicInd ξ * mjC j ξ‖ ≤ 1 := by
          rw [norm_mul]
          nlinarith [norm_IicInd_le ξ, norm_mjC_le j ξ, norm_nonneg (IicInd ξ),
            norm_nonneg (mjC j ξ)]
        linarith [norm_IccInd_le (-(aj j)) ξ]
    _ = 2 := by norm_num

/-- The smooth/boundary splitting of the multiplier `1_{[-a_j,0]}`. -/
lemma indicator_split (j : ℕ) (ξ : ℝ) :
    IccInd (-(aj j)) ξ = mjC j ξ * IicInd ξ + bjC j ξ := by
  rw [bjC]; ring

/-- Integrability of a measurable factor with a uniform bound times an integrable function. -/
lemma integrable_mul_of_norm_le {g h : ℝ → ℂ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hgb : ∀ ξ, ‖g ξ‖ ≤ C) (hh : Integrable h) : Integrable (fun ξ => g ξ * h ξ) := by
  refine Integrable.mono' (hh.norm.const_mul C)
    (hg.aestronglyMeasurable.mul hh.aestronglyMeasurable) ?_
  filter_upwards with ξ
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hgb ξ) (norm_nonneg _)


/-! ## The multiplier in the sharp form, and the smooth/boundary splitting -/

lemma indicator_eq (j : ℕ) :
    (fun ξ : ℝ => (Set.Icc (0:ℝ) (hj j)).indicator (fun _ => (1:ℂ)) (-(2*Real.pi)*ξ))
      = fun ξ => IccInd (-(aj j)) ξ := by
  funext ξ
  rw [IccInd, Set.indicator_apply, Set.indicator_apply]
  have hcond : (ξ ∈ Set.Icc (-(aj j)) 0) ↔ (-(2*Real.pi)*ξ ∈ Set.Icc (0:ℝ) (hj j)) := by
    rw [Set.mem_Icc, Set.mem_Icc, hj_eq j]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  by_cases h : ξ ∈ Set.Icc (-(aj j)) 0
  · rw [if_pos (hcond.mp h), if_pos h]
  · rw [if_neg (fun hc => h (hcond.mpr hc)), if_neg h]

lemma sharp_identity' {f : ℝ → ℂ} (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume)
    (j : ℕ) (x : ℝ) :
    (∫ y, f y * (∫ θ in (0:ℝ)..(hj j), Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))))
      = 2 * Real.pi * FI (fun ξ => IccInd (-(aj j)) ξ * FourierTransform.fourier f ξ) x := by
  have hgoal : FourierTransformInv.fourierInv
      (fun ξ => (Set.Icc (0:ℝ) (hj j)).indicator (fun _ => (1:ℂ)) (-(2*Real.pi)*ξ)
        * FourierTransform.fourier f ξ) x
      = FI (fun ξ => IccInd (-(aj j)) ξ * FourierTransform.fourier f ξ) x := by
    have hfuneq : (fun ξ : ℝ => (Set.Icc (0:ℝ) (hj j)).indicator (fun _ => (1:ℂ)) (-(2*Real.pi)*ξ)
        * FourierTransform.fourier f ξ)
        = fun ξ => IccInd (-(aj j)) ξ * FourierTransform.fourier f ξ := by
      funext ξ; rw [congrFun (indicator_eq j) ξ]
    rw [hfuneq, FI_eq_fourierInv]
  rw [sharp_identity hf1 hf2 j x, hgoal]

/-- The `≤ 0` part of the multiplier, times the Fourier transform of `f`. -/
def Gf (f : ℝ → ℂ) : ℝ → ℂ := fun ξ => IicInd ξ * FourierTransform.fourier f ξ

/-- The smooth part of the symbol. -/
def Sfun (j : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun ξ => mjC j ξ * (IicInd ξ * FourierTransform.fourier f ξ)

/-- The boundary part of the symbol. -/
def Bfun (j : ℕ) (f : ℝ → ℂ) : ℝ → ℂ := fun ξ => bjC j ξ * FourierTransform.fourier f ξ

lemma Gf_eq (f : ℝ → ℂ) : Gf f = fun ξ => IicInd ξ * FourierTransform.fourier f ξ := rfl

lemma integrable_Gf {f : ℝ → ℂ} (hF : Integrable (FourierTransform.fourier f)) :
    Integrable (Gf f) :=
  integrable_mul_of_norm_le measurable_IicInd zero_le_one (fun ξ => norm_IicInd_le ξ) hF

lemma integrable_Sfun {f : ℝ → ℂ} (hF : Integrable (FourierTransform.fourier f)) (j : ℕ) :
    Integrable (Sfun j f) :=
  integrable_mul_of_norm_le (measurable_mjC j) zero_le_one (fun ξ => norm_mjC_le j ξ)
    (integrable_Gf hF)

lemma integrable_Bfun {f : ℝ → ℂ} (hF : Integrable (FourierTransform.fourier f)) (j : ℕ) :
    Integrable (Bfun j f) :=
  integrable_mul_of_norm_le (measurable_bjC j) (by norm_num)
    (fun ξ => norm_bjC_le j ξ) hF

/-- The splitting of the multiplier `1_{[-a_j,0]} = m_j 1_{≤0} + b_j`. -/
lemma fun_split (j : ℕ) (f : ℝ → ℂ) :
    (fun ξ => IccInd (-(aj j)) ξ * FourierTransform.fourier f ξ)
      = fun ξ => Sfun j f ξ + Bfun j f ξ := by
  funext ξ
  rw [Sfun, Bfun, indicator_split j ξ]
  ring


lemma continuous_sig (j : ℕ) : Continuous (sig j) := by
  have : Continuous (fun y : ℝ => (2*Real.pi*aj j) * Real.exp (-(Real.pi*(aj j*y)^2))) := by
    fun_prop
  exact this

lemma measurable_sig (j : ℕ) : Measurable (sig j) := (continuous_sig j).measurable

/-- `mj j ξ` is `(1/2π)` times the Fourier integral of the Gaussian kernel `sig j`. -/
lemma mjC_eq (j : ℕ) (ξ : ℝ) :
    mjC j ξ = (1/(2*Real.pi)) *
      ∫ y : ℝ, (sig j y : ℂ) * Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ))) := by
  have hne : ((2*Real.pi : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  have hmain : ((2*Real.pi : ℝ) : ℂ) * mjC j ξ
      = ∫ y : ℝ, (sig j y : ℂ) * Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ))) := by
    rw [mjC, sig_fourier j ξ]; push_cast; ring
  calc mjC j ξ = ((2*Real.pi : ℝ) : ℂ)⁻¹ * (((2*Real.pi : ℝ) : ℂ) * mjC j ξ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ = ((2*Real.pi : ℝ) : ℂ)⁻¹ *
          ∫ y : ℝ, (sig j y : ℂ) * Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ))) := by
        rw [hmain]
    _ = (1/(2*Real.pi)) *
          ∫ y : ℝ, (sig j y : ℂ) * Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ))) := by
        congr 1
        rw [one_div, ← Complex.ofReal_inv]
        push_cast
        ring_nf

lemma norm_exp_ofReal_mul_I (t : ℝ) : ‖Complex.exp ((↑t : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]; simp

lemma norm_exp_neg_two_pi_I_mul (ξ y : ℝ) :
    ‖Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ)))‖ = 1 := by
  rw [show -(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ)) = ((↑(-(2*Real.pi*ξ*y)) : ℂ) * Complex.I)
    from by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

/-- **The smooth term is the Gaussian convolution.**  For a function `f` whose Fourier transform
is integrable, the smooth part `𝓕⁻(m_j·1_{≤0}·𝓕 f)` of the multiplier family equals the
convolution of the Gaussian kernel `sig j` with `𝓕⁻(1_{≤0}·𝓕 f)`. -/
theorem fubini_gaussian_smooth (j : ℕ) {f : ℝ → ℂ} (hF : Integrable (𝓕 f)) (x : ℝ) :
    (∫ ξ : ℝ, Complex.exp ((↑(2*Real.pi*ξ*x) : ℂ) * Complex.I)
        * (mjC j ξ * (IicInd ξ * 𝓕 f ξ)))
      = (1/(2*Real.pi)) * ∫ y : ℝ, (sig j y : ℂ) *
          (∫ ξ : ℝ, Complex.exp ((↑(2*Real.pi*ξ*(x-y)) : ℂ) * Complex.I)
            * (IicInd ξ * 𝓕 f ξ)) := by
  set A : ℝ → ℝ → ℂ := fun ξ y => Complex.exp ((↑(2*Real.pi*ξ*x) : ℂ) * Complex.I)
      * ((sig j y : ℂ) * (Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ)))
          * (IicInd ξ * 𝓕 f ξ))) with hA
  have hGint : Integrable (fun ξ : ℝ => IicInd ξ * 𝓕 f ξ) := integrable_Gf hF
  have hexp1 : ∀ ξ y : ℝ, Complex.exp ((↑(2*Real.pi*ξ*x) : ℂ) * Complex.I)
      * Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ)))
      = Complex.exp ((↑(2*Real.pi*ξ*(x-y)) : ℂ) * Complex.I) := by
    intro ξ y
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hAInt : Integrable (Function.uncurry A) (volume.prod volume) := by
    have hdom : Integrable (fun z : ℝ × ℝ => ‖IicInd z.1 * 𝓕 f z.1‖ * sig j z.2)
        (volume.prod volume) := hGint.norm.mul_prod (integrable_sig j)
    refine Integrable.mono' hdom ?_ ?_
    · have h1 : AEStronglyMeasurable
          (fun z : ℝ × ℝ => Complex.exp ((↑(2*Real.pi*z.1*x) : ℂ) * Complex.I))
          (volume.prod volume) :=
        (by fun_prop : Continuous
          (fun z : ℝ × ℝ => Complex.exp ((↑(2*Real.pi*z.1*x) : ℂ) * Complex.I))).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun z : ℝ × ℝ => (sig j z.2 : ℂ)) (volume.prod volume) :=
        (Complex.continuous_ofReal.comp ((continuous_sig j).comp continuous_snd)).aestronglyMeasurable
      have h3 : AEStronglyMeasurable
          (fun z : ℝ × ℝ => Complex.exp (-(2*Real.pi*Complex.I*(z.1:ℂ)*(z.2:ℂ))))
          (volume.prod volume) :=
        (by fun_prop : Continuous
          (fun z : ℝ × ℝ => Complex.exp (-(2*Real.pi*Complex.I*(z.1:ℂ)*(z.2:ℂ))))).aestronglyMeasurable
      have h4 : AEStronglyMeasurable (fun z : ℝ × ℝ => IicInd z.1 * 𝓕 f z.1)
          (volume.prod volume) :=
        (measurable_IicInd.comp measurable_fst).aestronglyMeasurable.mul
          hF.aestronglyMeasurable.comp_fst
      exact h1.mul (h2.mul (h3.mul h4))
    · filter_upwards with z
      obtain ⟨ξ, y⟩ := z
      have hnorm : ‖A ξ y‖ = ‖IicInd ξ * 𝓕 f ξ‖ * sig j y := by
        simp only [hA, norm_mul, norm_exp_ofReal_mul_I, norm_exp_neg_two_pi_I_mul,
          norm_ofReal_eq_abs, abs_of_nonneg (sig_nonneg j y), one_mul]
        ring
      rw [Function.uncurry_apply_pair, hnorm]
  have step1 : (∫ ξ : ℝ, Complex.exp ((↑(2*Real.pi*ξ*x) : ℂ) * Complex.I)
        * (mjC j ξ * (IicInd ξ * 𝓕 f ξ)))
      = (1/(2*Real.pi)) * ∫ ξ : ℝ, ∫ y : ℝ, A ξ y := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    have hinner : (∫ y : ℝ, A ξ y)
        = Complex.exp ((↑(2*Real.pi*ξ*x) : ℂ) * Complex.I)
          * ((∫ y : ℝ, (sig j y : ℂ) * Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ))))
            * (IicInd ξ * 𝓕 f ξ)) := by
      rw [hA, integral_const_mul]
      congr 1
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with y
      ring
    rw [mjC_eq j ξ, hinner]
    ring
  have step2 : (∫ ξ : ℝ, ∫ y : ℝ, A ξ y) = ∫ y : ℝ, ∫ ξ : ℝ, A ξ y :=
    MeasureTheory.integral_integral_swap hAInt
  have step3 : (∫ y : ℝ, ∫ ξ : ℝ, A ξ y)
      = ∫ y : ℝ, (sig j y : ℂ)
          * (∫ ξ : ℝ, Complex.exp ((↑(2*Real.pi*ξ*(x-y)) : ℂ) * Complex.I)
            * (IicInd ξ * 𝓕 f ξ)) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    have hpt : A ξ y = (sig j y : ℂ)
        * (Complex.exp ((↑(2*Real.pi*ξ*(x-y)) : ℂ) * Complex.I) * (IicInd ξ * 𝓕 f ξ)) := by
      simp only [hA]
      rw [show Complex.exp ((↑(2*Real.pi*ξ*x) : ℂ) * Complex.I)
            * ((sig j y : ℂ) * (Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ)))
              * (IicInd ξ * 𝓕 f ξ)))
          = (sig j y : ℂ) * ((Complex.exp ((↑(2*Real.pi*ξ*x) : ℂ) * Complex.I)
              * Complex.exp (-(2*Real.pi*Complex.I*(ξ:ℂ)*(y:ℂ)))) * (IicInd ξ * 𝓕 f ξ))
          from by ring,
          hexp1 ξ y]
    rw [hpt]
  rw [step1, step2, step3]


/-! ## The smooth part is bounded by the Hardy--Littlewood maximal function -/

lemma enorm_eq_ofReal_norm (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq]
  norm_cast

lemma enorm_norm_real (z : ℂ) : ‖(‖z‖ : ℝ)‖ₑ = ‖z‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (norm_nonneg _), enorm_eq_ofReal_norm]

lemma norm_one_div_two_pi : ‖(1:ℂ) / (2 * (Real.pi : ℂ))‖ = 1/(2*Real.pi) := by
  have h : (1:ℂ) / (2 * (Real.pi : ℂ)) = ((1/(2*Real.pi) : ℝ) : ℂ) := by
    rw [one_div, show (2 * (Real.pi:ℂ)) = ((2*Real.pi : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_inv]
    rw [show ((2*Real.pi:ℝ)⁻¹) = 1/(2*Real.pi) by rw [one_div]]
  rw [h, norm_ofReal_eq_abs, abs_of_nonneg (by positivity)]

lemma continuous_fourier_of_integrable {h : ℝ → ℂ} (hh : Integrable h) : Continuous (𝓕 h) := by
  have hc : Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) h) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hh
  convert hc using 1
  all_goals (funext w; rw [Real.fourier_eq]; simp only [VectorFourier.fourierIntegral]; congr 1)

lemma continuous_fourierInv_of_integrable {h : ℝ → ℂ} (hh : Integrable h) :
    Continuous (𝓕⁻ h) := by
  rw [show (𝓕⁻ h) = (𝓕 h) ∘ Neg.neg from by
    funext w; rw [Real.fourierInv_eq_fourier_neg]; rfl]
  exact (continuous_fourier_of_integrable hh).comp continuous_neg

/-- The Hardy--Littlewood maximal function only depends on the a.e. class of the function. -/
lemma hlMax_congr_ae {g g' : ℝ → ENNReal} (h : g =ᵐ[volume] g') (x : ℝ) :
    hlMax g x = hlMax g' x := by
  have hIcc : ∀ a b : ℝ, ∫⁻ y in Set.Icc a b, g y = ∫⁻ y in Set.Icc a b, g' y := by
    intro a b
    exact lintegral_congr_ae (MeasureTheory.ae_restrict_of_ae h)
  simp only [hlMax]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    rw [hIcc a b]
    exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab le_rfl))
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le hab (le_of_eq (by rw [hIcc a b]))))

/-- The inverse Fourier transform of the `≤ 0` part of the Fourier transform of `f`. -/
def Ginv (f : ℝ → ℂ) : ℝ → ℂ := FourierTransformInv.fourierInv (Gf f)

lemma continuous_Ginv {f : ℝ → ℂ} (hF : Integrable (𝓕 f)) : Continuous (Ginv f) :=
  continuous_fourierInv_of_integrable (integrable_Gf hF)

lemma FI_Sfun_eq (j : ℕ) {f : ℝ → ℂ} (hF : Integrable (𝓕 f)) (x : ℝ) :
    FI (Sfun j f) x = (1/(2*Real.pi)) * ∫ y : ℝ, (sig j y : ℂ) * Ginv f (x - y) := by
  have hkey : ∀ y : ℝ, Ginv f (x - y)
      = ∫ ξ : ℝ, Complex.exp ((↑(2*Real.pi*ξ*(x-y)) : ℂ) * Complex.I)
          * (IicInd ξ * 𝓕 f ξ) := by
    intro y
    show FourierTransformInv.fourierInv (fun ξ => IicInd ξ * 𝓕 f ξ) (x - y)
        = ∫ ξ : ℝ, Complex.exp ((↑(2*Real.pi*ξ*(x-y)) : ℂ) * Complex.I)
            * (IicInd ξ * 𝓕 f ξ)
    rw [Real.fourierInv_eq]
    apply integral_congr_ae; filter_upwards with ξ
    rw [Real.inner_apply, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
    congr 1; ring
  have h := fubini_gaussian_smooth j hF x
  rw [show (∫ y : ℝ, (sig j y : ℂ) * (∫ ξ : ℝ, Complex.exp ((↑(2*Real.pi*ξ*(x-y)) : ℂ) * Complex.I)
        * (IicInd ξ * 𝓕 f ξ))) = ∫ y : ℝ, (sig j y : ℂ) * Ginv f (x - y) from by
      apply integral_congr_ae; filter_upwards with y; rw [hkey y]] at h
  rw [show FI (Sfun j f) x = (∫ ξ : ℝ, Complex.exp ((↑(2*Real.pi*ξ*x) : ℂ) * Complex.I)
        * (mjC j ξ * (IicInd ξ * 𝓕 f ξ))) from by simp only [FI, Sfun]]
  exact h

/-- **The smooth term is dominated by the Hardy--Littlewood maximal function** (uniformly in the
scale `j`). -/
lemma smooth_bound (j : ℕ) {f : ℝ → ℂ} (hF : Integrable (𝓕 f)) (x : ℝ) :
    ‖FI (Sfun j f) x‖ₑ ≤ hlMax (fun y => ‖Ginv f y‖ₑ) x := by
  have hcG : Continuous (Ginv f) := continuous_Ginv hF
  have hmeas : Measurable (fun y : ℝ => ‖Ginv f y‖ₑ) :=
    (continuous_enorm.comp hcG).measurable
  have h1 : ‖FI (Sfun j f) x‖ₑ ≤ ENNReal.ofReal (1/(2*Real.pi))
      * ∫⁻ y : ℝ, ENNReal.ofReal (sig j y) * ‖Ginv f (x-y)‖ₑ := by
    rw [FI_Sfun_eq j hF x, enorm_mul, enorm_eq_ofReal_norm, norm_one_div_two_pi]
    gcongr
    calc ‖∫ y : ℝ, (sig j y : ℂ) * Ginv f (x-y)‖ₑ
        ≤ ∫⁻ y : ℝ, ‖(sig j y : ℂ) * Ginv f (x-y)‖ₑ :=
          enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y : ℝ, ENNReal.ofReal (sig j y) * ‖Ginv f (x-y)‖ₑ := by
          apply lintegral_congr; intro y
          rw [enorm_mul, enorm_eq_ofReal_norm, norm_ofReal_eq_abs,
            abs_of_nonneg (sig_nonneg j y)]
  have h2 : ∫⁻ y : ℝ, ENNReal.ofReal (sig j y) * ‖Ginv f (x-y)‖ₑ
      = ∫⁻ y : ℝ, ‖Ginv f y‖ₑ * ENNReal.ofReal (sig j (x-y)) := by
    rw [← MeasureTheory.lintegral_sub_left_eq_self
      (fun z : ℝ => ENNReal.ofReal (sig j z) * ‖Ginv f (x - z)‖ₑ) x]
    apply lintegral_congr; intro y
    simp only [sub_sub_cancel]
    rw [mul_comm]
  have h3 : ∫⁻ y : ℝ, ‖Ginv f y‖ₑ * ENNReal.ofReal (sig j (x-y))
      ≤ ENNReal.ofReal (2*Real.pi) * hlMax (fun y => ‖Ginv f y‖ₑ) x := by
    have h := Commons.Analysis.HardyLittlewood.lintegral_convolution_radial_decreasing_measurable_le_hlMax
      (fun z : ℝ => ENNReal.ofReal (sig j z))
      (fun z => by rw [sig_even j z])
      (fun u v hu huv => ENNReal.ofReal_le_ofReal (sig_antitone j hu huv))
      (fun y => ‖Ginv f y‖ₑ) hmeas x
    rwa [lintegral_ofReal_sig j] at h
  calc ‖FI (Sfun j f) x‖ₑ
      ≤ ENNReal.ofReal (1/(2*Real.pi))
          * ∫⁻ y : ℝ, ENNReal.ofReal (sig j y) * ‖Ginv f (x-y)‖ₑ := h1
    _ = ENNReal.ofReal (1/(2*Real.pi))
          * ∫⁻ y : ℝ, ‖Ginv f y‖ₑ * ENNReal.ofReal (sig j (x-y)) := by rw [h2]
    _ ≤ ENNReal.ofReal (1/(2*Real.pi))
          * (ENNReal.ofReal (2*Real.pi) * hlMax (fun y => ‖Ginv f y‖ₑ) x) := by
        gcongr
    _ = (ENNReal.ofReal (1/(2*Real.pi)) * ENNReal.ofReal (2*Real.pi))
          * hlMax (fun y => ‖Ginv f y‖ₑ) x := by rw [mul_assoc]
    _ = hlMax (fun y => ‖Ginv f y‖ₑ) x := by
        rw [← ENNReal.ofReal_mul (show (0:ℝ) ≤ 1/(2*Real.pi) by positivity),
          show (1/(2*Real.pi)) * (2*Real.pi) = 1 by field_simp, ENNReal.ofReal_one, one_mul]


/-! ## The geometric boundary-layer sum: partial sums are bounded -/

lemma gaussian_boundary_partial_sums_le (t : ℝ) (ht : 0 < t) (n : ℕ) :
    ∑ j ∈ Finset.range n,
      (((if t * (2:ℝ)^(j:ℝ) ≤ 1 then (1:ℝ) else 0)
        - Real.exp (-(Real.pi * (t * (2:ℝ)^(j:ℝ))^2))))^2 ≤ 100 := by
  classical
  simp only [Real.rpow_natCast]
  set x : ℕ → ℝ := fun j => t * (2:ℝ)^j with hx
  set T : ℕ → ℝ := fun j =>
    ((if x j ≤ 1 then (1:ℝ) else 0) - Real.exp (-(Real.pi * (x j)^2)))^2 with hT
  have hx_pos : ∀ j, 0 < x j := by intro j; simp only [hx]; positivity
  have hx_mono : ∀ j k, j ≤ k → x j ≤ x k := by
    intro j k hjk
    simp only [hx]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hjk) (le_of_lt ht)
  have hx_succ : ∀ j, x (j+1) = 2 * x j := by
    intro j; simp only [hx, pow_succ]; ring
  -- existence of a level exceeding 1
  have hex : ∃ j, 1 < x j := by
    obtain ⟨n, hn⟩ := exists_nat_gt (1/t)
    refine ⟨n, ?_⟩
    simp only [hx]
    have hn1 : 1/t < (n:ℝ) + 1 := by linarith
    have h2 : ((n:ℝ) + 1) ≤ (2:ℝ)^n := by
      have h : n + 1 ≤ 2^n := Nat.lt_iff_add_one_le.mp Nat.lt_two_pow_self
      exact_mod_cast h
    have ht1 : (1:ℝ) < t * ((n:ℝ) + 1) := by
      have hh := mul_lt_mul_of_pos_left hn1 ht
      rwa [mul_one_div, div_self (ne_of_gt ht)] at hh
    have hle := mul_le_mul_of_nonneg_left h2 (le_of_lt ht)
    linarith
  set M : ℕ := Nat.find hex with hM
  have hMspec : 1 < x M := Nat.find_spec hex
  have hMmin : ∀ j : ℕ, j < M → x j ≤ 1 := fun j hj => le_of_not_gt (Nat.find_min hex hj)
  have hMge : ∀ k : ℕ, 1 < x (k + M) := fun k =>
    lt_of_lt_of_le hMspec (hx_mono M (k+M) (Nat.le_add_left M k))
  -- the auxiliary ratio r
  set r : ℝ := Real.exp (-(2*Real.pi)) with hr
  have hr_pos : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hr_le_half : r ≤ 1/2 := by
    rw [hr]
    have h1 : Real.exp (-(2*Real.pi)) ≤ Real.exp (-(1:ℝ)) := by
      apply Real.exp_le_exp.mpr
      have := Real.pi_gt_three
      linarith
    have h2 : Real.exp (-(1:ℝ)) ≤ 1/2 := by
      rw [Real.exp_neg, show (1:ℝ)/2 = (2:ℝ)⁻¹ by norm_num]
      exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num)).mpr
        (by linarith [Real.add_one_le_exp 1])
    linarith
  have hr_lt_one : r < 1 := lt_of_le_of_lt hr_le_half (by norm_num)
  have hr_norm : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr_nonneg]
  have hT_nonneg : ∀ j : ℕ, 0 ≤ T j := by intro j; simp only [hT]; exact sq_nonneg _
  -- value of T at k + M
  have hT_Mk : ∀ k : ℕ, T (k+M) = Real.exp (-(2*Real.pi * (x (k+M))^2)) := by
    intro k
    have hgt : ¬ (x (k+M) ≤ 1) := not_le.mpr (hMge k)
    simp only [hT]
    rw [if_neg hgt, zero_sub, neg_sq, ← Real.exp_nat_mul]
    congr 1
    ring
  have hx_split : ∀ k : ℕ, x (k+M) = x M * (2:ℝ)^k := by
    intro k
    simp only [hx]
    rw [pow_add]; ring
  have hx2 : ∀ k : ℕ, ((k:ℝ) + 1) ≤ (x (k+M))^2 := by
    intro k
    have h4 : ((k:ℝ)+1) ≤ (4:ℝ)^k := by
      have h4nat : k + 1 ≤ 4^k :=
        Nat.lt_iff_add_one_le.mp (Nat.lt_pow_self (n := k) (by norm_num : 1 < 4))
      exact_mod_cast h4nat
    have h4eq : ((2:ℝ)^k)^2 = (4:ℝ)^k := by rw [sq, ← mul_pow]; norm_num
    have hxM_sq : 1 ≤ (x M)^2 := by nlinarith [hMspec]
    rw [hx_split k, mul_pow, h4eq]
    have h4nn : 0 ≤ (4:ℝ)^k := by positivity
    nlinarith [h4, hxM_sq, h4nn]
  have hT_Mk_le : ∀ k : ℕ, T (k+M) ≤ r^(k+1) := by
    intro k
    rw [hT_Mk k, hr]
    rw [show (Real.exp (-(2*Real.pi)))^(k+1)
          = Real.exp (-(2*Real.pi) * ((k:ℝ)+1)) by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos, hx2 k]
  -- first sum bound, termwise
  have hT_le_j : ∀ j, j < M → T j ≤ Real.pi^2 * (x j)^4 := by
    intro j hj
    have hxj : x j ≤ 1 := hMmin j hj
    simp only [hT]
    rw [if_pos hxj]
    have hexp_le : Real.exp (-(Real.pi * (x j)^2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, sq_nonneg (x j)]
    have hle1 : (1:ℝ) - Real.exp (-(Real.pi * (x j)^2)) ≤ Real.pi * (x j)^2 := by
      have := Real.add_one_le_exp (-(Real.pi * (x j)^2))
      linarith
    have hnn : 0 ≤ (1:ℝ) - Real.exp (-(Real.pi * (x j)^2)) := by linarith
    calc (1 - Real.exp (-(Real.pi * (x j)^2)))^2
        ≤ (Real.pi * (x j)^2)^2 := pow_le_pow_left₀ hnn hle1 2
      _ = Real.pi^2 * (x j)^4 := by ring
  -- key numeric bound on x M
  have hKey : (x M)^4 - (x 0)^4 ≤ 16 := by
    by_cases hM0 : M = 0
    · rw [hM0]; norm_num
    · have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
      obtain ⟨M', hM'⟩ : ∃ M', M = M' + 1 :=
        ⟨M - 1, (Nat.succ_pred_eq_of_pos hMpos).symm⟩
      have h1 : x M' ≤ 1 := hMmin M' (by rw [hM']; exact Nat.lt_succ_self M')
      have hxM_le : x M ≤ 2 := by rw [hM', hx_succ M']; linarith
      have hxb : (x M)^4 ≤ 16 := by
        calc (x M)^4 ≤ (2:ℝ)^4 := pow_le_pow_left₀ (le_of_lt (hx_pos M)) hxM_le 4
          _ = 16 := by norm_num
      have hx0 : 0 ≤ (x 0)^4 := by positivity
      linarith
  have hsum4 : ∑ j ∈ Finset.range M, (x j)^4 ≤ (16:ℝ)/15 := by
    have hterm : ∀ j, (x (j+1))^4 - (x j)^4 = 15 * (x j)^4 := by
      intro j; rw [hx_succ j]; ring
    have htel : ∑ j ∈ Finset.range M, ((x (j+1))^4 - (x j)^4) = (x M)^4 - (x 0)^4 :=
      Finset.sum_range_sub (fun j => (x j)^4) M
    have htel' : 15 * ∑ j ∈ Finset.range M, (x j)^4 = (x M)^4 - (x 0)^4 := by
      rw [Finset.mul_sum]
      exact (Finset.sum_congr rfl (fun j _ => (hterm j).symm)).trans htel
    nlinarith [htel', hKey]
  have hFirst : ∑ j ∈ Finset.range M, T j ≤ Real.pi^2 * (16/15) := by
    calc ∑ j ∈ Finset.range M, T j
        ≤ ∑ j ∈ Finset.range M, Real.pi^2 * (x j)^4 :=
          Finset.sum_le_sum (fun j hj => hT_le_j j (Finset.mem_range.mp hj))
      _ = Real.pi^2 * ∑ j ∈ Finset.range M, (x j)^4 := (Finset.mul_sum _ _ _).symm
      _ ≤ Real.pi^2 * (16/15) := mul_le_mul_of_nonneg_left hsum4 (sq_nonneg Real.pi)
  -- second sum bound
  have hsum_r : Summable (fun k : ℕ => r^(k+1)) := by
    have hbase : Summable (fun k : ℕ => r * r^k) :=
      (summable_geometric_of_norm_lt_one hr_norm).mul_left r
    exact hbase.congr (fun k => by rw [pow_succ]; ring)
  have hsum_g : Summable (fun k : ℕ => T (k+M)) :=
    Summable.of_nonneg_of_le (fun k => hT_nonneg (k+M)) (fun k => hT_Mk_le k) hsum_r
  have hsum_r_le : ∑' k : ℕ, r^(k+1) ≤ 1 := by
    have hval : ∑' k : ℕ, r^(k+1) = r * (1-r)⁻¹ := by
      have e : (fun k : ℕ => r^(k+1)) = (fun k : ℕ => r * r^k) := by
        funext k; rw [pow_succ]; ring
      rw [e, tsum_mul_left, tsum_geometric_of_norm_lt_one hr_norm]
    rw [hval, ← div_eq_mul_inv, div_le_one (by linarith)]
    linarith
  have hSecond : ∑' k : ℕ, T (k+M) ≤ 1 :=
    le_trans (Summable.tsum_le_tsum (fun k => hT_Mk_le k) hsum_g hsum_r) hsum_r_le
  have hgsum : Summable T := by
    rw [← summable_nat_add_iff M]
    exact hsum_g
  calc ∑ j ∈ Finset.range n, T j
      ≤ ∑' j : ℕ, T j := hgsum.sum_le_tsum (Finset.range n) (fun j _ => hT_nonneg j)
    _ ≤ 100 := by
        calc ∑' j : ℕ, T j
            = ∑ i ∈ Finset.range M, T i + ∑' i : ℕ, T (i+M) :=
              (hgsum.sum_add_tsum_nat_add M).symm
          _ ≤ Real.pi^2 * (16/15) + 1 := add_le_add hFirst hSecond
          _ ≤ 100 := by nlinarith [Real.pi_pos, Real.pi_lt_four]


/-! ## The boundary term -/

/-- The boundary profile: `1_{s ≤ 1} - e^{-π s²}`. -/
def beta (s : ℝ) : ℝ := (if s ≤ 1 then (1:ℝ) else 0) - Real.exp (-(Real.pi * s^2))

lemma beta_sq_nonneg (s : ℝ) : 0 ≤ (beta s)^2 := sq_nonneg _

/-- `aj j = (1/4π) * 2^{-j}`, whence `|ξ|/aj j = 4π|ξ| * 2^j`. -/
lemma abs_div_aj (j : ℕ) (ξ : ℝ) :
    |ξ| / aj j = 4*Real.pi*|ξ| * (2:ℝ)^(j:ℝ) := by
  have h2 : (2:ℝ)^(-(j:ℝ)-1) = ((2:ℝ)^(j:ℝ))⁻¹ / 2 := by
    rw [show (-(j:ℝ)-1) = -((j:ℝ)+1) by ring,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]
    ring
  have h3 : (2:ℝ)^(j:ℝ) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  rw [aj, hj, h2]
  field_simp
  ring

lemma bjC_eq_zero_of_pos {j : ℕ} {ξ : ℝ} (hξ : ¬ ξ ≤ 0) : bjC j ξ = 0 := by
  have hnot : ξ ∉ Set.Icc (-(aj j)) 0 := fun h => hξ h.2
  have hnot2 : ξ ∉ Set.Iic (0:ℝ) := hξ
  rw [bjC, IccInd, IicInd, Set.indicator_apply, Set.indicator_apply, if_neg hnot2,
    if_neg hnot]
  simp

lemma norm_bjC (j : ℕ) (ξ : ℝ) :
    ‖bjC j ξ‖ = if ξ ≤ 0 then |beta (|ξ|/aj j)| else 0 := by
  by_cases hξ : ξ ≤ 0
  · have ha : 0 < aj j := aj_pos j
    have hIcc : (ξ ∈ Set.Icc (-(aj j)) 0) ↔ |ξ|/aj j ≤ 1 := by
      rw [Set.mem_Icc, div_le_one ha]
      constructor
      · rintro ⟨h1, -⟩
        rw [abs_of_nonpos hξ]; linarith
      · intro h
        rw [abs_of_nonpos hξ] at h
        exact ⟨by linarith, hξ⟩
    have hmj : (mj j ξ : ℂ) = (Real.exp (-(Real.pi*((|ξ|/aj j))^2)) : ℂ) := by
      have hsq : (ξ/aj j)^2 = (|ξ|/aj j)^2 := by
        rw [show ξ / aj j = -((|ξ|/aj j)) from by rw [abs_of_nonpos hξ]; ring]
        ring
      rw [mj, hsq]
    have hrs : bjC j ξ = ((beta (|ξ|/aj j) : ℝ) : ℂ) := by
      have h1 : bjC j ξ = ((if ξ ∈ Set.Icc (-(aj j)) 0 then (1:ℝ) else 0 : ℝ) : ℂ)
          - ((Real.exp (-(Real.pi*((|ξ|/aj j))^2)) : ℝ) : ℂ) := by
        rw [bjC, IccInd, IicInd, mjC, Set.indicator_apply, Set.indicator_apply,
          if_pos (show ξ ∈ Set.Iic (0:ℝ) from hξ), hmj]
        simp only [one_mul]
        rw [show (if ξ ∈ Set.Icc (-(aj j)) 0 then (1:ℂ) else 0)
            = ((if ξ ∈ Set.Icc (-(aj j)) 0 then (1:ℝ) else 0 : ℝ) : ℂ) by
          split_ifs <;> simp]
      rw [h1, ← Complex.ofReal_sub, beta, if_congr hIcc rfl rfl]
    rw [if_pos hξ, hrs, norm_ofReal_eq_abs]
  · rw [if_neg hξ, bjC_eq_zero_of_pos hξ, norm_zero]

lemma summable_sq_beta {t : ℝ} (ht : 0 < t) :
    Summable (fun j : ℕ => (beta (t * (2:ℝ)^(j:ℝ)))^2) :=
  summable_of_sum_range_le (c := 100) (fun n => beta_sq_nonneg _)
    (fun n => by simpa only [beta] using gaussian_boundary_partial_sums_le t ht n)

lemma tsum_sq_beta_le {t : ℝ} (ht : 0 < t) :
    ∑' j : ℕ, (beta (t * (2:ℝ)^(j:ℝ)))^2 ≤ 100 :=
  le_of_tendsto' (summable_sq_beta ht).hasSum.tendsto_sum_nat
    (fun n => by simpa only [beta] using gaussian_boundary_partial_sums_le t ht n)

lemma bjC_sq_eq_zero (ξ : ℝ) (h0 : ξ = 0) (j : ℕ) : ‖bjC j ξ‖ ^ 2 = 0 := by
  rw [norm_bjC j ξ, if_pos (le_of_eq h0)]
  have hb : beta (|ξ|/aj j) = 0 := by
    rw [h0, beta]; norm_num
  rw [hb, abs_zero, sq, mul_zero]

lemma summable_norm_bjC (ξ : ℝ) : Summable (fun j : ℕ => ‖bjC j ξ‖ ^ 2) := by
  by_cases h0 : ξ = 0
  · simp only [bjC_sq_eq_zero ξ h0]
    exact summable_zero
  · have ht : 0 < 4*Real.pi*|ξ| := by
      have hpos : 0 < |ξ| := abs_pos.mpr h0
      positivity
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
      (summable_sq_beta (t := 4*Real.pi*|ξ|) ht)
    by_cases hξ : ξ ≤ 0
    · rw [norm_bjC j ξ, if_pos hξ, abs_div_aj, sq_abs]
    · rw [norm_bjC j ξ, if_neg hξ]
      simpa using beta_sq_nonneg (4*Real.pi*|ξ| * (2:ℝ)^(j:ℝ))

lemma tsum_norm_bjC_le (ξ : ℝ) : ∑' j : ℕ, ‖bjC j ξ‖ ^ 2 ≤ 100 := by
  by_cases h0 : ξ = 0
  · simp only [bjC_sq_eq_zero ξ h0, tsum_zero]
    norm_num
  · have ht : 0 < 4*Real.pi*|ξ| := by
      have hpos : 0 < |ξ| := abs_pos.mpr h0
      positivity
    calc ∑' j : ℕ, ‖bjC j ξ‖ ^ 2
        ≤ ∑' j : ℕ, (beta (4*Real.pi*|ξ| * (2:ℝ)^(j:ℝ)))^2 := by
          refine Summable.tsum_le_tsum (fun j => ?_) (summable_norm_bjC ξ)
            (summable_sq_beta ht)
          by_cases hξ : ξ ≤ 0
          · rw [norm_bjC j ξ, if_pos hξ, abs_div_aj, sq_abs]
          · rw [norm_bjC j ξ, if_neg hξ]
            simpa using beta_sq_nonneg (4*Real.pi*|ξ| * (2:ℝ)^(j:ℝ))
      _ ≤ 100 := tsum_sq_beta_le ht


/-! ## Boundary bound and assembly -/

lemma lintegral_fourierInv_enorm_sq {h : ℝ → ℂ} (h1 : MemLp h 1 volume)
    (h2 : MemLp h 2 volume) :
    ∫⁻ x, ‖𝓕⁻ h x‖ₑ ^ (2:ℝ) = ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) := by
  simp_rw [enorm_eq_ofReal_norm]
  exact lintegral_fourierInv_eq h1 h2

lemma memLp_Gf {f : ℝ → ℂ} {p : ℝ≥0∞} (hF : MemLp (𝓕 f) p volume) :
    MemLp (Gf f) p volume := by
  refine MemLp.mono hF (measurable_IicInd.aestronglyMeasurable.mul hF.aestronglyMeasurable) ?_
  filter_upwards with ξ
  rw [show Gf f ξ = IicInd ξ * 𝓕 f ξ from rfl, norm_mul]
  calc ‖IicInd ξ‖ * ‖𝓕 f ξ‖ ≤ 1 * ‖𝓕 f ξ‖ :=
        mul_le_mul_of_nonneg_right (norm_IicInd_le ξ) (norm_nonneg _)
    _ = ‖𝓕 f ξ‖ := one_mul _

lemma memLp_Bfun {f : ℝ → ℂ} {p : ℝ≥0∞} (hF : MemLp (𝓕 f) p volume) (j : ℕ) :
    MemLp (Bfun j f) p volume := by
  refine MemLp.mono' (hF.norm.const_mul 2)
    ((measurable_bjC j).aestronglyMeasurable.mul hF.aestronglyMeasurable) ?_
  filter_upwards with ξ
  rw [show Bfun j f ξ = bjC j ξ * 𝓕 f ξ from rfl, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_bjC_le j ξ) (norm_nonneg _)

lemma add_rpow_two_le (A B : ENNReal) :
    (A + B) ^ (2:ℝ) ≤ 4 * (A ^ (2:ℝ) + B ^ (2:ℝ)) := by
  have key : ∀ x : ENNReal, x ^ (2:ℝ) = x * x := by
    intro x; rw [ENNReal.rpow_two, pow_two]
  have hsup : (A ⊔ B) ^ (2:ℝ) ≤ A ^ (2:ℝ) + B ^ (2:ℝ) := by
    rcases le_total A B with h | h
    · rw [max_eq_right h]; exact le_add_left (le_refl _)
    · rw [max_eq_left h]; exact le_add_right (le_refl _)
  have hAB : A + B ≤ 2 * (A ⊔ B) := by
    rw [two_mul]
    exact add_le_add le_sup_left le_sup_right
  calc (A + B) ^ (2:ℝ) ≤ (2 * (A ⊔ B)) ^ (2:ℝ) := ENNReal.rpow_le_rpow hAB (by norm_num)
    _ = 4 * ((A ⊔ B) ^ (2:ℝ)) := by
        rw [key, key]; ring
    _ ≤ 4 * (A ^ (2:ℝ) + B ^ (2:ℝ)) := by gcongr

lemma iSup_sq_le_tsum_sq (a : ℕ → ENNReal) :
    (⨆ j, a j) ^ (2:ℝ) ≤ ∑' j, (a j) ^ (2:ℝ) := by
  have key : ∀ x : ENNReal, x ^ (2:ℝ) = x * x := by
    intro x; rw [ENNReal.rpow_two, pow_two]
  simp only [key]
  rw [ENNReal.mul_iSup]
  simp_rw [ENNReal.iSup_mul]
  refine iSup_le fun k => iSup_le fun j => ?_
  rcases le_total (a j) (a k) with h | h
  · calc a j * a k ≤ a k * a k := by gcongr
      _ ≤ ∑' m, a m * a m := ENNReal.le_tsum (f := fun m => a m * a m) k
  · calc a j * a k ≤ a j * a j := by gcongr
      _ ≤ ∑' m, a m * a m := ENNReal.le_tsum (f := fun m => a m * a m) j

lemma tsum_enorm_bjC_le (ξ : ℝ) :
    ∑' j : ℕ, ‖bjC j ξ‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal 100 := by
  calc ∑' j : ℕ, ‖bjC j ξ‖ₑ ^ (2:ℝ)
      = ∑' j : ℕ, ENNReal.ofReal (‖bjC j ξ‖ ^ 2) := by
        refine tsum_congr fun j => ?_
        rw [enorm_eq_ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
          Real.rpow_two]
    _ = ENNReal.ofReal (∑' j : ℕ, ‖bjC j ξ‖ ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) (summable_norm_bjC ξ)).symm
    _ ≤ ENNReal.ofReal 100 := ENNReal.ofReal_le_ofReal (tsum_norm_bjC_le ξ)

lemma boundary_bound {f : ℝ → ℂ} (hf2 : MemLp f 2 volume)
    (hF1 : MemLp (𝓕 f) 1 volume) (hF2 : MemLp (𝓕 f) 2 volume)
    (hFm : Measurable (𝓕 f)) (hinv : ∀ x, 𝓕⁻ (𝓕 f) x = f x) :
    ∫⁻ x, (⨆ j : ℕ, ‖FI (Bfun j f) x‖ₑ) ^ (2:ℝ)
      ≤ ENNReal.ofReal 100 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
  have hmem1 : ∀ j, MemLp (Bfun j f) 1 volume := fun j => memLp_Bfun hF1 j
  have hmem2 : ∀ j, MemLp (Bfun j f) 2 volume := fun j => memLp_Bfun hF2 j
  have hmeas : ∀ j, AEMeasurable (fun x : ℝ => ‖𝓕⁻ (Bfun j f) x‖ₑ ^ (2:ℝ)) volume := fun j =>
    ((ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp
      (continuous_enorm.measurable.comp (continuous_fourierInv_of_integrable
        (MeasureTheory.memLp_one_iff_integrable.mp (hmem1 j))).measurable)).aemeasurable
  have hmeasB : Measurable (fun ξ : ℝ => ‖𝓕 f ξ‖ₑ ^ (2:ℝ)) :=
    (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp (continuous_enorm.measurable.comp hFm)
  have hmeas2 : ∀ j, AEMeasurable (fun ξ : ℝ => ‖Bfun j f ξ‖ₑ ^ (2:ℝ)) volume := fun j =>
    ((ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp
      (continuous_enorm.measurable.comp ((measurable_bjC j).mul hFm))).aemeasurable
  have hplanch : ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ (2:ℝ) = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
    rw [← lintegral_fourierInv_enorm_sq hF1 hF2]
    apply lintegral_congr; intro x
    rw [hinv x]
  calc ∫⁻ x, (⨆ j, ‖FI (Bfun j f) x‖ₑ) ^ (2:ℝ)
      = ∫⁻ x, (⨆ j, ‖𝓕⁻ (Bfun j f) x‖ₑ) ^ (2:ℝ) := by
        apply lintegral_congr; intro x
        congr 1
        exact iSup_congr fun j => by rw [FI_eq_fourierInv]
    _ ≤ ∫⁻ x, ∑' j, ‖𝓕⁻ (Bfun j f) x‖ₑ ^ (2:ℝ) :=
        lintegral_mono fun x => iSup_sq_le_tsum_sq _
    _ = ∑' j, ∫⁻ x, ‖𝓕⁻ (Bfun j f) x‖ₑ ^ (2:ℝ) :=
        lintegral_tsum hmeas
    _ = ∑' j, ∫⁻ ξ, ‖Bfun j f ξ‖ₑ ^ (2:ℝ) :=
        tsum_congr fun j => lintegral_fourierInv_enorm_sq (hmem1 j) (hmem2 j)
    _ = ∫⁻ ξ, ∑' j, ‖Bfun j f ξ‖ₑ ^ (2:ℝ) := (lintegral_tsum hmeas2).symm
    _ = ∫⁻ ξ, (∑' j, ‖bjC j ξ‖ₑ ^ (2:ℝ)) * ‖𝓕 f ξ‖ₑ ^ (2:ℝ) := by
        apply lintegral_congr; intro ξ
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun j => ?_
        rw [show Bfun j f ξ = bjC j ξ * 𝓕 f ξ from rfl, enorm_mul,
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ ∫⁻ ξ, ENNReal.ofReal 100 * ‖𝓕 f ξ‖ₑ ^ (2:ℝ) := by
        refine lintegral_mono fun ξ => ?_
        gcongr
        exact tsum_enorm_bjC_le ξ
    _ = ENNReal.ofReal 100 * ∫⁻ ξ, ‖𝓕 f ξ‖ₑ ^ (2:ℝ) := lintegral_const_mul _ hmeasB
    _ = ENNReal.ofReal 100 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by rw [hplanch]


/-- The smooth part, maximised over the scales. -/
def Smax (f : ℝ → ℂ) (x : ℝ) : ENNReal := ⨆ j : ℕ, ‖FI (Sfun j f) x‖ₑ

/-- The boundary part, maximised over the scales. -/
def Bmax (f : ℝ → ℂ) (x : ℝ) : ENNReal := ⨆ j : ℕ, ‖FI (Bfun j f) x‖ₑ

lemma measurable_Smax {f : ℝ → ℂ} (hFi : Integrable (𝓕 f)) : Measurable (Smax f) := by
  refine Measurable.iSup fun j => ?_
  have hcont : Continuous (fun b => FI (Sfun j f) b) := by
    rw [show (fun b => FI (Sfun j f) b) = fun b => 𝓕⁻ (Sfun j f) b from
      funext fun b => FI_eq_fourierInv _ b]
    exact continuous_fourierInv_of_integrable (integrable_Sfun hFi j)
  exact continuous_enorm.measurable.comp hcont.measurable

lemma measurable_Smax' {f : ℝ → ℂ} (hFi : Integrable (𝓕 f)) :
    Measurable (fun x => (Smax f x) ^ (2:ℝ)) :=
  (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp (measurable_Smax hFi)

lemma measurable_Bmax {f : ℝ → ℂ} (hFi : Integrable (𝓕 f)) : Measurable (Bmax f) := by
  refine Measurable.iSup fun j => ?_
  have hcont : Continuous (fun b => FI (Bfun j f) b) := by
    rw [show (fun b => FI (Bfun j f) b) = fun b => 𝓕⁻ (Bfun j f) b from
      funext fun b => FI_eq_fourierInv _ b]
    exact continuous_fourierInv_of_integrable (integrable_Bfun hFi j)
  exact continuous_enorm.measurable.comp hcont.measurable

lemma measurable_Bmax' {f : ℝ → ℂ} (hFi : Integrable (𝓕 f)) :
    Measurable (fun x => (Bmax f x) ^ (2:ℝ)) :=
  (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp (measurable_Bmax hFi)

/-- Integrability against a unimodular exponential factor. -/
lemma integrable_exp_mul {h : ℝ → ℂ} (hh : Integrable h) (x : ℝ) :
    Integrable (fun ξ : ℝ => Complex.exp ((↑(2*Real.pi*ξ*x) : ℂ) * Complex.I) * h ξ) := by
  refine Integrable.mono' hh.norm ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
    hh.aestronglyMeasurable) ?_
  filter_upwards with ξ
  rw [norm_mul, norm_exp_ofReal_mul_I, one_mul]

lemma norm_two_pi : ‖(2:ℂ) * (Real.pi : ℂ)‖ = 2*Real.pi := by
  rw [show (2:ℂ) * (Real.pi : ℂ) = ((2*Real.pi : ℝ) : ℂ) by push_cast; ring]
  rw [norm_ofReal_eq_abs, abs_of_nonneg (by positivity)]

/-- **The estimate for functions with integrable Fourier transform.** -/
theorem schwartz_case :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℂ) (hf1 : MemLp f 1 volume) (hf2 : MemLp f 2 volume)
      (hF1 : MemLp (𝓕 f) 1 volume) (hF2 : MemLp (𝓕 f) 2 volume)
      (hFm : Measurable (𝓕 f)) (hinv : ∀ x, 𝓕⁻ (𝓕 f) x = f x),
      ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
          (∫ θ in (0:ℝ)..(hj j), Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ)
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
  obtain ⟨Chl, hChl_pos, hChl⟩ := real_maximal_strong_type 2 (by norm_num : (1:ℝ) < 2)
  refine ⟨2*Real.pi*2*Real.sqrt (Chl^2 + 100), by positivity, ?_⟩
  intro f hf1 hf2 hF1 hF2 hFm hinv
  have hFi : Integrable (𝓕 f) := MeasureTheory.memLp_one_iff_integrable.mp hF1
  have hT : ∀ j x, ‖∫ y : ℝ, f y *
        (∫ θ in (0:ℝ)..(hj j), Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ
      ≤ ENNReal.ofReal (2*Real.pi) * (‖FI (Sfun j f) x‖ₑ + ‖FI (Bfun j f) x‖ₑ) := by
    intro j x
    rw [sharp_identity' hf1 hf2 j x]
    have hlin : FI (fun ξ => IccInd (-(aj j)) ξ * 𝓕 f ξ) x
        = FI (Sfun j f) x + FI (Bfun j f) x := by
      simp only [FI]
      rw [show (∫ ξ : ℝ, Complex.exp ((↑(2*Real.pi*ξ*x) : ℂ) * Complex.I)
              * (IccInd (-(aj j)) ξ * 𝓕 f ξ))
            = ∫ ξ : ℝ, (Complex.exp ((↑(2*Real.pi*ξ*x) : ℂ) * Complex.I) * Sfun j f ξ
                + Complex.exp ((↑(2*Real.pi*ξ*x) : ℂ) * Complex.I) * Bfun j f ξ) from by
          apply integral_congr_ae; filter_upwards with ξ
          rw [congrFun (fun_split j f) ξ]; ring]
      rw [integral_add (integrable_exp_mul (integrable_Sfun hFi j) x)
        (integrable_exp_mul (integrable_Bfun hFi j) x)]
    rw [hlin, enorm_mul, enorm_eq_ofReal_norm, norm_two_pi]
    gcongr
    exact enorm_add_le _ _
  have hpt : ∀ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
        (∫ θ in (0:ℝ)..(hj j), Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ)
      ≤ ENNReal.ofReal ((2*Real.pi)^2 * 4) * ((Smax f x) ^ (2:ℝ) + (Bmax f x) ^ (2:ℝ)) := by
    intro x
    have h1 : (⨆ j : ℕ, ‖∫ y : ℝ, f y *
          (∫ θ in (0:ℝ)..(hj j), Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ)
        ≤ ENNReal.ofReal (2*Real.pi) * (Smax f x + Bmax f x) := by
      rw [show Smax f x = ⨆ j : ℕ, ‖FI (Sfun j f) x‖ₑ from rfl,
        show Bmax f x = ⨆ j : ℕ, ‖FI (Bfun j f) x‖ₑ from rfl]
      refine iSup_le fun j => ?_
      calc ‖∫ y : ℝ, f y * (∫ θ in (0:ℝ)..(hj j),
            Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ
          ≤ ENNReal.ofReal (2*Real.pi)
              * (‖FI (Sfun j f) x‖ₑ + ‖FI (Bfun j f) x‖ₑ) := hT j x
        _ ≤ ENNReal.ofReal (2*Real.pi)
              * ((⨆ j : ℕ, ‖FI (Sfun j f) x‖ₑ) + (⨆ j : ℕ, ‖FI (Bfun j f) x‖ₑ)) := by
            gcongr
            · exact le_iSup (fun j => ‖FI (Sfun j f) x‖ₑ) j
            · exact le_iSup (fun j => ‖FI (Bfun j f) x‖ₑ) j
    calc (⨆ j : ℕ, ‖∫ y : ℝ, f y *
          (∫ θ in (0:ℝ)..(hj j), Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ)
        ≤ (ENNReal.ofReal (2*Real.pi) * (Smax f x + Bmax f x)) ^ (2:ℝ) :=
          ENNReal.rpow_le_rpow h1 (by norm_num)
      _ = (ENNReal.ofReal (2*Real.pi)) ^ (2:ℝ) * (Smax f x + Bmax f x) ^ (2:ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ ≤ (ENNReal.ofReal (2*Real.pi)) ^ (2:ℝ)
            * (4 * ((Smax f x) ^ (2:ℝ) + (Bmax f x) ^ (2:ℝ))) := by
          gcongr
          exact add_rpow_two_le _ _
      _ = ENNReal.ofReal ((2*Real.pi)^2 * 4) * ((Smax f x) ^ (2:ℝ) + (Bmax f x) ^ (2:ℝ)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ 2*Real.pi)
                (by norm_num : (0:ℝ) ≤ 2), Real.rpow_two]
          rw [show ENNReal.ofReal ((2*Real.pi) ^ 2) * (4 * ((Smax f x) ^ (2:ℝ) + (Bmax f x) ^ (2:ℝ)))
                = (ENNReal.ofReal ((2*Real.pi) ^ 2) * 4)
                  * ((Smax f x) ^ (2:ℝ) + (Bmax f x) ^ (2:ℝ)) from by ring]
          congr 1
          rw [show (4:ENNReal) = ENNReal.ofReal 4 by norm_num,
            ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2*Real.pi)^2)]
  have hd : ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
        (∫ θ in (0:ℝ)..(hj j), Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ)
      ≤ ENNReal.ofReal ((2*Real.pi)^2 * 4)
          * ((∫⁻ x, (Smax f x) ^ (2:ℝ)) + (∫⁻ x, (Bmax f x) ^ (2:ℝ))) := by
    calc ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
          (∫ θ in (0:ℝ)..(hj j), Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ)
        ≤ ∫⁻ x, ENNReal.ofReal ((2*Real.pi)^2 * 4)
            * ((Smax f x) ^ (2:ℝ) + (Bmax f x) ^ (2:ℝ)) := lintegral_mono hpt
      _ = ENNReal.ofReal ((2*Real.pi)^2 * 4)
            * ∫⁻ x, ((Smax f x) ^ (2:ℝ) + (Bmax f x) ^ (2:ℝ)) :=
          lintegral_const_mul _ ((measurable_Smax' hFi).add (measurable_Bmax' hFi))
      _ = ENNReal.ofReal ((2*Real.pi)^2 * 4)
            * ((∫⁻ x, (Smax f x) ^ (2:ℝ)) + (∫⁻ x, (Bmax f x) ^ (2:ℝ))) := by
          rw [lintegral_add_left (measurable_Smax' hFi)]
  have he : ∫⁻ x, (Smax f x) ^ (2:ℝ) ≤ ENNReal.ofReal (Chl^2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
    have hpoint : ∀ x, Smax f x ≤ hlMax (fun y => ‖Ginv f y‖ₑ) x := fun x =>
      iSup_le fun j => smooth_bound j hFi x
    have hfun : (fun y : ℝ => ‖(‖Ginv f y‖ : ℝ)‖ₑ) = fun y => ‖Ginv f y‖ₑ := by
      funext y
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (norm_nonneg _), enorm_eq_ofReal_norm]
    have hhl := hChl (fun y : ℝ => ‖Ginv f y‖)
    simp only [enorm_norm_real, hlMax, ENNReal.rpow_two, Real.rpow_two] at hhl
    have h1 : ∫⁻ x, (Smax f x) ^ (2:ℝ) ≤ ∫⁻ x, (hlMax (fun y => ‖Ginv f y‖ₑ) x) ^ (2:ℝ) :=
      lintegral_mono fun x => ENNReal.rpow_le_rpow (hpoint x) (by norm_num)
    have h2 : ∫⁻ x, (hlMax (fun y => ‖Ginv f y‖ₑ) x) ^ (2:ℝ)
        ≤ ENNReal.ofReal (Chl^2) * ∫⁻ x, ‖Ginv f x‖ₑ ^ (2:ℝ) := by
      simpa only [hlMax, ENNReal.rpow_two] using hhl
    have h3 : ∫⁻ x, ‖Ginv f x‖ₑ ^ (2:ℝ) ≤ ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
      have hGF : ∫⁻ x, ‖Ginv f x‖ₑ ^ (2:ℝ) = ∫⁻ x, ‖Gf f x‖ₑ ^ (2:ℝ) :=
        lintegral_fourierInv_enorm_sq (memLp_Gf hF1) (memLp_Gf hF2)
      rw [hGF]
      calc ∫⁻ x, ‖Gf f x‖ₑ ^ (2:ℝ) ≤ ∫⁻ x, ‖𝓕 f x‖ₑ ^ (2:ℝ) := by
            refine lintegral_mono fun x => ENNReal.rpow_le_rpow ?_ (by norm_num)
            rw [show Gf f x = IicInd x * 𝓕 f x from rfl, enorm_mul]
            have h2 : ‖IicInd x‖ₑ ≤ 1 := by
              rw [enorm_eq_ofReal_norm]
              calc ENNReal.ofReal ‖IicInd x‖ ≤ ENNReal.ofReal 1 :=
                    ENNReal.ofReal_le_ofReal (norm_IicInd_le x)
                _ = 1 := ENNReal.ofReal_one
            calc ‖IicInd x‖ₑ * ‖𝓕 f x‖ₑ ≤ 1 * ‖𝓕 f x‖ₑ := by
                  gcongr
              _ = ‖𝓕 f x‖ₑ := one_mul _
        _ = ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
            rw [← lintegral_fourierInv_enorm_sq hF1 hF2]
            apply lintegral_congr; intro x
            rw [hinv x]
    calc ∫⁻ x, (Smax f x) ^ (2:ℝ) ≤ ∫⁻ x, (hlMax (fun y => ‖Ginv f y‖ₑ) x) ^ (2:ℝ) := h1
      _ ≤ ENNReal.ofReal (Chl^2) * ∫⁻ x, ‖Ginv f x‖ₑ ^ (2:ℝ) := h2
      _ ≤ ENNReal.ofReal (Chl^2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by gcongr
  have hb : ∫⁻ x, (Bmax f x) ^ (2:ℝ) ≤ ENNReal.ofReal 100 * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
    rw [show (fun x => (Bmax f x) ^ (2:ℝ))
        = fun x => (⨆ j : ℕ, ‖FI (Bfun j f) x‖ₑ) ^ (2:ℝ) from rfl]
    exact boundary_bound hf2 hF1 hF2 hFm hinv
  have hCsq : (2*Real.pi*2*Real.sqrt (Chl^2 + 100))^2 = (2*Real.pi)^2 * 4 * (Chl^2 + 100) := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ Chl^2 + 100)]
    ring
  have h1 : ENNReal.ofReal (Chl^2) + ENNReal.ofReal 100 = ENNReal.ofReal (Chl^2 + 100) :=
    (ENNReal.ofReal_add (sq_nonneg Chl) (by norm_num : (0:ℝ) ≤ 100)).symm
  have h2 : ENNReal.ofReal ((2*Real.pi)^2 * 4) * ENNReal.ofReal (Chl^2 + 100)
      = ENNReal.ofReal ((2*Real.pi)^2 * 4 * (Chl^2 + 100)) :=
    (ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2*Real.pi)^2 * 4)).symm
  calc ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
        (∫ θ in (0:ℝ)..(hj j), Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ)
      ≤ ENNReal.ofReal ((2*Real.pi)^2 * 4)
          * ((∫⁻ x, (Smax f x) ^ (2:ℝ)) + (∫⁻ x, (Bmax f x) ^ (2:ℝ))) := hd
    _ ≤ ENNReal.ofReal ((2*Real.pi)^2 * 4)
          * ((ENNReal.ofReal (Chl^2) + ENNReal.ofReal 100)
            * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ))) := by
        gcongr
        calc (∫⁻ x, (Smax f x) ^ (2:ℝ)) + (∫⁻ x, (Bmax f x) ^ (2:ℝ))
            ≤ ENNReal.ofReal (Chl^2) * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ))
              + ENNReal.ofReal 100 * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := add_le_add he hb
          _ = (ENNReal.ofReal (Chl^2) + ENNReal.ofReal 100)
                * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := by ring
    _ = (ENNReal.ofReal ((2*Real.pi)^2 * 4) * ENNReal.ofReal (Chl^2 + 100))
          * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := by
        rw [h1, mul_assoc]
    _ = ENNReal.ofReal ((2*Real.pi)^2 * 4 * (Chl^2 + 100)) * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := by
        rw [h2]
    _ = ENNReal.ofReal ((2*Real.pi*2*Real.sqrt (Chl^2 + 100))^2) * (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ)) := by
        rw [hCsq]


/-! ## The Dirichlet-type kernels and the passage to general `L²` functions -/

lemma norm_exp_neg_I_mul (t : ℝ) : ‖Complex.exp (-((↑t : ℂ) * Complex.I))‖ = 1 := by
  rw [show -((↑t : ℂ) * Complex.I) = ((↑(-t)) : ℂ) * Complex.I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

lemma norm_integral_exp_neg_I_le (T : ℝ) :
    ‖∫ u in (0:ℝ)..T, Complex.exp (-(Complex.I * (u:ℂ)))‖ ≤ 2 := by
  have hderiv : ∀ u ∈ Set.uIcc (0:ℝ) T,
      HasDerivAt (fun u : ℝ => Complex.I * Complex.exp (-(Complex.I * (u:ℂ))))
        (Complex.exp (-(Complex.I * (u:ℂ)))) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => (u:ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun u : ℝ => -(Complex.I * (u:ℂ))) (-Complex.I) u := by
      have h3 : HasDerivAt (fun u : ℝ => (Complex.I : ℂ) * (u:ℂ)) Complex.I u := by
        have hh3 := h1.const_mul Complex.I
        simpa using hh3
      exact h3.neg
    have h4 := h2.cexp.const_mul Complex.I
    have hderiv' : Complex.I * (Complex.exp (-(Complex.I * (u:ℂ))) * (-Complex.I))
        = Complex.exp (-(Complex.I * (u:ℂ))) := by
      rw [show Complex.I * (Complex.exp (-(Complex.I * (u:ℂ))) * (-Complex.I))
          = (-(Complex.I * Complex.I)) * Complex.exp (-(Complex.I * (u:ℂ))) by ring,
        Complex.I_mul_I]
      ring
    simpa only [hderiv'] using h4
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by fun_prop : Continuous (fun u : ℝ => Complex.exp (-(Complex.I * (u:ℂ))))).intervalIntegrable _ _)]
  have heq : Complex.I * Complex.exp (-(Complex.I * (T:ℂ)))
        - Complex.I * Complex.exp (-(Complex.I * ((0:ℝ):ℂ)))
      = Complex.I * (Complex.exp (-(Complex.I * (T:ℂ))) - 1) := by
    rw [show -(Complex.I * ((0:ℝ):ℂ)) = 0 by simp, Complex.exp_zero]
    ring
  rw [heq, norm_mul, show ‖(Complex.I : ℂ)‖ = 1 by simp, one_mul]
  calc ‖Complex.exp (-(Complex.I * (T:ℂ))) - 1‖
      ≤ ‖Complex.exp (-(Complex.I * (T:ℂ)))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
        rw [show -(Complex.I * (T:ℂ)) = -((↑T : ℂ) * Complex.I) by ring,
          norm_exp_neg_I_mul, norm_one]; norm_num

lemma dirichlet_bound_h {h : ℝ} (hh : 0 < h) (z : ℝ) :
    ‖∫ θ in (0:ℝ)..h, Complex.exp (-(Complex.I * (z:ℂ) * (θ:ℂ)))‖ ≤ h := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := h) (C := 1)
    (f := fun θ : ℝ => Complex.exp (-(Complex.I * (z:ℂ) * (θ:ℂ)))) ?_
  · simpa [sub_zero, one_mul, abs_of_pos hh] using this
  · intro θ _
    rw [show -(Complex.I * (z:ℂ) * (θ:ℂ)) = ((↑(-(z*θ)) : ℂ) * Complex.I) by push_cast; ring,
      norm_exp_ofReal_mul_I]

lemma dirichlet_bound_inv {h : ℝ} (hh : 0 < h) {z : ℝ} (hz : z ≠ 0) :
    ‖∫ θ in (0:ℝ)..h, Complex.exp (-(Complex.I * (z:ℂ) * (θ:ℂ)))‖ ≤ 2/|z| := by
  have hsub : (∫ θ in (0:ℝ)..h, Complex.exp (-(Complex.I * (z:ℂ) * (θ:ℂ))))
      = (z:ℂ)⁻¹ * ∫ u in (0:ℝ)..(z * h), Complex.exp (-(Complex.I * (u:ℂ))) := by
    rw [show (∫ θ in (0:ℝ)..h, Complex.exp (-(Complex.I * (z:ℂ) * (θ:ℂ))))
        = ∫ θ in (0:ℝ)..h,
            (fun u : ℝ => Complex.exp (-(Complex.I * (u:ℂ)))) (z * θ) from by
        apply intervalIntegral.integral_congr; intro θ _
        push_cast; ring_nf,
      intervalIntegral.integral_comp_mul_left (fun u : ℝ => Complex.exp (-(Complex.I * (u:ℂ)))) hz]
    rw [show (z:ℝ) * 0 = 0 by ring]
    simp only [Complex.real_smul, Complex.ofReal_inv]
  rw [hsub, norm_mul,
    show ((z:ℂ))⁻¹ = (((z⁻¹ : ℝ)) : ℂ) from (Complex.ofReal_inv z).symm,
    norm_ofReal_eq_abs, abs_inv, inv_eq_one_div]
  calc (1 / |z|) * ‖∫ u in (0:ℝ)..(z*h), Complex.exp (-(Complex.I * (u:ℂ)))‖
      ≤ (1 / |z|) * 2 := by
        gcongr
        exact norm_integral_exp_neg_I_le _
    _ = 2/|z| := by ring_nf

theorem dirichlet_kernel_l2 (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) :
    MemLp (fun z : ℝ => ∫ θ in (0:ℝ)..h, Complex.exp (-(Complex.I * (z:ℂ) * (θ:ℂ)))) 2 volume ∧
      (eLpNorm (fun z : ℝ => ∫ θ in (0:ℝ)..h, Complex.exp (-(Complex.I * (z:ℂ) * (θ:ℂ))))
        2 volume).toReal ≤ 6 := by
  set K : ℝ → ℂ := fun z => ∫ θ in (0:ℝ)..h, Complex.exp (-(Complex.I * (z:ℂ) * (θ:ℂ))) with hK
  have hcont : Continuous K := by
    rw [hK]
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) ?_ 0 h
    exact Complex.continuous_exp.comp (by fun_prop)
  have hsq : ∀ z : ℝ, ‖K z‖ ^ 2 ≤ 8/(1+z^2) := by
    intro z
    by_cases hz : z = 0
    · subst hz
      have h1 : ‖K 0‖ ≤ 1 := by
        rw [hK]; exact (dirichlet_bound_h hh 0).trans hh1
      have h2 : (1:ℝ) ≤ 8/(1+0^2) := by norm_num
      nlinarith [norm_nonneg (K 0), h1, sq_nonneg ‖K 0‖]
    · by_cases hz2 : |z| ≤ 2
      · have h1 : ‖K z‖ ≤ 1 := by
          rw [hK]; exact (dirichlet_bound_h hh z).trans hh1
        have h2 : (1:ℝ) ≤ 8/(1+z^2) := by
          rw [le_div_iff₀ (by positivity)]
          nlinarith [hz2, abs_nonneg z, sq_abs z, sq_nonneg z]
        nlinarith [norm_nonneg (K z), h1, h2, sq_nonneg ‖K z‖]
      · push Not at hz2
        have h2 : ‖K z‖ ≤ 2/|z| := by rw [hK]; exact dirichlet_bound_inv hh hz
        have hkey : (2/|z|)^2 ≤ 8/(1+z^2) := by
          rw [div_pow, sq_abs, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hz2, abs_nonneg z, sq_abs z, sq_nonneg z]
        nlinarith [norm_nonneg (K z), h2, hkey, sq_nonneg ‖K z‖]
  have hInt : Integrable (fun z : ℝ => (8:ℝ) * (1+z^2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul 8
  have hInt' : Integrable (fun z : ℝ => 8/(1+z^2)) volume := by
    convert hInt using 1
    funext z; rw [div_eq_mul_inv]
  have hKint : Integrable (fun z : ℝ => ‖K z‖ ^ 2) volume := by
    refine Integrable.mono' hInt' ((hcont.norm.pow 2).aestronglyMeasurable) ?_
    filter_upwards with z
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hsq z
  have hmem : MemLp K 2 volume :=
    (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr hKint
  refine ⟨by rw [hK]; exact hmem, ?_⟩
  have hbound : ∫⁻ z : ℝ, ‖K z‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal 32 := by
    calc ∫⁻ z : ℝ, ‖K z‖ₑ ^ (2:ℝ)
        = ∫⁻ z : ℝ, ENNReal.ofReal (‖K z‖^2) := by
          apply lintegral_congr; intro z
          rw [enorm_eq_ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
            Real.rpow_two]
      _ ≤ ∫⁻ z : ℝ, ENNReal.ofReal (8/(1+z^2)) := by
          refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hsq z)
      _ = ENNReal.ofReal (∫ z : ℝ, 8/(1+z^2)) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt'
            (Filter.Eventually.of_forall fun z => by positivity)).symm
      _ = ENNReal.ofReal (8 * Real.pi) := by
          congr 1
          rw [show (∫ z : ℝ, 8/(1+z^2)) = 8 * ∫ z : ℝ, (1+z^2)⁻¹ by
            rw [← MeasureTheory.integral_const_mul]
            congr 1]
          rw [integral_univ_inv_one_add_sq]
      _ ≤ ENNReal.ofReal 32 := ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_lt_four])
  have hlin : (eLpNorm K 2 volume) ^ (2:ℝ) = ∫⁻ z : ℝ, ‖K z‖ₑ ^ (2:ℝ) := by
    have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (f := K) (μ := volume)
      (p := (2:NNReal)) (by norm_num) hcont.aestronglyMeasurable
    simpa using h
  have hfin : eLpNorm K 2 volume ≤ ENNReal.ofReal 6 := by
    rw [← ENNReal.rpow_le_rpow_iff (show (0:ℝ) < 2 by norm_num), hlin]
    calc ∫⁻ z : ℝ, ‖K z‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal 32 := hbound
      _ ≤ ENNReal.ofReal 36 := ENNReal.ofReal_le_ofReal (by norm_num)
      _ = (ENNReal.ofReal 6) ^ (2:ℝ) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num), Real.rpow_two]
          norm_num
  rw [hK]
  exact ENNReal.toReal_le_of_le_ofReal (by norm_num) hfin


/-! ## The kernels attached to the scales -/

/-- The Dirichlet-type kernel of the `j`-th scale: `K_j z = ∫_0^{h_j} e^{-i z θ} dθ`. -/
def Kj (j : ℕ) (z : ℝ) : ℂ :=
  ∫ θ in (0:ℝ)..(hj j), Complex.exp (-(Complex.I * (z : ℂ) * (θ : ℂ)))

lemma hj_le_one (j : ℕ) : hj j ≤ 1 := by
  have h1 : (2:ℝ) ^ (-(j:ℝ)-1) ≤ (2:ℝ) ^ (0:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show (-(j:ℝ)-1) ≤ 0 by
        rw [show (-(j:ℝ)-1) = -((j:ℝ)+1) by ring]
        exact neg_nonpos.mpr (by positivity))
  simpa [hj, Real.rpow_zero] using h1

lemma Kj_lambda (j : ℕ) :
    (fun z : ℝ => ∫ θ in (0:ℝ)..(hj j), Complex.exp (-(Complex.I * (z:ℂ) * (θ:ℂ)))) = Kj j := by
  funext z; simp only [Kj]

lemma memLp_Kj (j : ℕ) : MemLp (Kj j) 2 volume := by
  have h := (dirichlet_kernel_l2 (hj j) (hj_pos j) (hj_le_one j)).1
  rwa [Kj_lambda j] at h

lemma eLpNorm_Kj_le (j : ℕ) : (eLpNorm (Kj j) 2 volume).toReal ≤ 6 := by
  have h := (dirichlet_kernel_l2 (hj j) (hj_pos j) (hj_le_one j)).2
  rwa [Kj_lambda j] at h

/-! ## Auxiliary lemmas -/

lemma eLpNorm_coeFn_Lp_two (L : Lp ℂ 2 (volume : Measure ℝ)) :
    eLpNorm (L : ℝ → ℂ) 2 volume = ENNReal.ofReal ‖L‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top L)]

lemma iSup_mul_self_le (b : ℕ → ENNReal) :
    (⨆ n, b n) * (⨆ n, b n) ≤ ⨆ n, b n * b n := by
  rw [ENNReal.mul_iSup]
  simp_rw [ENNReal.iSup_mul]
  refine iSup_le fun k => iSup_le fun j => ?_
  rcases le_total (b j) (b k) with h | h
  · calc b j * b k ≤ b k * b k := by gcongr
      _ ≤ ⨆ n, b n * b n := le_iSup (fun n => b n * b n) k
  · calc b j * b k ≤ b j * b j := by gcongr
      _ ≤ ⨆ n, b n * b n := le_iSup (fun n => b n * b n) j

lemma iInf_mul_self_le {ι : Type*} (b : ι → ENNReal) :
    (⨅ i, b i) * (⨅ i, b i) ≤ ⨅ i, b i * b i :=
  le_iInf fun i => mul_le_mul' (iInf_le b i) (iInf_le b i)

lemma liminf_rpow_two_le (a : ℕ → ENNReal) :
    (Filter.liminf a atTop) ^ (2:ℝ) ≤ Filter.liminf (fun n => (a n) ^ (2:ℝ)) atTop := by
  have key : ∀ x : ENNReal, x ^ (2:ℝ) = x * x := by
    intro x; rw [ENNReal.rpow_two, pow_two]
  simp only [key]
  rw [Filter.liminf_eq_iSup_iInf_of_nat, Filter.liminf_eq_iSup_iInf_of_nat]
  calc (⨆ n, ⨅ i, ⨅ (_ : i ≥ n), a i) * (⨆ n, ⨅ i, ⨅ (_ : i ≥ n), a i)
      ≤ ⨆ n, (⨅ i, ⨅ (_ : i ≥ n), a i) * (⨅ i, ⨅ (_ : i ≥ n), a i) :=
        iSup_mul_self_le _
    _ ≤ ⨆ n, ⨅ i, ⨅ (_ : i ≥ n), a i * a i := by
        refine iSup_le fun n => ?_
        refine (iInf_mul_self_le (fun i => ⨅ (_ : i ≥ n), a i)).trans ?_
        refine le_trans ?_ (le_iSup (fun n => ⨅ i, ⨅ (_ : i ≥ n), a i * a i) n)
        refine le_iInf fun (i : ℕ) => ?_
        refine le_iInf fun (hi : i ≥ n) => ?_
        exact (iInf_le (fun i => (⨅ (_ : i ≥ n), a i) * (⨅ (_ : i ≥ n), a i)) i).trans
          (mul_le_mul' (iInf_le _ hi) (iInf_le _ hi))

lemma eLpNorm_sub_left_eq (g : ℝ → ℂ) (x : ℝ) :
    eLpNorm (fun y : ℝ => g (x - y)) 2 volume = eLpNorm g 2 volume := by
  have h2 : (2:ℝ≥0∞) ≠ 0 := by norm_num
  have h2' : (2:ℝ≥0∞) ≠ ⊤ := by norm_num
  by_cases hg : AEStronglyMeasurable g volume
  swap
  · have hgx : ¬ AEStronglyMeasurable (fun y : ℝ => g (x - y)) volume := by
      intro h
      apply hg
      have h3 := h.comp_measurePreserving (Measure.measurePreserving_sub_left (volume : Measure ℝ) x)
      refine h3.congr (Filter.Eventually.of_forall fun z => ?_)
      simp
    rw [eLpNorm_of_not_aestronglyMeasurable hg, eLpNorm_of_not_aestronglyMeasurable hgx]
  have hgx : AEStronglyMeasurable (fun y : ℝ => g (x - y)) volume :=
    hg.comp_measurePreserving (Measure.measurePreserving_sub_left (volume : Measure ℝ) x)
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2' hgx,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal h2 h2' hg]
  rw [MeasureTheory.lintegral_sub_left_eq_self (G := ℝ) (μ := volume)
    (fun z : ℝ => ‖g z‖ₑ ^ ((2:ℝ≥0∞).toReal)) x]

lemma integral_norm_sq_eq (g : ℝ → ℂ) (hg : MemLp g 2 volume) :
    ∫ y : ℝ, ‖g y‖ ^ (2:ℝ) = ((eLpNorm g 2 volume).toReal) ^ 2 := by
  have hInt : Integrable (fun y : ℝ => ‖g y‖ ^ 2) volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have h1 : ∫ y : ℝ, ‖g y‖ ^ 2 = (∫⁻ y : ℝ, ‖g y‖ₑ ^ (2:ℝ)).toReal := by
    have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall fun y => sq_nonneg ‖g y‖)
    have h2' : ∫⁻ y : ℝ, ENNReal.ofReal (‖g y‖ ^ 2) = ∫⁻ y : ℝ, ‖g y‖ₑ ^ (2:ℝ) := by
      apply lintegral_congr; intro y
      rw [enorm_eq_ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        Real.rpow_two]
    rw [h2'] at h
    rw [← h, ENNReal.toReal_ofReal (integral_nonneg fun y => sq_nonneg ‖g y‖)]
  have h2 : ∫⁻ y : ℝ, ‖g y‖ₑ ^ (2:ℝ) = (eLpNorm g 2 volume) ^ (2:ℝ) := by
    simpa using (MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := volume)
      (p := (2:NNReal)) (by norm_num) hg.aestronglyMeasurable).symm
  rw [show (∫ y : ℝ, ‖g y‖ ^ (2:ℝ)) = ∫ y : ℝ, ‖g y‖ ^ 2 from by
      congr 1; funext y; rw [Real.rpow_two],
    h1, h2, ← ENNReal.toReal_rpow, Real.rpow_two]

lemma norm_integral_mul_le_eLpNorm (g K : ℝ → ℂ) (hg : MemLp g 2 volume)
    (hK : MemLp K 2 volume) (x : ℝ) :
    ‖∫ y : ℝ, g y * K (x - y)‖
      ≤ (eLpNorm g 2 volume).toReal * (eLpNorm K 2 volume).toReal := by
  have hKx : MemLp (fun y : ℝ => K (x - y)) 2 volume := by
    rw [memLp_iff, eLpNorm_sub_left_eq K x]; exact hK.eLpNorm_lt_top
  have h1 : ‖∫ y : ℝ, g y * K (x - y)‖
      ≤ (∫ y : ℝ, ‖g y‖ ^ (2:ℝ)) ^ (1/(2:ℝ))
          * (∫ y : ℝ, ‖K (x - y)‖ ^ (2:ℝ)) ^ (1/(2:ℝ)) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [show (∫ y : ℝ, ‖g y * K (x - y)‖) = ∫ y : ℝ, ‖g y‖ * ‖K (x - y)‖ from
      integral_congr_ae (Filter.Eventually.of_forall fun y => norm_mul _ _)]
    exact MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
      Real.HolderConjugate.two_two (by simpa using hg) (by simpa using hKx)
  rw [integral_norm_sq_eq g hg, integral_norm_sq_eq (fun y : ℝ => K (x - y)) hKx,
    eLpNorm_sub_left_eq K x] at h1
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (by positivity : (0:ℝ) ≤ (eLpNorm g 2 volume).toReal),
    Real.sqrt_sq (by positivity : (0:ℝ) ≤ (eLpNorm K 2 volume).toReal)] at h1
  exact h1

-- =====================================================================================
-- REMAINING PIECES (see the strategy comment at the top of the file):
--
--  * `smooth_shell_le_maximal` : for `g : ℝ → ℂ`, `j : ℕ`, `x : ℝ`,
--      `|(1/2π) ∫ y, sig j y * g (x - y)| ≤ C * (⨆ (a b : ℝ) (_ : a ≤ x ∧ x ≤ b),
--          ENNReal.ofReal (b-a)⁻¹ * ∫⁻ y in Set.Icc a b, ‖g y‖ₑ)`
--    (elementary shell estimate; `sig j / 2π` is an approximate identity at scale `1/aj j`).
--
--  * `boundary_tsum_le` : for `f` Schwartz,
--      `∑' j, ∫⁻ x, ‖𝓕⁻ (fun ξ => bj j ξ * 𝓕 f ξ) x‖ₑ^2 ≤ C * ∫⁻ x, ‖f x‖ₑ^2`
--    (Plancherel `lintegral_fourierInv_eq` + `geometric_gaussian_complement_tsum_le`).
--
--  * `main_schwartz` : the target inequality for Schwartz `f`, assembling the previous two
--    with `sharp_identity`, `sig_fourier`, `real_maximal_strong_type 2`.
--
--  * `main_theorem` : the stated theorem, via Fatou (`⨆_j ‖T_j f_n x‖ → ⨆_j ‖T_j f x‖`
--    pointwise for `f_n` Schwartz, `f_n → f` in `L²`).
-- =====================================================================================


/-! ## The passage from Schwartz functions to general `L²` functions

For `f ∈ L²` we approximate by Schwartz functions `ψ_n → f` in `L²`.  For a Schwartz function the
level operators are continuous convolutions with the Dirichlet-type kernels `K_j`, so the sup over
the scales is measurable, and Fatou's lemma gives the estimate for `f`. -/

lemma lintegral_enorm_rpow_two_eq (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume) :
    ∫⁻ x, ‖g x‖ₑ ^ (2:ℝ) = (eLpNorm g 2 volume) ^ (2:ℝ) := by
  simpa using (MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := volume)
    (p := (2:NNReal)) (by norm_num) hg).symm

/-- Schwartz functions have integrable Fourier transform. -/
lemma integrable_fourier_schwartz (ψ : SchwartzMap ℝ ℂ) : Integrable (𝓕 (ψ : ℝ → ℂ)) volume := by
  have h : Integrable ((𝓕 ψ : SchwartzMap ℝ ℂ) : ℝ → ℂ) volume := SchwartzMap.integrable (𝓕 ψ)
  rwa [SchwartzMap.fourier_coe ψ] at h

/-- The translate of the Dirichlet-type kernel is in `L²`. -/
lemma memLp_Kj_sub (j : ℕ) (x : ℝ) : MemLp (fun y : ℝ => Kj j (x - y)) 2 volume :=
  by rw [memLp_iff, eLpNorm_sub_left_eq (Kj j) x]; exact (memLp_Kj j).eLpNorm_lt_top

/-- For a Schwartz function the level operators are continuous convolutions. -/
lemma continuous_conv_Kj (ψ : SchwartzMap ℝ ℂ) (j : ℕ) :
    Continuous (fun x : ℝ => ∫ y, (ψ : ℝ → ℂ) y * Kj j (x - y)) := by
  have hF : Integrable (𝓕 (ψ : ℝ → ℂ)) volume := integrable_fourier_schwartz ψ
  have hh : Integrable (fun ξ : ℝ => IccInd (-(aj j)) ξ * 𝓕 (ψ : ℝ → ℂ) ξ) volume :=
    integrable_mul_of_norm_le (measurable_IccInd _) zero_le_one (fun ξ => norm_IccInd_le _ ξ) hF
  have hfun : (fun x : ℝ => FI (fun ξ : ℝ => IccInd (-(aj j)) ξ * 𝓕 (ψ : ℝ → ℂ) ξ) x)
      = 𝓕⁻ (fun ξ : ℝ => IccInd (-(aj j)) ξ * 𝓕 (ψ : ℝ → ℂ) ξ) := by
    funext x
    exact FI_eq_fourierInv _ x
  have hcont : Continuous
      (fun x : ℝ => FI (fun ξ : ℝ => IccInd (-(aj j)) ξ * 𝓕 (ψ : ℝ → ℂ) ξ) x) := by
    rw [hfun]
    exact continuous_fourierInv_of_integrable hh
  have hconv : (fun x : ℝ => ∫ y, (ψ : ℝ → ℂ) y * Kj j (x - y))
      = fun x : ℝ => 2 * Real.pi * FI (fun ξ : ℝ => IccInd (-(aj j)) ξ * 𝓕 (ψ : ℝ → ℂ) ξ) x := by
    funext x
    simpa only [Kj] using sharp_identity' (SchwartzMap.memLp ψ 1 volume)
      (SchwartzMap.memLp ψ 2 volume) j x
  rw [hconv]
  exact continuous_const.mul hcont

lemma continuous_enorm_conv_Kj (ψ : SchwartzMap ℝ ℂ) (j : ℕ) :
    Continuous (fun x : ℝ => ‖∫ y, (ψ : ℝ → ℂ) y * Kj j (x - y)‖ₑ) :=
  continuous_enorm.comp (continuous_conv_Kj ψ j)

lemma measurable_sup_conv_Kj (ψ : SchwartzMap ℝ ℂ) :
    Measurable (fun x : ℝ => (⨆ j : ℕ, ‖∫ y, (ψ : ℝ → ℂ) y * Kj j (x - y)‖ₑ) ^ (2:ℝ)) :=
  (ENNReal.continuous_rpow_const (y := (2:ℝ))).measurable.comp
    (Measurable.iSup fun j => (continuous_enorm_conv_Kj ψ j).measurable)

/-- The `L²` distance of a Schwartz function to `f`, expressed through the `Lp` classes. -/
lemma eLpNorm_sub_schwartz (ψ : SchwartzMap ℝ ℂ) (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    eLpNorm (fun y : ℝ => f y - (ψ : ℝ → ℂ) y) 2 volume
      = ENNReal.ofReal ‖hf.toLp f - SchwartzMap.toLpCLM ℝ ℂ 2 volume ψ‖ := by
  have hae : ((hf.toLp f - SchwartzMap.toLpCLM ℝ ℂ 2 volume ψ : Lp ℂ 2 volume) : ℝ → ℂ)
      =ᵐ[volume] fun y : ℝ => f y - (ψ : ℝ → ℂ) y := by
    have h3 : ((SchwartzMap.toLpCLM ℝ ℂ 2 volume ψ : Lp ℂ 2 volume) : ℝ → ℂ)
        =ᵐ[volume] (ψ : ℝ → ℂ) := SchwartzMap.coeFn_toLp ψ 2 volume
    filter_upwards [Lp.coeFn_sub (hf.toLp f) (SchwartzMap.toLpCLM ℝ ℂ 2 volume ψ),
      hf.coeFn_toLp, h3] with y h1 h2 h4
    rw [h1, Pi.sub_apply, h2, h4]
  rw [← eLpNorm_congr_ae hae, eLpNorm_coeFn_Lp_two]

/-- **The maximal estimate for general `L²` functions.** -/
lemma main_l2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℂ) (hf : MemLp f 2 volume),
      ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y * Kj j (x - y)‖ₑ) ^ (2:ℝ)
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := schwartz_case
  refine ⟨C, hCpos, ?_⟩
  intro f hf
  -- Schwartz approximation
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) :=
    SchwartzMap.denseRange_toLpCLM (p := 2) (by norm_num) (μ := volume)
  choose ψ hψ using fun n : ℕ =>
    hdense.exists_dist_lt (hf.toLp f) (by positivity : (0:ℝ) < 1 / ((n:ℝ) + 1))
  have hψδ : ∀ n : ℕ,
      ‖hf.toLp f - SchwartzMap.toLpCLM ℝ ℂ 2 volume (ψ n)‖ < 1 / ((n:ℝ) + 1) := by
    intro n
    rw [← dist_eq_norm]
    exact hψ n
  have hψtend : Tendsto (fun n : ℕ => SchwartzMap.toLpCLM ℝ ℂ 2 volume (ψ n)) atTop
      (nhds (hf.toLp f)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero
      (f := fun n : ℕ => ‖SchwartzMap.toLpCLM ℝ ℂ 2 volume (ψ n) - hf.toLp f‖)
      (g := fun n : ℕ => 1 / ((n:ℝ) + 1)) (fun n => norm_nonneg _) (fun n => ?_) ?_
    · rw [norm_sub_rev]
      exact (hψδ n).le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- the error terms tend to zero
  have he : Tendsto
      (fun n : ℕ => ENNReal.ofReal (6 * ‖hf.toLp f - SchwartzMap.toLpCLM ℝ ℂ 2 volume (ψ n)‖))
      atTop (nhds 0) := by
    have h0 : Tendsto
        (fun n : ℕ => ‖hf.toLp f - SchwartzMap.toLpCLM ℝ ℂ 2 volume (ψ n)‖) atTop (nhds 0) := by
      have h := ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => hf.toLp f) atTop (nhds (hf.toLp f))).sub hψtend).norm
      simpa using h
    have h6 := h0.const_mul 6
    have h7 := ENNReal.tendsto_ofReal h6
    simpa using h7
  -- pointwise comparison with an approximant
  have hle : ∀ (n : ℕ) (x : ℝ),
      (⨆ j : ℕ, ‖∫ y : ℝ, f y * Kj j (x - y)‖ₑ)
        ≤ (⨆ j : ℕ, ‖∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj j (x - y)‖ₑ)
          + ENNReal.ofReal (6 * ‖hf.toLp f - SchwartzMap.toLpCLM ℝ ℂ 2 volume (ψ n)‖) := by
    intro n x
    refine iSup_le fun j => ?_
    have hKx := memLp_Kj_sub j x
    have hψ2 : MemLp (ψ n : ℝ → ℂ) 2 volume := SchwartzMap.memLp (ψ n) 2 volume
    haveI : ENNReal.HolderTriple (2:ℝ≥0∞) (2:ℝ≥0∞) 1 :=
      ⟨by rw [inv_one, ENNReal.inv_two_add_inv_two]⟩
    have hsi : Integrable (fun y : ℝ => (ψ n : ℝ → ℂ) y * Kj j (x - y)) volume :=
      hψ2.integrable_mul hKx
    have hdi : Integrable (fun y : ℝ => (f y - (ψ n : ℝ → ℂ) y) * Kj j (x - y)) volume :=
      (hf.sub hψ2).integrable_mul hKx
    have hsplit : ∫ y : ℝ, f y * Kj j (x - y)
        = (∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj j (x - y))
          + ∫ y : ℝ, (f y - (ψ n : ℝ → ℂ) y) * Kj j (x - y) := by
      rw [← integral_add hsi hdi]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      ring
    calc ‖∫ y : ℝ, f y * Kj j (x - y)‖ₑ
        = ‖(∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj j (x - y))
            + ∫ y : ℝ, (f y - (ψ n : ℝ → ℂ) y) * Kj j (x - y)‖ₑ := by rw [hsplit]
      _ ≤ ‖∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj j (x - y)‖ₑ
            + ‖∫ y : ℝ, (f y - (ψ n : ℝ → ℂ) y) * Kj j (x - y)‖ₑ := enorm_add_le _ _
      _ ≤ (⨆ j : ℕ, ‖∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj j (x - y)‖ₑ)
            + ENNReal.ofReal (6 * ‖hf.toLp f - SchwartzMap.toLpCLM ℝ ℂ 2 volume (ψ n)‖) := by
        gcongr
        · exact le_iSup (fun k => ‖∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj k (x - y)‖ₑ) j
        · rw [enorm_eq_ofReal_norm]
          refine ENNReal.ofReal_le_ofReal ?_
          calc ‖∫ y : ℝ, (f y - (ψ n : ℝ → ℂ) y) * Kj j (x - y)‖
              ≤ (eLpNorm (fun y : ℝ => f y - (ψ n : ℝ → ℂ) y) 2 volume).toReal
                  * (eLpNorm (Kj j) 2 volume).toReal :=
                norm_integral_mul_le_eLpNorm _ _ (hf.sub hψ2) (memLp_Kj j) x
            _ = ‖hf.toLp f - SchwartzMap.toLpCLM ℝ ℂ 2 volume (ψ n)‖
                  * (eLpNorm (Kj j) 2 volume).toReal := by
                rw [eLpNorm_sub_schwartz, ENNReal.toReal_ofReal (norm_nonneg _)]
            _ ≤ ‖hf.toLp f - SchwartzMap.toLpCLM ℝ ℂ 2 volume (ψ n)‖ * 6 := by
                gcongr
                exact eLpNorm_Kj_le j
            _ = 6 * ‖hf.toLp f - SchwartzMap.toLpCLM ℝ ℂ 2 volume (ψ n)‖ := by ring
  -- take the liminf
  have hkey : ∀ x : ℝ, (⨆ j : ℕ, ‖∫ y : ℝ, f y * Kj j (x - y)‖ₑ)
      ≤ Filter.liminf
          (fun n : ℕ => (⨆ j : ℕ, ‖∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj j (x - y)‖ₑ)) atTop := by
    intro x
    refine (le_iInf fun n => hle n x).trans ?_
    have h2 : (⨅ n : ℕ, ((⨆ j : ℕ, ‖∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj j (x - y)‖ₑ)
          + ENNReal.ofReal (6 * ‖hf.toLp f - SchwartzMap.toLpCLM ℝ ℂ 2 volume (ψ n)‖)))
        ≤ Filter.liminf
            (fun n : ℕ => (⨆ j : ℕ, ‖∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj j (x - y)‖ₑ)) atTop := by
      rw [← ENNReal.liminf_add_of_right_tendsto_zero he
        (fun n : ℕ => (⨆ j : ℕ, ‖∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj j (x - y)‖ₑ))]
      exact Filter.iInf_le_liminf
    exact h2
  have hpoint : ∀ x : ℝ, (⨆ j : ℕ, ‖∫ y : ℝ, f y * Kj j (x - y)‖ₑ) ^ (2:ℝ)
      ≤ Filter.liminf
          (fun n : ℕ => ((⨆ j : ℕ, ‖∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj j (x - y)‖ₑ)) ^ (2:ℝ))
          atTop := by
    intro x
    exact (ENNReal.rpow_le_rpow (hkey x) (by norm_num)).trans (liminf_rpow_two_le _)
  have hFatou : ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y * Kj j (x - y)‖ₑ) ^ (2:ℝ)
      ≤ Filter.liminf
          (fun n : ℕ => ∫⁻ x, ((⨆ j : ℕ, ‖∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj j (x - y)‖ₑ)) ^ (2:ℝ))
          atTop :=
    (lintegral_mono hpoint).trans (lintegral_liminf_le fun n => measurable_sup_conv_Kj (ψ n))
  -- apply the Schwartz case
  have hF1 : ∀ n : ℕ, MemLp (𝓕 (ψ n : ℝ → ℂ)) 1 volume := fun n => by
    have h := SchwartzMap.memLp (𝓕 (ψ n) : SchwartzMap ℝ ℂ) 1 volume
    rwa [SchwartzMap.fourier_coe (ψ n)] at h
  have hF2 : ∀ n : ℕ, MemLp (𝓕 (ψ n : ℝ → ℂ)) 2 volume := fun n => by
    have h := SchwartzMap.memLp (𝓕 (ψ n) : SchwartzMap ℝ ℂ) 2 volume
    rwa [SchwartzMap.fourier_coe (ψ n)] at h
  have hFm : ∀ n : ℕ, Measurable (𝓕 (ψ n : ℝ → ℂ)) := fun n =>
    (continuous_fourier_of_integrable (SchwartzMap.integrable (ψ n))).measurable
  have hinv : ∀ (n : ℕ) (x : ℝ), 𝓕⁻ (𝓕 (ψ n : ℝ → ℂ)) x = (ψ n : ℝ → ℂ) x := fun n x =>
    congrFun ((ψ n).continuous.fourierInv_fourier_eq (SchwartzMap.integrable (ψ n))
      (integrable_fourier_schwartz (ψ n))) x
  have hbnd : ∀ n : ℕ, ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj j (x - y)‖ₑ) ^ (2:ℝ)
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ x, ‖(ψ n : ℝ → ℂ) x‖ₑ ^ (2:ℝ) := fun n =>
    hC (ψ n) (SchwartzMap.memLp (ψ n) 1 volume) (SchwartzMap.memLp (ψ n) 2 volume)
      (hF1 n) (hF2 n) (hFm n) (hinv n)
  -- the `L²` norms of the approximants converge
  have hJeq : ∀ n : ℕ, ∫⁻ x, ‖(ψ n : ℝ → ℂ) x‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal (‖SchwartzMap.toLpCLM ℝ ℂ 2 volume (ψ n)‖ ^ 2) := by
    intro n
    rw [lintegral_enorm_rpow_two_eq _ (ψ n).continuous.aestronglyMeasurable,
      show eLpNorm (ψ n : ℝ → ℂ) 2 volume
          = ENNReal.ofReal ‖SchwartzMap.toLpCLM ℝ ℂ 2 volume (ψ n)‖ from
        (eLpNorm_congr_ae (SchwartzMap.coeFn_toLp (ψ n) 2 volume)).symm.trans
          (eLpNorm_coeFn_Lp_two _),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    rw [← Real.rpow_two]
  have hJ : ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖hf.toLp f‖ ^ 2) := by
    rw [lintegral_enorm_rpow_two_eq _ hf.aestronglyMeasurable,
      show eLpNorm f 2 volume = ENNReal.ofReal ‖hf.toLp f‖ from
        (eLpNorm_congr_ae hf.coeFn_toLp).symm.trans (eLpNorm_coeFn_Lp_two _),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    rw [← Real.rpow_two]
  have hJn : Tendsto (fun n : ℕ => ∫⁻ x, ‖(ψ n : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) atTop
      (nhds (∫⁻ x, ‖f x‖ₑ ^ (2:ℝ))) := by
    simp only [hJeq, hJ]
    exact ENNReal.tendsto_ofReal (hψtend.norm.pow 2)
  have hlim : Filter.liminf
        (fun n : ℕ => ENNReal.ofReal (C ^ 2) * ∫⁻ x, ‖(ψ n : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) atTop
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := by
    have h : Tendsto
        (fun n : ℕ => ENNReal.ofReal (C ^ 2) * ∫⁻ x, ‖(ψ n : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) atTop
        (nhds (ENNReal.ofReal (C ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ))) :=
      ((ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).tendsto _).comp hJn
    rw [Filter.Tendsto.liminf_eq h]
  calc ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y * Kj j (x - y)‖ₑ) ^ (2:ℝ)
      ≤ Filter.liminf
          (fun n : ℕ => ∫⁻ x, ((⨆ j : ℕ, ‖∫ y : ℝ, (ψ n : ℝ → ℂ) y * Kj j (x - y)‖ₑ)) ^ (2:ℝ))
          atTop := hFatou
    _ ≤ Filter.liminf
          (fun n : ℕ => ENNReal.ofReal (C ^ 2) * ∫⁻ x, ‖(ψ n : ℝ → ℂ) x‖ₑ ^ (2:ℝ)) atTop :=
        Filter.liminf_le_liminf (Filter.Eventually.of_forall hbnd)
    _ ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) := hlim
end OneSided

theorem one_sided_geometric_maximal_l2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume),
      ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
          (∫ θ in (0:ℝ)..((2:ℝ)^(-(j:ℝ)-1)),
            Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ)
        ∂MeasureTheory.volume
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.volume := by
  simpa only [OneSided.hj, OneSided.Kj] using OneSided.main_l2

end

end Commons.Analysis.Fourier
