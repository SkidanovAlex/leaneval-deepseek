import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.conv_l2_contraction

/-!
# The smoothing `f ↦ f̃ = T ψ(T·) * f` contracts the `L²` norm (GM §9)

`smoothed ψSmooth T f u = T ∫ ψ(T(u-u')) f(u') du'` is the convolution of `f` with the
nonnegative approximate identity `φ(t) = T ψ(T t)`, which has total mass `∫φ = 1`.  Hence
`‖f̃‖₂ ≤ ‖φ‖₁ ‖f‖₂ = ‖f‖₂` (Young's inequality for `L¹ * L² → L²`), which is what is proved here.

The proof reduces to the Jensen-based contraction `conv_l2_contraction` applied to `|f|` (so that
no positivity hypothesis on `f` is needed), together with the pointwise bound
`|f̃(u)| ≤ |f|~(u)` coming from `|∫ k f| ≤ ∫ k |f|` for a nonnegative kernel `k`.
-/

open MeasureTheory

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The smoothing kernel `φ(x) = T ψ(T x)` associated with the mollifier `smoothed ψ T`. -/
noncomputable def smoothKernel (T : ℝ) : ℝ → ℝ := fun x => T * psiSmooth (T * x)

lemma smoothKernel_nonneg (T : ℝ) (hT : 0 ≤ T) (x : ℝ) : 0 ≤ smoothKernel T x :=
  mul_nonneg hT (psiSmooth_nonneg (T * x))

lemma smoothKernel_continuous (T : ℝ) : Continuous (smoothKernel T) := by
  change Continuous (fun x : ℝ => T * psiSmooth (T * x))
  exact continuous_const.mul
    (psiSmooth_contDiff.continuous.comp (continuous_const.mul continuous_id))

/-- The kernel `T ψ(T·)` is supported in `[-1/T, 1/T]`. -/
lemma smoothKernel_support (T : ℝ) (hT : 0 < T) :
    Function.support (smoothKernel T) ⊆ Set.Icc (-(1 / T)) (1 / T) := by
  intro x hx
  have hx' : psiSmooth (T * x) ≠ 0 := by
    intro h
    apply hx
    change T * psiSmooth (T * x) = 0
    rw [h, mul_zero]
  have hmem : |T * x| ≤ 1 := by
    have h1 := psiSmooth_support hx'
    rw [Set.mem_Icc] at h1
    exact abs_le.mpr h1
  have hxabs : |x| ≤ 1 / T := by
    rw [abs_mul, abs_of_pos hT] at hmem
    rw [le_div_iff₀ hT, mul_comm]
    exact hmem
  exact abs_le.mp hxabs

lemma smoothKernel_hasCompactSupport (T : ℝ) (hT : 0 < T) : HasCompactSupport (smoothKernel T) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (smoothKernel_support T hT)

lemma smoothKernel_integrable (T : ℝ) (hT : 0 < T) : Integrable (smoothKernel T) :=
  (smoothKernel_continuous T).integrable_of_hasCompactSupport (smoothKernel_hasCompactSupport T hT)

/-- The kernel `T ψ(T·)` has total mass `1`. -/
lemma smoothKernel_integral (T : ℝ) (hT : 0 < T) : ∫ x, smoothKernel T x = 1 := by
  change ∫ x, T * psiSmooth (T * x) = 1
  rw [integral_const_mul, Measure.integral_comp_mul_left]
  simp only [psiSmooth_integral, smul_eq_mul, mul_one, abs_of_pos (inv_pos.mpr hT),
    mul_inv_cancel₀ hT.ne']

/-- `smoothed ψSmooth T g` is the convolution of `g` with the kernel `T ψSmooth (T ·)`. -/
lemma smoothed_eq_convolution (g : ℝ → ℝ) (T u : ℝ) :
    smoothed psiSmooth T g u
      = convolution (smoothKernel T) g (ContinuousLinearMap.lsmul ℝ ℝ) volume u := by
  rw [smoothed, convolution_lsmul_swap]
  simp only [smul_eq_mul]
  change T * ∫ (u' : ℝ), psiSmooth (T * (u - u')) * g u'
      = ∫ (t : ℝ), (T * psiSmooth (T * (u - t))) * g t
  rw [show (∫ t, (T * psiSmooth (T * (u - t))) * g t)
        = T * ∫ t, psiSmooth (T * (u - t)) * g t by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring]

lemma continuous_smoothed {T : ℝ} {g : ℝ → ℝ} (hg : Continuous g)
    (hgs : HasCompactSupport g) : Continuous (smoothed psiSmooth T g) := by
  rw [show smoothed psiSmooth T g = fun u => convolution (smoothKernel T) g
        (ContinuousLinearMap.lsmul ℝ ℝ) volume u
      from funext (fun u => smoothed_eq_convolution g T u)]
  exact HasCompactSupport.continuous_convolution_right (f := smoothKernel T) (g := g)
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hgs
    (smoothKernel_continuous T).locallyIntegrable hg

lemma hasCompactSupport_smoothed {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ}
    (hgs : HasCompactSupport g) : HasCompactSupport (smoothed psiSmooth T g) := by
  rw [show smoothed psiSmooth T g = fun u => convolution (smoothKernel T) g
        (ContinuousLinearMap.lsmul ℝ ℝ) volume u
      from funext (fun u => smoothed_eq_convolution g T u)]
  exact HasCompactSupport.convolution (f := smoothKernel T) (g := g)
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (smoothKernel_hasCompactSupport T hT) hgs

/-- The square of `smoothed ψSmooth T g` is integrable for continuous compactly supported `g`. -/
lemma integrable_smoothed_sq {T : ℝ} (hT : 0 < T) {g : ℝ → ℝ} (hg : Continuous g)
    (hgs : HasCompactSupport g) : Integrable (fun u => (smoothed psiSmooth T g u) ^ 2) :=
  ((continuous_smoothed hg hgs).pow 2).integrable_of_hasCompactSupport
    (by simpa only [pow_two] using (hasCompactSupport_smoothed (T := T) hT hgs).mul_right)

/-- The smoothed function `smoothed ψSmooth T (|f|)` is nonnegative. -/
lemma smoothed_abs_nonneg (T : ℝ) (hT : 0 < T) (g : ℝ → ℝ) (u : ℝ) :
    0 ≤ smoothed psiSmooth T (fun u => |g u|) u := by
  rw [smoothed]
  refine mul_nonneg hT.le (integral_nonneg fun t => ?_)
  exact mul_nonneg (psiSmooth_nonneg _) (abs_nonneg _)

/-- Pointwise: `|smoothed ψ T f u| ≤ smoothed ψ T |f| u` for a nonnegative kernel `ψ`. -/
lemma abs_smoothed_le_smoothed_abs (T : ℝ) (hT : 0 < T) (g : ℝ → ℝ) (u : ℝ) :
    |smoothed psiSmooth T g u| ≤ smoothed psiSmooth T (fun u => |g u|) u := by
  rw [smoothed, smoothed, abs_mul, abs_of_pos hT]
  refine mul_le_mul_of_nonneg_left ?_ hT.le
  calc |∫ (u' : ℝ), psiSmooth (T * (u - u')) * g u'|
      ≤ ∫ (u' : ℝ), |psiSmooth (T * (u - u')) * g u'| := abs_integral_le_integral_abs
    _ = ∫ (u' : ℝ), psiSmooth (T * (u - u')) * |g u'| := by
        apply integral_congr_ae
        filter_upwards with t
        rw [abs_mul, abs_of_nonneg (psiSmooth_nonneg _)]

theorem smoothed_L2_le {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hf : Continuous f)
    (hcs : HasCompactSupport f) :
    (∫ u, (smoothed psiSmooth T f u) ^ 2) ≤ ∫ u, (f u) ^ 2 := by
  have hcs_abs : HasCompactSupport (fun u : ℝ => |f u|) :=
    HasCompactSupport.of_support_subset_isCompact hcs.isCompact (fun x hx => subset_tsupport _
      (fun h => hx (by simp [h])))
  have hcs_abs2 : HasCompactSupport (fun u : ℝ => (|f u|) ^ 2) :=
    HasCompactSupport.of_support_subset_isCompact hcs_abs.isCompact (fun x hx => subset_tsupport _
      (fun h => hx (by simp [h])))
  -- Step 1: `(smoothed f)² ≤ (smoothed |f|)²` pointwise, hence for the integrals.
  have hmono : (∫ u, (smoothed psiSmooth T f u) ^ 2)
      ≤ ∫ u, (smoothed psiSmooth T (fun u => |f u|) u) ^ 2 := by
    apply integral_mono_ae (integrable_smoothed_sq hT hf hcs)
      (integrable_smoothed_sq hT hf.abs hcs_abs)
    filter_upwards with u
    rw [sq_le_sq, abs_of_nonneg (smoothed_abs_nonneg T hT f u)]
    exact abs_smoothed_le_smoothed_abs T hT f u
  -- Step 2: Young's inequality / Jensen for the nonnegative kernel, applied to `|f|`.
  have hfi : Integrable (fun u => |f u|) := hf.abs.integrable_of_hasCompactSupport hcs_abs
  have hfi2 : Integrable (fun u => (|f u|) ^ 2) :=
    (hf.abs.pow 2).integrable_of_hasCompactSupport hcs_abs2
  have hkey := conv_l2_contraction (φ := smoothKernel T) (f := fun u => |f u|)
    (smoothKernel_nonneg T hT.le) (smoothKernel_continuous T) (smoothKernel_hasCompactSupport T hT)
    (smoothKernel_integral T hT) (fun u => abs_nonneg _) hfi hfi2
  have hkey' : (∫ u, (smoothed psiSmooth T (fun u => |f u|) u) ^ 2) ≤ ∫ u, (f u) ^ 2 := by
    have h1 : (∫ u, (smoothed psiSmooth T (fun u => |f u|) u) ^ 2)
        = ∫ u, (convolution (smoothKernel T) (fun u => |f u|)
            (ContinuousLinearMap.lsmul ℝ ℝ) volume u) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with u
      rw [smoothed_eq_convolution]
    have h2 : (∫ u, (|f u|) ^ 2) = ∫ u, (f u) ^ 2 := by
      apply integral_congr_ae
      filter_upwards with u
      exact sq_abs (f u)
    rw [h1, ← h2]
    exact hkey
  exact le_trans hmono hkey'

end

end Work.GM.Affine
