import Mathlib.Analysis.Fourier.Convolution
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Row2.chat_conv` — the convolution theorem for `chat`

`Work.BoseFixR.chat W k = (kinFT (W : ℝ³ → ℂ) k).re = ∫_y W y · cos ⟪k,y⟫ dy` is the
cosine/real-Fourier transform of a one-body kernel.  This file proves that on `L¹(ℝ³)` the
cosine transform turns **convolution** into **multiplication** (whenever the second factor is
even, so that its transform is real), together with the two elementary companions: `L¹`-convolution
integrability, the `L¹`-norm bound `‖f⋆g‖₁ ≤ ‖f‖₁‖g‖₁`, and the support inclusion
`supp f, supp g ⊆ B(0,R) ⟹ supp (f⋆g) ⊆ B(0,2R)`.

Everything is phrased through Mathlib's `MeasureTheory.convolution` (`convolution_mul`,
`Integrable.integrable_convolution`, `integral_convolution`, `Real.fourier_smul_convolution_eq`)
and the corpus bridge `Work.SmallBoxBridge.Resolve.kinFT_eq_fourier`
(`kinFT u p = 𝓕 u ((2π)⁻¹ • p)`).
-/

noncomputable section

namespace Work.BoseRowsL.Row2

open MeasureTheory Metric

/-! ## 1. Integrability of the convolution -/

/-- The convolution integral of two `L¹` functions is integrable. -/
lemma chat_conv_integrable {f g : ℝ³ → ℝ} (hf : MeasureTheory.Integrable f)
    (hg : MeasureTheory.Integrable g) :
    MeasureTheory.Integrable (fun y : ℝ³ => ∫ x : ℝ³, f x * g (y - x)) := by
  refine (hf.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hg).congr ?_
  filter_upwards with y
  rw [MeasureTheory.convolution_mul]

/-! ## 2. The `L¹`-norm bound -/

/-- **Young's inequality for the `L¹`-convolution at `p = q = 1`**:
`∫ |f ⋆ g| ≤ (∫ |f|)(∫ |g|)`. -/
lemma chat_conv_abs_integral_le {f g : ℝ³ → ℝ} (hf : MeasureTheory.Integrable f)
    (hg : MeasureTheory.Integrable g) :
    (∫ y : ℝ³, |∫ x : ℝ³, f x * g (y - x)|)
      ≤ (∫ x : ℝ³, |f x|) * (∫ x : ℝ³, |g x|) := by
  have hF : MeasureTheory.Integrable (fun x : ℝ³ => |f x|) := hf.abs
  have hG : MeasureTheory.Integrable (fun x : ℝ³ => |g x|) := hg.abs
  have hkey : (∫ y : ℝ³, MeasureTheory.convolution (fun x : ℝ³ => |f x|) (fun x : ℝ³ => |g x|)
        (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume y)
      = (∫ x : ℝ³, |f x|) * (∫ x : ℝ³, |g x|) := by
    rw [MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hF hG]
    rfl
  calc (∫ y : ℝ³, |∫ x : ℝ³, f x * g (y - x)|)
      = ∫ y : ℝ³,
          |MeasureTheory.convolution f g (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume y| := by
        simp only [MeasureTheory.convolution_mul]
    _ ≤ ∫ y : ℝ³, MeasureTheory.convolution (fun x : ℝ³ => |f x|) (fun x : ℝ³ => |g x|)
          (ContinuousLinearMap.mul ℝ ℝ) MeasureTheory.volume y := by
        apply MeasureTheory.integral_mono
        · exact (hf.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hg).abs
        · exact hF.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hG
        · intro y
          have h := MeasureTheory.abs_integral_le_integral_abs
            (μ := MeasureTheory.volume) (f := fun t : ℝ³ => f t * g (y - t))
          simpa [MeasureTheory.convolution_mul, abs_mul] using h
    _ = (∫ x : ℝ³, |f x|) * (∫ x : ℝ³, |g x|) := hkey

/-! ## 3. The Fourier-side product identity -/

/-- **The Fourier transform of the convolution is the product of the transforms**, in the
corpus's `p`-convention (`kinFT`). -/
lemma kinFT_ofReal_convolution {f g : ℝ³ → ℝ} (hf : MeasureTheory.Integrable f)
    (hg : MeasureTheory.Integrable g) (k : ℝ³) :
    Submission.BoseGases.kinFT (fun y : ℝ³ => ((∫ x : ℝ³, f x * g (y - x) : ℝ) : ℂ)) k
      = Submission.BoseGases.kinFT (fun x : ℝ³ => ((f x : ℝ) : ℂ)) k
        * Submission.BoseGases.kinFT (fun x : ℝ³ => ((g x : ℝ) : ℂ)) k := by
  have hF : MeasureTheory.Integrable (fun x : ℝ³ => ((f x : ℝ) : ℂ)) := hf.ofReal
  have hG : MeasureTheory.Integrable (fun x : ℝ³ => ((g x : ℝ) : ℂ)) := hg.ofReal
  have hconv : (fun y : ℝ³ => ((∫ x : ℝ³, f x * g (y - x) : ℝ) : ℂ))
      = MeasureTheory.convolution (fun x : ℝ³ => ((f x : ℝ) : ℂ))
          (fun x : ℝ³ => ((g x : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℂ ℂ) MeasureTheory.volume := by
    funext y
    rw [MeasureTheory.convolution_lsmul]
    simp only [smul_eq_mul]
    have step : (∫ x : ℝ³, ((f x * g (y - x) : ℝ) : ℂ))
        = ∫ x : ℝ³, ((f x : ℝ) : ℂ) * ((g (y - x) : ℝ) : ℂ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact Complex.ofReal_mul _ _
    exact (integral_ofReal (𝕜 := ℂ) (f := fun x : ℝ³ => f x * g (y - x))).symm.trans step
  calc Submission.BoseGases.kinFT (fun y : ℝ³ => ((∫ x : ℝ³, f x * g (y - x) : ℝ) : ℂ)) k
      = FourierTransform.fourier (fun y : ℝ³ => ((∫ x : ℝ³, f x * g (y - x) : ℝ) : ℂ))
          ((2 * Real.pi)⁻¹ • k) := Work.SmallBoxBridge.Resolve.kinFT_eq_fourier _ k
    _ = FourierTransform.fourier (MeasureTheory.convolution (fun x : ℝ³ => ((f x : ℝ) : ℂ))
          (fun x : ℝ³ => ((g x : ℝ) : ℂ)) (ContinuousLinearMap.lsmul ℂ ℂ) MeasureTheory.volume)
          ((2 * Real.pi)⁻¹ • k) := by rw [hconv]
    _ = (FourierTransform.fourier (fun x : ℝ³ => ((f x : ℝ) : ℂ)) ((2 * Real.pi)⁻¹ • k))
        * (FourierTransform.fourier (fun x : ℝ³ => ((g x : ℝ) : ℂ)) ((2 * Real.pi)⁻¹ • k)) := by
        simpa only [smul_eq_mul] using Real.fourier_smul_convolution_eq hF hG ((2 * Real.pi)⁻¹ • k)
    _ = Submission.BoseGases.kinFT (fun x : ℝ³ => ((f x : ℝ) : ℂ)) k
        * Submission.BoseGases.kinFT (fun x : ℝ³ => ((g x : ℝ) : ℂ)) k := by
        rw [← Work.SmallBoxBridge.Resolve.kinFT_eq_fourier (fun x : ℝ³ => ((f x : ℝ) : ℂ)) k,
            ← Work.SmallBoxBridge.Resolve.kinFT_eq_fourier (fun x : ℝ³ => ((g x : ℝ) : ℂ)) k]

/-! ## 4. The transform of an even real function is real -/

/-- For a real **even** function `g`, the `p`-convention transform `kinFT g` is real-valued. -/
lemma kinFT_ofReal_im_eq_zero {g : ℝ³ → ℝ} (hge : ∀ x : ℝ³, g (-x) = g x) (k : ℝ³) :
    (Submission.BoseGases.kinFT (fun x : ℝ³ => ((g x : ℝ) : ℂ)) k).im = 0 := by
  set Z : ℂ := ∫ x : ℝ³, Complex.exp (-(Complex.I * (inner ℝ k x : ℂ))) * ((g x : ℝ) : ℂ)
    with hZ
  have hkin : Submission.BoseGases.kinFT (fun x : ℝ³ => ((g x : ℝ) : ℂ)) k = Z := rfl
  rw [hkin]
  refine Complex.conj_eq_iff_im.mp ?_
  have h1 : (starRingEnd ℂ) Z
      = ∫ x : ℝ³, Complex.exp (Complex.I * (inner ℝ k x : ℂ)) * ((g x : ℝ) : ℂ) := by
    rw [hZ, ← integral_conj]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [map_mul, ← Complex.exp_conj]
    congr 1
    · rw [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring_nf
    · rw [Complex.conj_ofReal]
  have h2 : (∫ x : ℝ³, Complex.exp (Complex.I * (inner ℝ k x : ℂ)) * ((g x : ℝ) : ℂ)) = Z := by
    rw [hZ, ← MeasureTheory.integral_neg_eq_self
      (fun x : ℝ³ => Complex.exp (Complex.I * (inner ℝ k x : ℂ)) * ((g x : ℝ) : ℂ))
      MeasureTheory.volume]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [inner_neg_right, hge x]
    congr 1
    push_cast
    ring_nf
  exact h1.trans h2

/-! ## 5. The convolution theorem for `chat` -/

/-- **`chat` of a convolution is the product of the `chat`s.**  The evenness of `g` is what makes
its transform real, so that the real part of the product is the product of the real parts. -/
lemma chat_conv_chat_eq {f g : ℝ³ → ℝ} (hf : MeasureTheory.Integrable f)
    (hg : MeasureTheory.Integrable g) (hge : ∀ x : ℝ³, g (-x) = g x) (k : ℝ³) :
    Work.BoseFixR.chat (fun y : ℝ³ => ∫ x : ℝ³, f x * g (y - x)) k
      = Work.BoseFixR.chat f k * Work.BoseFixR.chat g k := by
  have hB := kinFT_ofReal_convolution hf hg k
  have him := kinFT_ofReal_im_eq_zero hge k
  simp only [Work.BoseFixR.chat]
  rw [hB, Complex.mul_re, him]
  ring

/-! ## 6. The support of a convolution -/

/-- If `tsupport f` and `tsupport g` lie in the closed ball of radius `R`, then the same holds
for `tsupport (f ⋆ g)` with radius `2R`.  (The pointwise argument: a nonvanishing product
`f x · g (z−x)` forces `‖x‖ ≤ R` and `‖z−x‖ ≤ R`, hence `‖z‖ ≤ 2R`.) -/
lemma tsupport_conv_subset {f g : ℝ³ → ℝ} {R : ℝ}
    (hfR : tsupport f ⊆ Metric.closedBall 0 R) (hgR : tsupport g ⊆ Metric.closedBall 0 R) :
    tsupport (fun y : ℝ³ => ∫ x : ℝ³, f x * g (y - x)) ⊆ Metric.closedBall 0 (2 * R) := by
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro z hz
  by_contra hzc
  have hzlt : 2 * R < ‖z‖ := by
    have h : ¬ (dist z 0 ≤ 2 * R) := fun hle => hzc (Metric.mem_closedBall.mpr hle)
    rw [dist_zero_right] at h
    exact not_le.mp h
  have hmem : ∀ w : ℝ³, w ∈ tsupport f → ‖w‖ ≤ R := by
    intro w hw
    have h := hfR hw
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have hmemg : ∀ w : ℝ³, w ∈ tsupport g → ‖w‖ ≤ R := by
    intro w hw
    have h := hgR hw
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  have hpt : ∀ x : ℝ³, f x * g (z - x) = 0 := by
    intro x
    by_cases hfx : f x = 0
    · rw [hfx, zero_mul]
    · have hgx : g (z - x) = 0 := by
        by_contra hne
        have h1 := hmem x (subset_tsupport f (Function.mem_support.mpr hfx))
        have h2 := hmemg (z - x) (subset_tsupport g (Function.mem_support.mpr hne))
        have h3 : ‖z‖ ≤ 2 * R := by
          have h4 : ‖z‖ ≤ ‖x‖ + ‖z - x‖ := by
            have h5 := norm_add_le x (z - x)
            rwa [show x + (z - x) = z by abel] at h5
          linarith
        linarith
      rw [hgx, mul_zero]
  exact hz (by simp [hpt])

/-! ## 7. The target -/

theorem chat_conv {f g : ℝ³ → ℝ} (hf : MeasureTheory.Integrable f)
    (hg : MeasureTheory.Integrable g) (hge : ∀ x : ℝ³, g (-x) = g x) :
    MeasureTheory.Integrable (fun y : ℝ³ => ∫ x : ℝ³, f x * g (y - x))
      ∧ (∫ y : ℝ³, |∫ x : ℝ³, f x * g (y - x)|) ≤ (∫ x : ℝ³, |f x|) * (∫ x : ℝ³, |g x|)
      ∧ (∀ k : ℝ³, Work.BoseFixR.chat (fun y : ℝ³ => ∫ x : ℝ³, f x * g (y - x)) k
          = Work.BoseFixR.chat f k * Work.BoseFixR.chat g k)
      ∧ (∀ R : ℝ, tsupport f ⊆ Metric.closedBall 0 R → tsupport g ⊆ Metric.closedBall 0 R →
          tsupport (fun y : ℝ³ => ∫ x : ℝ³, f x * g (y - x)) ⊆ Metric.closedBall 0 (2 * R)) :=
  ⟨chat_conv_integrable hf hg, chat_conv_abs_integral_le hf hg,
    fun k => chat_conv_chat_eq hf hg hge k,
    fun _ hfR hgR => tsupport_conv_subset hfR hgR⟩

end Work.BoseRowsL.Row2
