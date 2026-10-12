import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.latSampling_decay
import Submission.Work.BoseBoxFock.uvSmear_continuous_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.latSampling_uvSmear` — Poisson sampling of the UV-smoothed weight

The shifted Poisson sampling identity of the lattice `(2π/ℓ)ℤ³` at the *smoothed* one-body weight
`W = uvSmear fu Λ f = uvKernel fu Λ ⋆ f`:

    `∑'_m chat W (k_m)·e^{i⟪k_m,z⟫} = ℓ³ ∑'_d W (z + ℓ·latVec d)` ,   `k_m = (2π/ℓ) • latVec m` .

## Route

`uvSmear fu Λ f` is the convolution of the Schwartz kernel `uvKernel fu Λ` with `f`, so it is
**even** when `f` is (`uvSmear_even_aux`), continuous (`uvSmear_continuous`) and rapidly decreasing
(`uvSmear_rapidDecay`, from the compact support of `f`).  Evenness makes the `p`-convention Fourier
integral real and equal to `chat` (`chat_eq_kinFT_integral_aux`, via the corpus's
`Work.BoseRowsL.Row2.kinFT_ofReal_im_eq_zero`), which is exactly the shape in which
`Work.BoseBoxFock.latSampling_decay` (the decay-based Poisson summation) applies.  The rapid decay
of the *transform* — the third hypothesis of `latSampling_decay` — comes from
`chat_uvSmear`: `chat (uvSmear fu Λ f) p = uvCut fu Λ p · chat f p` is compactly supported in `p`,
`|uvCut fu Λ p| ≤ 1` and `|chat f| ≤ ∫|f|`.
-/

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Elementary properties of `uvSmear` and of `chat` -/

/-- **`uvSmear fu Λ f` is even when `f` is.**  The convolution kernel `uvKernel fu Λ` is even
(`uvKernel_even`), so changing variables `y ↦ -y` in the defining integral and using the evenness
of `f` gives the claim. -/
private lemma uvSmear_even_aux (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ) {f : E3 → ℝ}
    (hfev : ∀ x : E3, f (-x) = f x) (x : E3) :
    uvSmear fu Λ f (-x) = uvSmear fu Λ f x := by
  simp only [uvSmear]
  have h1 : (∫ y : E3, uvKernel fu Λ (-x - y) * f y)
      = ∫ y : E3, uvKernel fu Λ (-x + y) * f (-y) := by
    have h := MeasureTheory.integral_neg_eq_self
      (fun y : E3 => uvKernel fu Λ (-x - y) * f y) (volume : Measure E3)
    simpa using h.symm
  rw [h1]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show uvKernel fu Λ (-x + y) * f (-y) = uvKernel fu Λ (x - y) * f y
  rw [hfev y, show (-x + y : E3) = -(x - y) by abel, uvKernel_even]

/-- **The `p`-convention Fourier integral of an even real function is `chat`.** For `W` even the
corpus's transform `kinFT (W : ℂ)` is real, hence equals the real number `chat W p`: the real part
is `chat` by definition and the imaginary part vanishes by
`Work.BoseRowsL.Row2.kinFT_ofReal_im_eq_zero`. -/
private lemma chat_eq_kinFT_integral_aux {W : E3 → ℝ} (hWe : ∀ x : E3, W (-x) = W x) (p : E3) :
    (∫ x : E3, Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * (W x : ℂ))
      = ((Work.BoseFixR.chat W p : ℝ) : ℂ) := by
  apply Complex.ext
  · show (∫ x : E3, Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * (W x : ℂ)).re
      = ((Work.BoseFixR.chat W p : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    rfl
  · show (∫ x : E3, Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))) * (W x : ℂ)).im
      = ((Work.BoseFixR.chat W p : ℝ) : ℂ).im
    rw [Complex.ofReal_im]
    exact Work.BoseRowsL.Row2.kinFT_ofReal_im_eq_zero hWe p

/-- `|chat f p| ≤ ∫ |f|` for `f ∈ L¹`: `chat` is the real part of the `p`-convention Fourier
integral, whose modulus is bounded by the integral of the modulus, and the phase factor is
unimodular. -/
private lemma chat_abs_le_aux {f : E3 → ℝ} (_hf : Integrable f) (p : E3) :
    |Work.BoseFixR.chat f p| ≤ ∫ y : E3, |f y| := by
  have h1 : Work.BoseFixR.chat f p
      = (Submission.BoseGases.kinFT (fun y : E3 => (f y : ℂ)) p).re := rfl
  rw [h1]
  have hphase : ∀ y : E3, ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))‖ = 1 := by
    intro y
    rw [show -(Complex.I * ((inner ℝ p y : ℝ) : ℂ)) = ((-(inner ℝ p y) : ℝ) : ℂ) * Complex.I
        by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  calc |(Submission.BoseGases.kinFT (fun y : E3 => (f y : ℂ)) p).re|
      ≤ ‖Submission.BoseGases.kinFT (fun y : E3 => (f y : ℂ)) p‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ y : E3, ‖(f y : ℂ)‖ := by
        rw [Submission.BoseGases.kinFT]
        refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (f y : ℂ)‖ = ‖(f y : ℂ)‖
        rw [norm_mul, hphase y, one_mul]
    _ = ∫ y : E3, |f y| := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show ‖(f y : ℂ)‖ = |f y|
        rw [Complex.norm_real, Real.norm_eq_abs]

/-- `|ζ_Λ(k)| ≤ 1`: `0 ≤ f ≤ 1` for a `LowCut`. -/
private lemma abs_uvCut_le_one_aux (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ) (k : E3) :
    |uvCut fu Λ k| ≤ 1 := by
  rw [uvCut, abs_le]
  exact ⟨by linarith [fu.nonneg (‖k‖ / Λ)], fu.le_one _⟩

/-- `ζ_Λ(k) = 0` as soon as `2Λ ≤ ‖k‖` (`fu.f` vanishes above `2`). -/
private lemma uvCut_eq_zero_aux (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ) {k : E3}
    (hk : 2 * Λ ≤ ‖k‖) : uvCut fu Λ k = 0 := by
  rw [uvCut, fu.zero _ ?_]
  rw [le_div_iff₀ hΛ]
  linarith

/-! ## 2. The theorem -/

theorem latSampling_uvSmear (fu : Work.BoseBoxFix.LowCut) {Λ : ℝ} (hΛ : 0 < Λ)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : MeasureTheory.Integrable f)
    (hfs : HasCompactSupport f) (hfev : ∀ x : EuclideanSpace ℝ (Fin 3), f (-x) = f x)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (z : EuclideanSpace ℝ (Fin 3)) :
    (∑' m : Fin 3 → ℤ,
        (Work.BoseFixR.chat (Work.BoseBoxFock.uvSmear fu Λ f)
            ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m)) *
          Complex.exp (Complex.I *
            (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) z : ℂ)))
      = (ℓ : ℂ) ^ 3 * ∑' d : Fin 3 → ℤ,
          ((Work.BoseBoxFock.uvSmear fu Λ f (z + ℓ • Work.BoseBoxFock.latVec d) : ℝ) : ℂ) := by
  classical
  set W : E3 → ℝ := uvSmear fu Λ f with hWdef
  -- * evenness, continuity and rapid decay of `W`
  have hWev : ∀ x : E3, W (-x) = W x := by
    intro x
    rw [hWdef]
    exact uvSmear_even_aux fu Λ hfev x
  have hWcont : Continuous W := by
    rw [hWdef]
    exact uvSmear_continuous fu hΛ hf
  have hFcont : Continuous (fun x : E3 => (W x : ℂ)) :=
    Complex.continuous_ofReal.comp hWcont
  have hFdec : ∀ n : ℕ, ∃ C : ℝ, ∀ x : E3, ‖(W x : ℂ)‖ ≤ C * (1 + ‖x‖) ^ (-(n : ℤ)) := by
    intro n
    obtain ⟨C, _hC0, hCd⟩ := uvSmear_rapidDecay fu hΛ hf hfs n
    exact ⟨C, fun x => by
      rw [hWdef, Complex.norm_real, Real.norm_eq_abs]
      exact hCd x⟩
  -- * rapid decay of the Fourier transform, from `chat (uvSmear …) = uvCut · chat f` and the
  --   compact support of the cut-off
  have hFTdec : ∀ n : ℕ, ∃ C : ℝ, ∀ p : E3,
      ‖∫ y : E3, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (W y : ℂ)‖
        ≤ C * (1 + ‖p‖) ^ (-(n : ℤ)) := by
    intro n
    refine ⟨(∫ y : E3, |f y|) * (1 + 2 * Λ) ^ n, fun p => ?_⟩
    rw [chat_eq_kinFT_integral_aux hWev p, hWdef, chat_uvSmear fu hΛ hf p,
      Complex.norm_real, Real.norm_eq_abs, zpow_neg, zpow_natCast, ← div_eq_mul_inv,
      le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖p‖) ^ n)]
    by_cases h0 : uvCut fu Λ p = 0
    · rw [h0]
      simp only [zero_mul, abs_zero]
      positivity
    · have hnorm : ‖p‖ ≤ 2 * Λ := by
        by_contra hlt
        rw [not_le] at hlt
        exact h0 (uvCut_eq_zero_aux fu hΛ hlt.le)
      calc |uvCut fu Λ p * Work.BoseFixR.chat f p| * (1 + ‖p‖) ^ n
          = |uvCut fu Λ p| * |Work.BoseFixR.chat f p| * (1 + ‖p‖) ^ n := by rw [abs_mul]
        _ ≤ 1 * (∫ y : E3, |f y|) * (1 + 2 * Λ) ^ n := by
            refine mul_le_mul (mul_le_mul (abs_uvCut_le_one_aux fu Λ p) (chat_abs_le_aux hf p)
              (abs_nonneg _) (by norm_num)) ?_ (by positivity) (by positivity)
            exact pow_le_pow_left₀ (by positivity) (by linarith) n
        _ = (∫ y : E3, |f y|) * (1 + 2 * Λ) ^ n := by ring
  -- * the Fourier samples are `chat`
  have hterm : ∀ m : Fin 3 → ℤ,
      (∫ x : E3, Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) x : ℂ)))
          * (W x : ℂ))
        = ((Work.BoseFixR.chat W ((2 * Real.pi / ℓ) • latVec m) : ℝ) : ℂ) :=
    fun m => chat_eq_kinFT_integral_aux hWev _
  -- * assembly
  have hL : (∑' m : Fin 3 → ℤ,
        (Work.BoseFixR.chat W ((2 * Real.pi / ℓ) • latVec m)) *
          Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ)))
      = ∑' m : Fin 3 → ℤ,
          (∫ x : E3, Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) x : ℂ)))
              * (W x : ℂ)) *
            Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • latVec m) z : ℂ)) :=
    tsum_congr fun m => by rw [hterm m]
  rw [hL, latSampling_decay hℓ hFcont hFdec hFTdec z]

end

end Work.BoseBoxFock
