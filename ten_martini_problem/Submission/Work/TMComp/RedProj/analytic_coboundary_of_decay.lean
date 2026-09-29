import Mathlib
import Submission.Work.TMComp.RedProj.summable_int_exp_neg
import Submission.Work.TMComp.RedProj.fourier_series_pointwise
import Submission.Work.TMComp.RedProj.analyticOnNhd_tsum_fourier
import Submission.Work.TMComp.RedProj.exp_ne_one_of_irrational

/-!
# The analytic coboundary of a function with exponentially decaying Fourier coefficients

For an irrational `α : ℝ` and a continuous `1`-periodic `φ : ℝ → ℂ` whose non-zero Fourier
coefficients on `[0,1]` decay at least like `C · ‖exp (2πi k α) − 1‖ · exp (−η|k|)`, the
cohomological equation `φ − ∫ φ = ψ(· + α) − ψ` has a `1`-periodic, analytic solution `ψ`.

This is the classical small-denominator argument.  The coefficients
`c k = ∫_0^1 φ(t) exp(-2πi k t) dt` decay exponentially, so the Fourier series converges
absolutely and reproduces `φ` (`fourier_series_pointwise`).  The formal solution is
`ψ = ∑_{k ≠ 0} c k / (exp (2πi k α) − 1) · exp (2πi k x)`; dividing by the small
denominator is legitimate because `α` is irrational (`exp_ne_one_of_irrational`), and the
resulting coefficients are bounded by `C exp (-η|k|)`, so the series is absolutely
convergent on the strip `2π|Im w| < η` and defines an analytic function
(`analyticOnNhd_tsum_fourier`), while `summable_int_exp_neg` supplies the summability of
the geometric majorant over `ℤ`.
-/

namespace Work.TMComp.RedProj

noncomputable section

open scoped Classical

theorem analytic_coboundary_of_decay (α : ℝ) (hα : Irrational α) (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hper : ∀ x, φ (x + 1) = φ x)
    (η : ℝ) (hη : 0 < η) (C : ℝ) (hC : 0 < C)
    (hbd : ∀ k : ℤ, k ≠ 0 → ‖fourierCoeffOn (show (0:ℝ) < 1 by norm_num) φ k‖
      ≤ C * ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ * Real.exp (-(η * |(k : ℝ)|))) :
    ∃ ψ : ℝ → ℂ, (∀ x, ψ (x + 1) = ψ x) ∧ AnalyticOnNhd ℝ ψ Set.univ ∧
      ∀ x, φ x - (∫ t in (0 : ℝ)..1, φ t) = ψ (x + α) - ψ x := by
  classical
  have h1 : (0 : ℝ) < 1 := by norm_num
  let E : ℤ → ℂ := fun k => Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I)
  let c : ℤ → ℂ := fun k => fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) φ k
  let d : ℤ → ℂ := fun k => c k / (E k - 1)
  let F : ℂ → ℂ := fun w => ∑' k : ℤ, d k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * w)
  have hE1 : ∀ k : ℤ, k ≠ 0 → E k ≠ 1 := by
    intro k hk hc
    exact exp_ne_one_of_irrational α hα k hk hc
  have hEnorm : ∀ k : ℤ, ‖E k‖ = 1 := by
    intro k
    change ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I)‖ = 1
    rw [Complex.norm_exp]
    have hre : (2 * Real.pi * (k : ℝ) * α * Complex.I).re = 0 := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero]
  have hEsub : ∀ k : ℤ, ‖E k - 1‖ ≤ 2 := by
    intro k
    calc ‖E k - 1‖ ≤ ‖E k‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hEnorm k]; norm_num
  have hEarg : ∀ k : ℤ, Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (α:ℂ)) = E k := by
    intro k
    change Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (α:ℂ)) =
      Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I)
    congr 1
    push_cast
    ring
  -- summability of c
  have hsum_c0 : Summable (fun k : ℤ => if k = 0 then 0 else c k) := by
    refine Summable.of_norm_bounded ((summable_int_exp_neg η hη).mul_left (2 * C)) ?_
    intro k
    by_cases hk : k = 0
    · simp [hk, hC.le]
    · simp only [hk, if_false]
      have hb : ‖c k‖ ≤ C * ‖E k - 1‖ * Real.exp (-(η * |(k:ℝ)|)) := hbd k hk
      have h2 : C * ‖E k - 1‖ ≤ C * 2 := mul_le_mul_of_nonneg_left (hEsub k) hC.le
      have hexp : 0 ≤ Real.exp (-(η * |(k:ℝ)|)) := Real.exp_nonneg _
      calc ‖c k‖ ≤ C * ‖E k - 1‖ * Real.exp (-(η * |(k:ℝ)|)) := hb
        _ ≤ C * 2 * Real.exp (-(η * |(k:ℝ)|)) := mul_le_mul_of_nonneg_right h2 hexp
        _ = 2 * C * Real.exp (-(η * |(k:ℝ)|)) := by ring
  have hsum_c : Summable c := by
    have h2 : Summable (fun k : ℤ => if k = 0 then c k else 0) :=
      (hasSum_single (0 : ℤ) (fun b hb => by simp [hb])).summable
    have h3 : Summable (fun k : ℤ => (if k = 0 then 0 else c k) + (if k = 0 then c k else 0)) :=
      hsum_c0.add h2
    exact (summable_congr (fun k => by by_cases hk : k = 0 <;> simp [hk])).mp h3
  -- bound and summability of d
  have hdb : ∀ k : ℤ, ‖d k‖ ≤ C * Real.exp (-(η * |(k : ℝ)|)) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have hE0 : E 0 - 1 = 0 := by
        change Complex.exp (2 * Real.pi * ((0:ℤ) : ℝ) * α * Complex.I) - 1 = 0
        simp
      change ‖c 0 / (E 0 - 1)‖ ≤ C * Real.exp (-(η * |(((0:ℤ):ℝ))|))
      rw [hE0, div_zero, norm_zero]
      simpa using hC.le
    · have hne : E k - 1 ≠ 0 := sub_ne_zero.mpr (hE1 k hk)
      have hpos : 0 < ‖E k - 1‖ := norm_pos_iff.mpr hne
      change ‖c k / (E k - 1)‖ ≤ C * Real.exp (-(η * |(k:ℝ)|))
      rw [norm_div, div_le_iff₀ hpos]
      have hb : ‖c k‖ ≤ C * ‖E k - 1‖ * Real.exp (-(η * |(k:ℝ)|)) := hbd k hk
      calc ‖c k‖ ≤ C * ‖E k - 1‖ * Real.exp (-(η * |(k:ℝ)|)) := hb
        _ = (C * Real.exp (-(η * |(k:ℝ)|))) * ‖E k - 1‖ := by ring
  have hsum_d : Summable d :=
    Summable.of_norm_bounded ((summable_int_exp_neg η hη).mul_left C) hdb
  -- the coefficient identity d k * (E k - 1) = (if k = 0 then 0 else c k)
  have hdE : ∀ k : ℤ, d k * (E k - 1) = if k = 0 then 0 else c k := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have hE0 : E 0 - 1 = 0 := by
        change Complex.exp (2 * Real.pi * ((0:ℤ) : ℝ) * α * Complex.I) - 1 = 0
        simp
      rw [hE0, mul_zero]
      simp
    · rw [if_neg hk]
      have hne : E k - 1 ≠ 0 := sub_ne_zero.mpr (hE1 k hk)
      change c k / (E k - 1) * (E k - 1) = c k
      rw [div_mul_cancel₀ _ hne]
  -- norm of the exponential
  have hexp_norm : ∀ (k : ℤ) (z : ℂ), z.im = 0 →
      ‖Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * z)‖ = 1 := by
    intro k z hz
    rw [Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * (k:ℂ) * z).re = 0 := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hz]
    rw [hre, Real.exp_zero]
  have hsum_dB : ∀ (z : ℂ), z.im = 0 →
      Summable (fun k : ℤ => d k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * z)) := by
    intro z hz
    refine Summable.of_norm_bounded ((summable_int_exp_neg η hη).mul_left C) ?_
    intro k
    rw [norm_mul, hexp_norm k z hz, mul_one]
    exact hdb k
  -- analyticity
  have hF_an : AnalyticOnNhd ℂ F {w : ℂ | 2 * Real.pi * |w.im| < η} :=
    analyticOnNhd_tsum_fourier d η C hη hdb
  have hψ_an : AnalyticOnNhd ℝ (fun x : ℝ => F (x:ℂ)) Set.univ := by
    intro x _
    have hxmem : ((x:ℝ):ℂ) ∈ {w : ℂ | 2 * Real.pi * |w.im| < η} := by
      simp [Complex.ofReal_im, hη]
    have ha1 : AnalyticAt ℂ F ((x:ℝ):ℂ) := hF_an _ hxmem
    have ha2 : AnalyticAt ℝ F ((x:ℝ):ℂ) := ha1.restrictScalars
    exact ha2.comp (Complex.ofRealCLM.analyticAt x)
  -- periodicity
  have hψ_per : ∀ x : ℝ, F (((x + 1 : ℝ)) : ℂ) = F ((x:ℝ):ℂ) := by
    intro x
    rw [Complex.ofReal_add, Complex.ofReal_one]
    change (∑' k : ℤ, d k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * ((x:ℂ) + 1))) =
      (∑' k : ℤ, d k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ)))
    apply tsum_congr
    intro k
    have hk1 : Complex.exp (2 * Real.pi * Complex.I * (k:ℂ)) = 1 := by
      have : 2 * Real.pi * Complex.I * (k:ℂ) = (k:ℂ) * (2 * Real.pi * Complex.I) := by ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [mul_add, mul_one, Complex.exp_add, hk1, mul_one]
  -- the main identity
  have hmain : ∀ x : ℝ, F ((x:ℂ) + (α:ℂ)) - F (x:ℂ) =
      (∑' k : ℤ, c k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ))) - c 0 := by
    intro x
    have hz1 : ((x:ℂ) + (α:ℂ)).im = 0 := by
      simp [Complex.add_im, Complex.ofReal_im]
    have hz2 : (x:ℂ).im = 0 := by simp
    have hs1 := hsum_dB ((x:ℂ) + (α:ℂ)) hz1
    have hs2 := hsum_dB (x:ℂ) hz2
    have hBs : Summable (fun k : ℤ => c k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ))) :=
      (fourier_series_pointwise φ hφ hper hsum_c x).summable
    have hF1 : F ((x:ℂ) + (α:ℂ)) = ∑' k : ℤ, d k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * ((x:ℂ) + (α:ℂ))) := rfl
    have hF2 : F (x:ℂ) = ∑' k : ℤ, d k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ)) := rfl
    have hterm : ∀ k : ℤ, d k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * ((x:ℂ) + (α:ℂ))) -
        d k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ)) =
        (if k = 0 then 0 else c k) * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ)) := by
      intro k
      have hA : Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * ((x:ℂ) + (α:ℂ))) =
          Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ)) * E k := by
        rw [mul_add, Complex.exp_add, hEarg k]
      rw [hA, ← hdE k]
      ring
    rw [hF1, hF2, (Summable.tsum_sub hs1 hs2).symm]
    calc ∑' k : ℤ, (d k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * ((x:ℂ) + (α:ℂ))) -
            d k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ)))
        = ∑' k : ℤ, (if k = 0 then 0 else c k) * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ)) :=
          tsum_congr (fun k => hterm k)
      _ = ∑' k : ℤ, (if k = 0 then 0 else c k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ))) :=
          tsum_congr (fun k => by by_cases hk : k = 0 <;> simp [hk])
      _ = (∑' k : ℤ, c k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ))) - c 0 := by
          have hsplit := Summable.tsum_eq_add_tsum_ite hBs 0
          have hB0 : Complex.exp (2 * Real.pi * Complex.I * ((0:ℤ):ℂ) * (x:ℂ)) = 1 := by simp
          rw [hsplit, hB0, mul_one]
          ring
  refine ⟨fun x : ℝ => F (x:ℂ), ?_, ?_, ?_⟩
  · intro x
    exact hψ_per x
  · exact hψ_an
  · intro x
    have hx := hmain x
    have hfx : (∑' k : ℤ, c k * Complex.exp (2 * Real.pi * Complex.I * (k:ℂ) * (x:ℂ))) = φ x :=
      (fourier_series_pointwise φ hφ hper hsum_c x).tsum_eq
    have hc0 : c 0 = ∫ t in (0:ℝ)..1, φ t := by
      change fourierCoeffOn h1 φ 0 = ∫ t in (0:ℝ)..1, φ t
      rw [fourierCoeffOn_eq_integral]
      simp
    rw [hfx, hc0] at hx
    change φ x - (∫ t in (0:ℝ)..1, φ t) = F (((x + α : ℝ)) : ℂ) - F ((x:ℝ):ℂ)
    rw [Complex.ofReal_add]
    exact hx.symm

end

end Work.TMComp.RedProj
