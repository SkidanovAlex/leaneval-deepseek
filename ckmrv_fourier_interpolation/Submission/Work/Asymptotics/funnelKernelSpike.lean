import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.funnelKernelSpike_core
import Submission.Work.Asymptotics.Funnel_Kfun_diag_bound

namespace Work.Asymptotics

open UpperHalfPlane

/-- The squared distance from `i t` to `τ`. -/
private lemma sq_norm_imagAxis_sub (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t) :
    ‖((Work.Kernels.imagAxis t ht : ℍ) : ℂ) - (τ : ℂ)‖ ^ 2 = τ.re ^ 2 + (t - τ.im) ^ 2 := by
  have hcoe : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  rw [hcoe, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

private lemma re_mul_I (t : ℝ) : ((t : ℂ) * Complex.I).re = 0 := by simp

private lemma im_mul_I (t : ℝ) : ((t : ℂ) * Complex.I).im = t := by simp

/-- **The funnel kernel in the spike region.**  On the spike
`{t : |t - Im τ| ≤ 1}` the CKMRV kernel `K^{(d)}(τ, i t)` differs from the sum of the two
translate poles (residues `1/(2π)` at `z = τ - 1` and `-1/(2π)` at `z = τ + 1`) by a locally
polynomially bounded function. -/
theorem funnelKernelSpike (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ (c₁ c₂ : ℂ) (C N M : ℝ), 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧ ‖c₁‖ ≤ C ∧ ‖c₂‖ ≤ C ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im →
        τ.im - 1 ≤ t → t ≤ τ.im + 1 →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t -
          (c₁ / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1)) +
            c₂ / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1)))‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨C₀, N₀, M₀, hC₀, hN₀, hM₀, hcore⟩ := funnelKernelSpike_core ℓ d hd
  obtain ⟨Cd, Nd, hCd, hNd, hdiag⟩ := Funnel_Kfun_diag_bound ℓ d hd
  have hpi1 : (0:ℝ) < 1 / Real.pi := by positivity
  have hCnorm1 : (0:ℝ) ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ := norm_nonneg _
  have hCnorm2 : (0:ℝ) ≤ ‖(-(1 / (2 * Real.pi)) : ℂ)‖ := norm_nonneg _
  refine ⟨(1 / (2 * Real.pi) : ℂ), (-(1 / (2 * Real.pi)) : ℂ),
    C₀ + Cd + 1 + 1 / Real.pi + ‖(1 / (2 * Real.pi) : ℂ)‖ + ‖(-(1 / (2 * Real.pi)) : ℂ)‖,
    max N₀ (max Nd 0), max M₀ 0, by positivity, le_max_of_le_left hN₀, le_max_of_le_left hM₀,
    ?_, ?_, ?_⟩
  · linarith
  · linarith
  · intro τ t hD him ht1 ht2
    have ht0 : 0 < t := by linarith
    set z : ℍ := Work.Kernels.imagAxis t ht0 with hzdef
    have hzcoe : (z : ℂ) = (t : ℂ) * Complex.I := rfl
    have hznorm : ‖(z : ℂ)‖ = t := by
      rw [hzcoe, norm_mul, Complex.norm_I, mul_one]
      have h2 : ‖(t : ℂ)‖ ^ 2 = t ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
      nlinarith [norm_nonneg (t : ℂ), ht0]
    have hKax : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t = Work.Kernels.Kfun ℓ d τ z := by
      rw [Work.Kernels.Kaxis, dif_pos ht0]
    have hfun : Funnel τ := ⟨hD, him⟩
    have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hscalepos : (0:ℝ) < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
    have h1t : (0:ℝ) < 1 + t := by linarith
    have hre_lt : τ.re < 1 := hD.2.1
    have hre_gt : -1 < τ.re := hD.1
    rw [hKax]
    by_cases hzt : z = τ
    · -- the diagonal case: only the explicit value at the diagonal enters
      have hzteq : (t : ℂ) * Complex.I = (τ : ℂ) := by
        rw [← hzcoe]
        exact congrArg (fun w : ℍ => (w : ℂ)) hzt
      have htau_re : τ.re = 0 := by
        have h : ((t : ℂ) * Complex.I).re = (τ : ℂ).re := congrArg Complex.re hzteq
        rw [re_mul_I, UpperHalfPlane.coe_re] at h
        exact h.symm
      have hdiag' := hdiag τ htau_re him
      have hnum1 : ((t : ℂ) * Complex.I - ((τ : ℂ) - 1)) = 1 := by rw [hzteq]; ring
      have hnum2 : ((t : ℂ) * Complex.I - ((τ : ℂ) + 1)) = -1 := by rw [hzteq]; ring
      have hval : (1 / (2 * Real.pi) : ℂ) / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1)) +
          (-(1 / (2 * Real.pi)) : ℂ) / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1))
            = 1 / (Real.pi : ℂ) := by
        rw [hnum1, hnum2, div_one, neg_div_neg_eq, div_one]
        have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        field_simp
        ring
      rw [hzt, hval]
      have hnormpi : ‖(1 / (Real.pi : ℂ))‖ = 1 / Real.pi := by
        rw [norm_div, norm_one]
        have h3 : ‖(Real.pi : ℂ)‖ = Real.pi := by
          have h4 : ‖(Real.pi : ℂ)‖ ^ 2 = Real.pi ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
          nlinarith [norm_nonneg (Real.pi : ℂ), Real.pi_pos]
        rw [h3]
      have hsplit : ‖Work.Kernels.Kfun ℓ d τ τ - 1 / (Real.pi : ℂ)‖
          ≤ ‖Work.Kernels.Kfun ℓ d τ τ‖ + 1 / Real.pi := by
        calc ‖Work.Kernels.Kfun ℓ d τ τ - 1 / (Real.pi : ℂ)‖
            ≤ ‖Work.Kernels.Kfun ℓ d τ τ‖ + ‖(1 / (Real.pi : ℂ))‖ := norm_sub_le _ _
          _ = ‖Work.Kernels.Kfun ℓ d τ τ‖ + 1 / Real.pi := by rw [hnormpi]
      refine le_trans hsplit ?_
      set N := max N₀ (max Nd 0) with hNdef
      set M := max M₀ 0 with hMdef
      have hN₀N : N₀ ≤ N := le_max_left _ _
      have hNdN : Nd ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
      have hM₀M : M₀ ≤ M := le_max_left _ _
      have hNnonneg : (0:ℝ) ≤ N := le_trans hN₀ hN₀N
      have hMnonneg : (0:ℝ) ≤ M := le_trans hM₀ hM₀M
      have hsp : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ N := Real.rpow_nonneg hscalepos.le _
      have htp : (0:ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg h1t.le _
      have h1M : (1:ℝ) ≤ (1 + t) ^ M := Real.one_le_rpow (by linarith : (1:ℝ) ≤ 1 + t) hMnonneg
      have hb1 : ‖Work.Kernels.Kfun ℓ d τ τ‖
          ≤ Cd * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
        refine le_trans hdiag' ?_
        have hs : Cd * (Work.Kernels.scale τ) ^ Nd ≤ Cd * (Work.Kernels.scale τ) ^ N :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hscale1 hNdN) hCd.le
        calc Cd * (Work.Kernels.scale τ) ^ Nd
            ≤ Cd * (Work.Kernels.scale τ) ^ N := hs
          _ = Cd * (Work.Kernels.scale τ) ^ N * 1 := (mul_one _).symm
          _ ≤ Cd * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M :=
              mul_le_mul_of_nonneg_left h1M (by positivity)
      have hb2 : 1 / Real.pi ≤ (1 / Real.pi) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
        have hsN : (1:ℝ) ≤ (Work.Kernels.scale τ) ^ N := Real.one_le_rpow hscale1 hNnonneg
        calc 1 / Real.pi = (1 / Real.pi) * 1 * 1 := by ring
          _ ≤ (1 / Real.pi) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
              apply mul_le_mul
              · apply mul_le_mul_of_nonneg_left hsN hpi1.le
              · exact h1M
              · norm_num
              · positivity
      have hCbig : Cd + 1 / Real.pi ≤ C₀ + Cd + 1 + 1 / Real.pi +
          ‖(1 / (2 * Real.pi) : ℂ)‖ + ‖(-(1 / (2 * Real.pi)) : ℂ)‖ := by
        linarith [hC₀, hCnorm1, hCnorm2]
      calc ‖Work.Kernels.Kfun ℓ d τ τ‖ + 1 / Real.pi
          ≤ (Cd * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
            + ((1 / Real.pi) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) := add_le_add hb1 hb2
        _ = (Cd + 1 / Real.pi) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring
        _ ≤ (C₀ + Cd + 1 + 1 / Real.pi + ‖(1 / (2 * Real.pi) : ℂ)‖ +
              ‖(-(1 / (2 * Real.pi)) : ℂ)‖) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCbig hsp) htp
    · -- the generic case: the core estimate applies
      have hzD : z ≠ (1 : ℝ) +ᵥ τ := by
        intro h
        have h1 : (z : ℂ) = (τ : ℂ) + 1 := by
          rw [h, UpperHalfPlane.coe_vadd]; push_cast; ring
        have h2 : ((z : ℂ)).re = ((τ : ℂ) + 1).re := congrArg Complex.re h1
        rw [hzcoe, re_mul_I, Complex.add_re, UpperHalfPlane.coe_re, Complex.one_re] at h2
        linarith
      have hzD' : z ≠ (-1 : ℝ) +ᵥ τ := by
        intro h
        have h1 : (z : ℂ) = (τ : ℂ) - 1 := by
          rw [h, UpperHalfPlane.coe_vadd]; push_cast; ring
        have h2 : ((z : ℂ)).re = ((τ : ℂ) - 1).re := congrArg Complex.re h1
        rw [hzcoe, re_mul_I, Complex.sub_re, UpperHalfPlane.coe_re, Complex.one_re] at h2
        linarith
      have hdist : ‖(z : ℂ) - (τ : ℂ)‖ ≤ 29 / 20 := by
        have hsq := sq_norm_imagAxis_sub τ t ht0
        have hre : τ.re ^ 2 ≤ 1 := by
          have h : |τ.re| < 1 := abs_lt.mpr ⟨hre_gt, hre_lt⟩
          nlinarith [h, sq_abs τ.re]
        have hd : (t - τ.im) ^ 2 ≤ 1 := by
          have h : |t - τ.im| ≤ 1 := by
            rw [abs_le]
            exact ⟨by linarith, by linarith⟩
          nlinarith [h, sq_abs (t - τ.im)]
        have h2 : ‖(z : ℂ) - (τ : ℂ)‖ ^ 2 ≤ 2 := by rw [hsq]; nlinarith
        have h4 : (2:ℝ) ≤ (29 / 20) ^ 2 := by norm_num
        nlinarith [norm_nonneg ((z : ℂ) - (τ : ℂ)), h2, h4]
      have hbridge := hcore τ z hfun hdist hzt hzD hzD'
      have hbridge' : ‖Work.Kernels.Kfun ℓ d τ z -
          ((1 / (2 * Real.pi) : ℂ) / ((t : ℂ) * Complex.I - ((τ : ℂ) - 1)) +
            (-(1 / (2 * Real.pi)) : ℂ) / ((t : ℂ) * Complex.I - ((τ : ℂ) + 1)))‖ ≤
          C₀ * (Work.Kernels.scale τ) ^ N₀ * (1 + ‖(z : ℂ)‖) ^ M₀ := by
        rw [← hzcoe]
        exact hbridge
      refine le_trans hbridge' ?_
      set N := max N₀ (max Nd 0) with hNdef
      set M := max M₀ 0 with hMdef
      have hN₀N : N₀ ≤ N := le_max_left _ _
      have hM₀M : M₀ ≤ M := le_max_left _ _
      have hNnonneg : (0:ℝ) ≤ N := le_trans hN₀ hN₀N
      have hMnonneg : (0:ℝ) ≤ M := le_trans hM₀ hM₀M
      have hsp : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ N := Real.rpow_nonneg hscalepos.le _
      have htp : (0:ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg h1t.le _
      have h2 : (1 + ‖(z : ℂ)‖) ^ M₀ ≤ (1 + t) ^ M := by
        have h2a : (1 + ‖(z : ℂ)‖) ^ M₀ ≤ (1 + t) ^ M₀ := by
          apply Real.rpow_le_rpow (by positivity)
          · rw [hznorm]
          · exact hM₀
        exact le_trans h2a (Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ 1 + t) hM₀M)
      have h1 : (Work.Kernels.scale τ) ^ N₀ ≤ (Work.Kernels.scale τ) ^ N :=
        Real.rpow_le_rpow_of_exponent_le hscale1 hN₀N
      have hCbig : C₀ ≤ C₀ + Cd + 1 + 1 / Real.pi +
          ‖(1 / (2 * Real.pi) : ℂ)‖ + ‖(-(1 / (2 * Real.pi)) : ℂ)‖ := by
        linarith [hCd, hpi1, hCnorm1, hCnorm2]
      have hXnonneg : (0:ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ M₀ := Real.rpow_nonneg (by positivity) _
      have hCnn : (0:ℝ) ≤ C₀ + Cd + 1 + 1 / Real.pi + ‖(1 / (2 * Real.pi) : ℂ)‖ +
          ‖(-(1 / (2 * Real.pi)) : ℂ)‖ := by positivity
      calc C₀ * (Work.Kernels.scale τ) ^ N₀ * (1 + ‖(z : ℂ)‖) ^ M₀
          = C₀ * ((Work.Kernels.scale τ) ^ N₀ * (1 + ‖(z : ℂ)‖) ^ M₀) := by ring
        _ ≤ (C₀ + Cd + 1 + 1 / Real.pi + ‖(1 / (2 * Real.pi) : ℂ)‖ +
              ‖(-(1 / (2 * Real.pi)) : ℂ)‖) *
              ((Work.Kernels.scale τ) ^ N * (1 + t) ^ M) := by
            apply mul_le_mul hCbig _ _ hCnn
            · exact mul_le_mul h1 h2 hXnonneg hsp
            · exact mul_nonneg (Real.rpow_nonneg hscalepos.le _) hXnonneg
        _ = (C₀ + Cd + 1 + 1 / Real.pi + ‖(1 / (2 * Real.pi) : ℂ)‖ +
              ‖(-(1 / (2 * Real.pi)) : ℂ)‖) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring

end Work.Asymptotics
