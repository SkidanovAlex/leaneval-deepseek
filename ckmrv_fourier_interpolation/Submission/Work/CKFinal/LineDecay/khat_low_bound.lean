import Mathlib
import Submission.Work.CKFinal.LineDecay.ContourPoint
import Submission.Work.Asymptotics.KPlus_slash_bound_half
import Submission.Work.Asymptotics.KMinus_slash_bound_half

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-- The two vertical lines `Re τ = ±1/2` with `Im τ ≥ 12` lie inside the CKMRV domain `𝒟`. -/
private lemma mem_DomainD_of_lines (τ : UpperHalfPlane) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2)
    (hy : 12 ≤ τ.im) : τ ∈ Work.Asymptotics.DomainD := by
  rw [Work.Asymptotics.mem_DomainD]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hre with h | h <;> rw [h] <;> norm_num
  · rcases hre with h | h <;> rw [h] <;> norm_num
  · have hsq : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (τ.re - 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hre' : ((τ : ℂ) - (1 / 2 : ℂ)).re = τ.re - 1 / 2 := by
        simp only [Complex.sub_re, UpperHalfPlane.coe_re]; norm_num
      have him' : ((τ : ℂ) - (1 / 2 : ℂ)).im = τ.im := by
        simp only [Complex.sub_im, UpperHalfPlane.coe_im]; norm_num
      rw [hre', him']; ring
    have h12 : (144 : ℝ) ≤ ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg (τ.re - 1 / 2 : ℝ), hy]
    nlinarith [norm_nonneg ((τ : ℂ) - (1 / 2 : ℂ)), h12]
  · have hsq : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (τ.re + 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hre' : ((τ : ℂ) + (1 / 2 : ℂ)).re = τ.re + 1 / 2 := by
        simp only [Complex.add_re, UpperHalfPlane.coe_re]; norm_num
      have him' : ((τ : ℂ) + (1 / 2 : ℂ)).im = τ.im := by
        simp only [Complex.add_im, UpperHalfPlane.coe_im]; norm_num
      rw [hre', him']; ring
    have h12 : (144 : ℝ) ≤ ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 := by
      rw [hsq]; nlinarith [sq_nonneg (τ.re + 1 / 2 : ℝ), hy]
    nlinarith [norm_nonneg ((τ : ℂ) + (1 / 2 : ℂ)), h12]

/-- If `‖z‖ ≥ 1` and `0 ≤ e`, then multiplication by the `e`-th power of `z` can only increase
the norm: `‖w‖ ≤ ‖z^e · w‖`. -/
private lemma norm_le_norm_zpow_mul {z w : ℂ} {e : ℤ} (he : 0 ≤ e) (hz : 1 ≤ ‖z‖) :
    ‖w‖ ≤ ‖z ^ e * w‖ := by
  have hzpow : z ^ e = z ^ (e.toNat) := by
    conv_lhs => rw [← Int.toNat_of_nonneg he]
    rw [zpow_natCast]
  rw [hzpow, norm_mul, norm_pow]
  calc ‖w‖ = 1 * ‖w‖ := (one_mul _).symm
    _ ≤ ‖z‖ ^ e.toNat * ‖w‖ := mul_le_mul_of_nonneg_right (one_le_pow₀ hz) (norm_nonneg _)

/-- **The hatted kernel is bounded on the low part `0 < t < 1` of the contour.**

Let `τ` lie on `Re τ = ±1/2` with `Im τ ≥ 12`, and suppose the divisor is bounded below on the
positive imaginary axis, `c ≤ ‖Δ(zcb u) * (j τ - j (zcb u))‖` for all `u ≥ 1/3` (`hdiv`).  Then
`K̂^{(d)}(τ, i t)` is bounded for `0 < t < 1` by a constant depending on `τ` (indeed one can take a
constant times `(1+‖τ‖)^A`).

Route: write `‖K̂(τ, i t)‖ ≤ (‖K_+(τ, i t)‖ + ‖K_-(τ, i t)‖)/2` and
`‖K_±(τ, i t)‖ = t^{d/2-2} ‖z^{d/2-2} K_±(τ, S • z)‖` with `z = zcb (1/t)` (so
`S • z = zcb t`, `Im z = 1/t ≥ 1`); the CKMRV quotient bounds at `z = zcb (1/t)` give
`‖K_±(τ, i t)‖ ≤ t^{d/2-2} C (1+‖τ‖)^A (1 + 1/t)^A e^{-π/t} / c` with `c` from `hdiv` at `u = 1/t`,
and `t^{d/2-2} (1 + 1/t)^A e^{-π/t}` is bounded for `t ∈ (0,1]` because the exponential `e^{-π/t}`
dominates every power of `1/t` (e.g. via `Work.CKFinal.rpow_exp_neg_bound` or by reducing to
boundedness of `u ↦ (1+u)^B e^{-πu}` on `u ≥ 1`). -/
theorem khat_low_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 12 ≤ τ.im)
    (hdiv : ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, 1 / 3 ≤ u →
      c ≤ ‖Work.Kernels.DeltaFun (zcb u)
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (zcb u))‖) :
    ∃ M : ℝ, ∀ t ∈ Set.Ioo (0 : ℝ) 1, ‖Work.Kernels.Khat ℓ d τ (zcb t)‖ ≤ M := by
  obtain ⟨c, hc, hdivc⟩ := hdiv
  obtain ⟨Cp, Ap, hCp, hAp, hbp⟩ := Work.Asymptotics.KPlus_slash_bound_half d hd
  obtain ⟨Cm, Am, hCm, hAm, hbm⟩ := Work.Asymptotics.KMinus_slash_bound_half ℓ d hd
  have hD : τ ∈ Work.Asymptotics.DomainD := mem_DomainD_of_lines τ hre hy
  have hτ2 : (1 : ℝ) / 2 ≤ τ.im := by linarith
  have he : (0 : ℤ) ≤ (d : ℤ) / 2 - 2 := by rcases hd with rfl | rfl <;> norm_num
  refine ⟨(Cp * (1 + ‖(τ : ℂ)‖) ^ Ap + Cm * (1 + ‖(τ : ℂ)‖) ^ Am) / (2 * c), ?_⟩
  intro t ht
  have ht0 : 0 < t := ht.1
  have htle1 : t ≤ 1 := le_of_lt ht.2
  have htinv : 0 < 1 / t := one_div_pos.mpr ht0
  have hz1 : (1 : ℝ) ≤ 1 / t := one_le_one_div ht0 htle1
  set z : UpperHalfPlane := zcb (1 / t) with hzdef
  have hzim : z.im = 1 / t := zcb_im htinv
  have hz3 : (1 : ℝ) / 3 ≤ z.im := by rw [hzim]; linarith
  have hzge1 : (1 : ℝ) ≤ ‖(z : ℂ)‖ := by
    have h : ‖(z : ℂ)‖ = 1 / t := by
      rw [hzdef, zcb_coe htinv, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [h]; exact hz1
  have hdivz : c ≤ ‖Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
    hdivc (1 / t) (by linarith)
  have hne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro hj
    have h0 : ‖Work.Kernels.DeltaFun z
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ = 0 := by
      rw [hj, sub_self, mul_zero, norm_zero]
    linarith
  have hS : ModularGroup.S • z = zcb t := by
    rw [hzdef, one_div]
    have h := S_smul_zcb (t := 1 / t) htinv
    rw [one_div, inv_inv] at h
    exact h
  have key : ∀ (C A : ℝ) (K : ℂ), 0 < C → (hb : ‖(z : ℂ) ^ ((d : ℤ) / 2 - 2) * K‖ ≤
        C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))
          / ‖Work.Kernels.DeltaFun z
              * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖) →
      ‖K‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A / c := by
    intro C A K hC hb
    refine le_trans (norm_le_norm_zpow_mul he hzge1) (le_trans hb ?_)
    have hP : 0 ≤ C * (1 + ‖(τ : ℂ)‖) ^ A :=
      mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)
    have hexp_le : Real.exp (-(Real.pi * z.im)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, z.im_pos]
    calc C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
        ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * 1
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
          gcongr
      _ = C * (1 + ‖(τ : ℂ)‖) ^ A
            / ‖Work.Kernels.DeltaFun z
                * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by ring
      _ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A / c := div_le_div_of_nonneg_left hP hc hdivz
  have hKp : ‖Work.Kernels.KPlus d τ (zcb t)‖ ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap / c := by
    have hb := hbp τ z hD hτ2 hz3 hne
    rw [hS] at hb
    exact key Cp Ap _ hCp hb
  have hKm : ‖Work.Kernels.KMinus ℓ d τ (zcb t)‖ ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ Am / c := by
    have hb := hbm τ z hD hτ2 hz3 hne
    rw [hS] at hb
    exact key Cm Am _ hCm hb
  have hKhat : ‖Work.Kernels.Khat ℓ d τ (zcb t)‖ ≤
      (‖Work.Kernels.KPlus d τ (zcb t)‖ + ‖Work.Kernels.KMinus ℓ d τ (zcb t)‖) / 2 := by
    rw [Work.Kernels.Khat, norm_div]
    rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
    have h := norm_sub_le (Work.Kernels.KPlus d τ (zcb t)) (Work.Kernels.KMinus ℓ d τ (zcb t))
    linarith
  calc ‖Work.Kernels.Khat ℓ d τ (zcb t)‖
      ≤ (‖Work.Kernels.KPlus d τ (zcb t)‖ + ‖Work.Kernels.KMinus ℓ d τ (zcb t)‖) / 2 := hKhat
    _ ≤ (Cp * (1 + ‖(τ : ℂ)‖) ^ Ap / c + Cm * (1 + ‖(τ : ℂ)‖) ^ Am / c) / 2 := by linarith
    _ = (Cp * (1 + ‖(τ : ℂ)‖) ^ Ap + Cm * (1 + ‖(τ : ℂ)‖) ^ Am) / (2 * c) := by ring

end Work.CKFinal.LineDecay
