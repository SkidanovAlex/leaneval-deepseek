import Mathlib
import Submission.Work.CKFinal.LineDecay.slash_qtau_twentyfour

namespace Work.CKFinal.LineDecay

/-- A point `τ` with `Re τ = ±1/2` and `Im τ ≥ 1` lies in the CKMRV domain `𝒟`.  Indeed the
strip conditions are immediate and each of the two circle conditions is implied by
`‖τ ∓ 1/2‖ ≥ |Im τ| = Im τ > 1/2`. -/
private lemma mem_DomainD_of_re_half_twentyfour {τ : UpperHalfPlane}
    (hre : τ.re = 1 / 2 ∨ τ.re = -1 / 2) (him : (1 : ℝ) ≤ τ.im) :
    τ ∈ Work.Asymptotics.DomainD := by
  have hre1 : -1 < τ.re ∧ τ.re < 1 := by
    rcases hre with h | h <;> (rw [h]; norm_num)
  refine ⟨hre1.1, hre1.2, ?_, ?_⟩
  · have h1 : |τ.im| ≤ ‖((τ : ℂ) - (1 / 2 : ℂ))‖ := by
      have h := Complex.abs_im_le_norm ((τ : ℂ) - (1 / 2 : ℂ))
      have him' : ((τ : ℂ) - (1 / 2 : ℂ)).im = τ.im := by simp
      rwa [him'] at h
    have h2 : |τ.im| = τ.im := abs_of_pos τ.im_pos
    linarith [abs_nonneg τ.im]
  · have h1 : |τ.im| ≤ ‖((τ : ℂ) + (1 / 2 : ℂ))‖ := by
      have h := Complex.abs_im_le_norm ((τ : ℂ) + (1 / 2 : ℂ))
      have him' : ((τ : ℂ) + (1 / 2 : ℂ)).im = τ.im := by simp
      rwa [him'] at h
    have h2 : |τ.im| = τ.im := abs_of_pos τ.im_pos
    linarith [abs_nonneg τ.im]

/-- **The `K₊^{(24)}` half of the tail bound on the lines `Re τ = ±1/2`.**

Assume the CKMRV divisor lower bound `hD` on the two lines:
`c (e^{-2π t} + e^{-2π Im τ}) ≤ ‖Δ(τ)Δ(it)(j(τ) - j(it))‖` for `Re τ = ±1/2`, `Im τ ≥ Y₀ ≥ 2`,
`t ≥ 1`.  Then, for those same `τ, t`, the slashed kernel on the line satisfies

`t^{10} ‖K₊^{(24)}(τ, S·(i t))‖ ≤ C (1+‖τ‖)^A · e^{-2π Im τ} · e^{-πt}/(1 + e^{2π(Im τ - t)})`.

Route: `Work.CKFinal.LineDecay.slash_qtau_twentyfour` gives
`‖(z:ℂ)^{10}K₊(τ,S·z)‖ ≤ C(1+‖τ‖)^A ‖q(τ)‖ e^{-π Im z}/‖Δ(z)(jτ-jz)‖` for `τ ∈ DomainD`,
`Im τ ≥ 2`, `Im z ≥ 1/3`, `jτ ≠ jz`; here `z = i t`, `Im z = t ≥ 1`, and `τ.re = ±1/2`,
`Im τ ≥ 2` imply `τ ∈ DomainD` (`-1 < ±1/2 < 1`, `|τ ∓ 1/2| = Im τ > 1/2`,
`|τ ± 1/2| = √(1+Im²τ) > 1/2`).
`hD` combined with `Work.Asymptotics.DeltaFun_upper_sharp`
(`‖Δ τ‖ ≤ 2e^{-2π Im τ}` for `Im τ ≥ 1`) gives
`‖Δ(z)(jτ-jz)‖ ≥ (c/2)(1 + e^{2π(Im τ - t)})`, whence also `jτ ≠ jz` and
`1/‖Δ(z)(jτ-jz)‖ ≤ (2/c)/(1 + e^{2π(Im τ - t)})`; finally
`‖q(τ)‖ = e^{-2π Im τ}` (`Work.Asymptotics.norm_qParamFun`). -/
theorem KPlus_tail_lines_twentyfour (ℓ : Work.Kernels.LogLambdaData) (c Y₀ : ℝ) (hc : 0 < c) (hY : 2 ≤ Y₀)
    (hD : ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im → 1 ≤ t →
        c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im)))
          ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) *
              (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im → 1 ≤ t →
        t ^ 10 * ‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
          ≤ C * (1 + ‖(τ : ℂ)‖) ^ A *
              (Real.exp (-(2 * Real.pi * τ.im)) *
                (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) := by
  obtain ⟨C₀, A₀, hC₀, hA₀, hb⟩ := Work.CKFinal.LineDecay.slash_qtau_twentyfour ℓ
  refine ⟨C₀ * (2 / c), A₀, by positivity, hA₀, ?_⟩
  intro τ t ht hreq him ht1
  set z : UpperHalfPlane := Work.Kernels.imagAxis t ht with hz
  have hzim : z.im = t := by rw [hz]; simp [Work.Kernels.imagAxis]
  have hznorm : ‖(z : ℂ)‖ = t := by
    rw [hz]
    rw [show ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht.le]
  have hτmem : τ ∈ Work.Asymptotics.DomainD :=
    mem_DomainD_of_re_half_twentyfour hreq (by linarith)
  have hτ2 : 2 ≤ τ.im := by linarith
  have hτhalf : (1 : ℝ) / 2 ≤ τ.im := by linarith
  have hzthird : (1 : ℝ) / 3 ≤ z.im := by rw [hzim]; linarith
  have hD' : c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im)))
      ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z *
          (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
    hD τ t ht hreq him ht1
  have hDz : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hprodpos : 0 < c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im))) :=
    mul_pos hc (add_pos (Real.exp_pos _) (Real.exp_pos _))
  have hne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro h
    have hzero : ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z *
        (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ = 0 := by
      rw [h]; simp
    rw [hzero] at hD'
    linarith
  set U : ℝ := ‖Work.Kernels.DeltaFun z *
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ with hU
  have hUnn : 0 ≤ U := by rw [hU]; exact norm_nonneg _
  have hfac : ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z *
        (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
      = ‖Work.Kernels.DeltaFun τ‖ * U := by
    rw [hU]
    simp only [norm_mul]
    ring
  -- The divisor lower bound `(c/2)(1 + e^{2π(Im τ - t)}) ≤ U`.
  have hden : (c / 2) * (1 + Real.exp (2 * Real.pi * (τ.im - t))) ≤ U := by
    have h1 : c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im)))
        ≤ ‖Work.Kernels.DeltaFun τ‖ * U := by
      rw [← hfac]; exact hD'
    have h2 : ‖Work.Kernels.DeltaFun τ‖ * U
        ≤ (2 * Real.exp (-(2 * Real.pi * τ.im))) * U :=
      mul_le_mul_of_nonneg_right
        (Work.Asymptotics.DeltaFun_upper_sharp τ (by linarith)) hUnn
    have h3 : c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im)))
        ≤ (2 * Real.exp (-(2 * Real.pi * τ.im))) * U := le_trans h1 h2
    have hkey : (c / 2) * (1 + Real.exp (2 * Real.pi * (τ.im - t)))
          * (2 * Real.exp (-(2 * Real.pi * τ.im)))
        = c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im))) := by
      have hFE : Real.exp (2 * Real.pi * (τ.im - t)) * Real.exp (-(2 * Real.pi * τ.im))
          = Real.exp (-(2 * Real.pi * t)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hexpand : (c / 2) * (1 + Real.exp (2 * Real.pi * (τ.im - t)))
            * (2 * Real.exp (-(2 * Real.pi * τ.im)))
          = c * Real.exp (-(2 * Real.pi * τ.im))
            + c * (Real.exp (2 * Real.pi * (τ.im - t)) * Real.exp (-(2 * Real.pi * τ.im))) := by
        ring
      rw [hexpand, hFE]; ring
    rw [← hkey] at h3
    have hpos : (0 : ℝ) < 2 * Real.exp (-(2 * Real.pi * τ.im)) := by positivity
    rw [mul_comm (2 * Real.exp (-(2 * Real.pi * τ.im))) U] at h3
    exact le_of_mul_le_mul_right h3 hpos
  -- The `K₊` bound on the slashed kernel.
  have hb' : ‖(z : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • z)‖
      ≤ C₀ * (1 + ‖(τ : ℂ)‖) ^ A₀ * ‖Work.Kernels.qParamFun τ‖
          * Real.exp (-(Real.pi * t)) / U := by
    have h := (hb τ z hτmem hτ2 hzthird hne).1
    rw [show ((24 : ℤ) / 2 - 2) = (10 : ℤ) by norm_num, zpow_ofNat] at h
    rw [hzim] at h
    rwa [← hU] at h
  have hlhs : t ^ 10 * ‖Work.Kernels.KPlus 24 τ (ModularGroup.S • z)‖
      = ‖(z : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • z)‖ := by
    rw [norm_mul, norm_pow, hznorm]
  have hPnn : 0 ≤ C₀ * (1 + ‖(τ : ℂ)‖) ^ A₀ * ‖Work.Kernels.qParamFun τ‖
      * Real.exp (-(Real.pi * t)) := by positivity
  have hdenpos : 0 < (c / 2) * (1 + Real.exp (2 * Real.pi * (τ.im - t))) := by positivity
  have hPU : C₀ * (1 + ‖(τ : ℂ)‖) ^ A₀ * ‖Work.Kernels.qParamFun τ‖
        * Real.exp (-(Real.pi * t)) / U
      ≤ C₀ * (1 + ‖(τ : ℂ)‖) ^ A₀ * ‖Work.Kernels.qParamFun τ‖
          * Real.exp (-(Real.pi * t))
          / ((c / 2) * (1 + Real.exp (2 * Real.pi * (τ.im - t)))) :=
    div_le_div_of_nonneg_left hPnn hdenpos hden
  refine le_trans (le_of_eq hlhs) (le_trans hb' (le_trans hPU ?_))
  have hEq : C₀ * (1 + ‖(τ : ℂ)‖) ^ A₀ * ‖Work.Kernels.qParamFun τ‖
        * Real.exp (-(Real.pi * t))
        / ((c / 2) * (1 + Real.exp (2 * Real.pi * (τ.im - t))))
      = C₀ * (2 / c) * (1 + ‖(τ : ℂ)‖) ^ A₀ *
          (Real.exp (-(2 * Real.pi * τ.im)) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) := by
    rw [Work.Asymptotics.norm_qParamFun τ]
    field_simp
  rw [hEq]

end Work.CKFinal.LineDecay
