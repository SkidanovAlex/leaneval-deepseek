import Mathlib
import Submission.Work.CKFinal.LineDecay.slash_qtau_twentyfour

namespace Work.CKFinal.LineDecay

open UpperHalfPlane ModularGroup
open scoped MatrixGroups

/-- A point `τ` with `Re τ = ±1/2` and `Im τ ≥ 1` lies in the CKMRV domain `𝒟`.  Indeed the
strip conditions are immediate and each of the two circle conditions is implied by
`‖τ ∓ 1/2‖ ≥ |Im τ| = Im τ > 1/2`. -/
private lemma mem_DomainD_of_re_half {τ : UpperHalfPlane}
    (hre : τ.re = 1 / 2 ∨ τ.re = -1 / 2) (him : (1 : ℝ) ≤ τ.im) :
    τ ∈ Work.Asymptotics.DomainD := by
  rw [Work.Asymptotics.mem_DomainD]
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

/-- The elementary identification of the two writings of the cusp factor for `d = 24`:
`e^{-π(4y+t)}/(e^{-2πt} + e^{-2πy}) = e^{-2πy}·e^{-πt}/(1 + e^{2π(y-t)})`, with the constants
`C, c` carried along. -/
private lemma tail_arith24 (C c y t : ℝ) :
    C * Real.exp (-(Real.pi * (4 * y + t))) /
        (c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * y))))
      = (C / c) * (Real.exp (-(2 * Real.pi * y)) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))) := by
  have hE1 : Real.exp (-(Real.pi * (4 * y + t)))
      = Real.exp (-(2 * Real.pi * y)) ^ 2 * Real.exp (-(Real.pi * t)) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hE2 : Real.exp (-(2 * Real.pi * t))
      = Real.exp (-(2 * Real.pi * y)) * Real.exp (2 * Real.pi * (y - t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hden : Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * y))
      = Real.exp (-(2 * Real.pi * y)) * (1 + Real.exp (2 * Real.pi * (y - t))) := by
    rw [mul_add, mul_one, hE2]; ring
  have hident : Real.exp (-(Real.pi * (4 * y + t))) /
        (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * y)))
      = Real.exp (-(2 * Real.pi * y)) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t)))) := by
    rw [hden, hE1, ← mul_div_assoc]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [show C * Real.exp (-(Real.pi * (4 * y + t))) /
        (c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * y))))
      = (C / c) * (Real.exp (-(Real.pi * (4 * y + t))) /
        (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * y)))) from by
    rw [div_mul_div_comm]]
  rw [hident]

/-- **The `K₋` half of the tail bound on the lines `Re τ = ±1/2`, in dimension 24.**

Assume the CKMRV divisor lower bound `hD` on the two lines:
`c (e^{-2π t} + e^{-2π Im τ}) ≤ ‖Δ(τ)Δ(it)(j(τ) - j(it))‖` for `Re τ = ±1/2`, `Im τ ≥ Y₀ ≥ 2`,
`t ≥ 1`.  Then, for those same `τ, t`, the slashed kernel on the line satisfies

`t¹⁰ ‖K₋^{(24)}(τ, S·(i t))‖ ≤ C (1+‖τ‖)^A · e^{-2π Im τ}·e^{-πt}/(1 + e^{2π(Im τ - t)})`.

Route: `Work.CKFinal.LineDecay.Ncusp24_delta_funnel_zfree ℓ` gives
`‖Δ(τ)·Ncusp ℓ 24 τ z‖ ≤ C₂(1+‖τ‖)^{A₂}·e^{-π(4 Im τ + Im z)}` for `τ ∈ DomainD`,
`Im τ ≥ 2`, `Im z ≥ 1/3`; `Work.Asymptotics.Ncusp_ident ℓ 24 (Or.inr rfl) τ z hne` gives
`Ncusp ℓ 24 τ z = Δ(z)(jτ - jz)·(z^{10} K₋^{(24)}(τ, S·z))` (note `-(2 - 24/2) = 10`); `hD`
lower-bounds the divisor `Δ(τ)Δ(z)(jτ-jz)`, and
`e^{-π(4 Im τ + t)}/(e^{-2πt}+e^{-2π Im τ}) = e^{-2π Im τ}·e^{-πt}/(1+e^{2π(Im τ - t)})`.
The hypothesis `jInvariantFun τ ≠ jInvariantFun (i t)` needed by `Ncusp_ident` follows from
`hD` (its right-hand side is `> 0`). -/
theorem KMinus_tail_lines_twentyfour (ℓ : Work.Kernels.LogLambdaData) (c Y₀ : ℝ) (hc : 0 < c) (hY : 2 ≤ Y₀)
    (hD : ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im → 1 ≤ t →
        c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im)))
          ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) *
              (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖) :
    ∃ C A : ℝ, 0 ≤ C ∧ 0 ≤ A ∧
      ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im → 1 ≤ t →
        t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
          ≤ C * (1 + ‖(τ : ℂ)‖) ^ A *
              (Real.exp (-(2 * Real.pi * τ.im)) *
                (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) := by
  obtain ⟨C₂, A₂, hC₂, hA₂, hb⟩ := Work.CKFinal.LineDecay.Ncusp24_delta_funnel_zfree ℓ
  refine ⟨C₂ / c, A₂, div_nonneg hC₂.le hc.le, hA₂, ?_⟩
  intro τ t ht hline hYτ h1t
  set z : UpperHalfPlane := Work.Kernels.imagAxis t ht with hz
  have hzim : z.im = t := by rw [hz]; simp [Work.Kernels.imagAxis]
  have hznorm : ‖(z : ℂ)‖ = t := by
    rw [hz]
    rw [show ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht.le]
  have hτ2 : 2 ≤ τ.im := le_trans hY hYτ
  have hτmem : τ ∈ Work.Asymptotics.DomainD :=
    mem_DomainD_of_re_half hline (by linarith)
  have hzthird : (1 : ℝ) / 3 ≤ z.im := by rw [hzim]; linarith
  have hDinst : c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im)))
      ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z *
          (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
    rw [hz]; exact hD τ t ht hline hYτ h1t
  have hne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z := by
    intro h
    have hpos : 0 < c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im))) :=
      mul_pos hc (add_pos (Real.exp_pos _) (Real.exp_pos _))
    have hlt : 0 < ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z *
        (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ :=
      lt_of_lt_of_le hpos hDinst
    rw [h, sub_self, mul_zero, norm_zero] at hlt
    exact lt_irrefl 0 hlt
  have hNc := hb τ z hτmem hτ2 hzthird
  rw [hzim] at hNc
  have hz10norm : ‖(z : ℂ) ^ 10‖ = t ^ 10 := by rw [norm_pow, hznorm]
  have hkey : t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • z)‖ *
        ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z *
          (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖
      = ‖Work.Kernels.DeltaFun τ * Work.Asymptotics.Ncusp ℓ 24 τ z‖ := by
    have e : (-(2 - ((24 : ℕ) : ℤ) / 2)) = (10 : ℤ) := by norm_num
    rw [Work.Asymptotics.Ncusp_ident ℓ 24 (Or.inr rfl) τ z hne, e, zpow_ofNat]
    rw [← hz10norm]
    simp only [norm_mul]
    ring
  rw [← hkey] at hNc
  have hA0 : 0 ≤ t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • z)‖ := by positivity
  have hstep : t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • z)‖ *
        (c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im))))
      ≤ C₂ * (1 + ‖(τ : ℂ)‖) ^ A₂ * Real.exp (-(Real.pi * (4 * τ.im + t))) :=
    le_trans (mul_le_mul_of_nonneg_left hDinst hA0) hNc
  have hDpos : 0 < c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im))) :=
    mul_pos hc (add_pos (Real.exp_pos _) (Real.exp_pos _))
  have hA2 : t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • z)‖
      ≤ C₂ * (1 + ‖(τ : ℂ)‖) ^ A₂ * Real.exp (-(Real.pi * (4 * τ.im + t))) /
          (c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im)))) := by
    rw [le_div_iff₀ hDpos]
    exact hstep
  refine le_trans hA2 (le_of_eq ?_)
  have htail : C₂ * (1 + ‖(τ : ℂ)‖) ^ A₂ * Real.exp (-(Real.pi * (4 * τ.im + t))) /
        (c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im))))
      = ((C₂ * (1 + ‖(τ : ℂ)‖) ^ A₂) / c) *
          (Real.exp (-(2 * Real.pi * τ.im)) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) :=
    tail_arith24 (C₂ * (1 + ‖(τ : ℂ)‖) ^ A₂) c τ.im t
  have hcomm : (C₂ / c) * (1 + ‖(τ : ℂ)‖) ^ A₂
      = (C₂ * (1 + ‖(τ : ℂ)‖) ^ A₂) / c := by ring
  rw [hcomm, ← htail]

end Work.CKFinal.LineDecay
