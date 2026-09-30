import Mathlib
import Submission.Work.BMF.Psi1_L2_bound
import Submission.Work.BMF.Psi2_L2_bound
import Submission.Work.BMF.mrlas.Psi_norm_sq_continuous

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Unit-window `L²` bound for `Ψ` on the line `Re s = 1 + α`

For every multiplicative-type `1`-bounded `f : ℕ → ℂ` with `f 1 = 1`, every `0 < α ≤ 1` and
every `c : ℝ` there is an absolute constant `C > 0` with

`∫_{c}^{c+1} ‖Ψ f (1 + α + i τ)‖² dτ ≤ C / α`.

Since `Ψ = Ψ₁ + Ψ₂` (by definition of `Ψ₂ = Ψ - Ψ₁`), the pointwise inequality
`‖Ψ‖² ≤ 2‖Ψ₁‖² + 2‖Ψ₂‖²` together with the already-proved unit-window bounds
`Work.BMF.Psi1_L2_bound` and `Work.BMF.Psi2_L2_bound` gives the claim with `C = 2 C₁ + 2 C₂`.
-/

namespace Work.BMF.casdiv

open MeasureTheory intervalIntegral

theorem psi_window_l2_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 → (∀ n, ‖f n‖ ≤ 1) →
      ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ c : ℝ,
        (∫ τ in c..(c+1), ‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
          ≤ C / α := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.BMF.Psi1_L2_bound
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.BMF.Psi2_L2_bound
  refine ⟨2 * C₁ + 2 * C₂, by positivity, ?_⟩
  intro f hf1 hb α hα hα1 c
  have ha1' : (1 : ℝ) < 1 + α := by linarith
  have hcontPsi : Continuous
      (fun τ : ℝ => ‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) :=
    (Work.BMF.mrlas.Psi_nsc_Psi_continuous f hf1 hb (1 + α) ha1').norm.pow 2
  obtain ⟨hcontP1, hcontP2⟩ :=
    Work.BMF.mrlas.Psi_norm_sq_continuous f hf1 hb (1 + α) ha1'
  have h1 := hC₁ f hb α hα hα1 c
  have h2 := hC₂ f hf1 hb α hα hα1 c
  have hsplit : ∀ τ : ℝ,
      ‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
        ≤ 2 * ‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
          + 2 * ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 := by
    intro τ
    have hPsi : Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
        = Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
          + Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I) := by
      rw [Work.BMF.Psi2]; ring
    rw [hPsi]
    have hsq : (‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
          + ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖) ^ 2
        ≤ 2 * ‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
          + 2 * ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖
        - ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖)]
    exact le_trans (pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2) hsq
  have hint : IntervalIntegrable
      (fun τ : ℝ => ‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
      volume c (c + 1) := hcontPsi.intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun τ : ℝ => 2 * ‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
        + 2 * ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
      volume c (c + 1) :=
    ((hcontP1.const_mul 2).add (hcontP2.const_mul 2)).intervalIntegrable _ _
  calc (∫ τ in c..(c+1), ‖Work.BMF.Psi f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
      ≤ ∫ τ in c..(c+1), (2 * ‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
          + 2 * ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by
        refine intervalIntegral.integral_mono_on (by linarith : c ≤ c + 1) hint hint2 ?_
        intro τ _; exact hsplit τ
    _ = 2 * (∫ τ in c..(c+1), ‖Work.BMF.Psi1 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2)
          + 2 * (∫ τ in c..(c+1), ‖Work.BMF.Psi2 f (((1 + α : ℝ) : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2) := by
        rw [intervalIntegral.integral_add ((hcontP1.const_mul 2).intervalIntegrable _ _)
          ((hcontP2.const_mul 2).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ 2 * (C₁ / α) + 2 * (C₂ / α) := by linarith
    _ = (2 * C₁ + 2 * C₂) / α := by rw [div_eq_mul_inv]; ring

end Work.BMF.casdiv
