import Mathlib
import Submission.Work.ZeroDensity.LogFree.poleLSDefs
import Submission.Work.ZeroDensity.LogFree.HB7MvtAny

namespace Work.ZeroDensity.LogFree

/-- Main term of the freeze-block: the family with the amplitudes frozen at `Y` is controlled
directly by the mean value theorem, with `δ = 1/L`, `Y₁ = Y e^{-L}`, `Y₂ = Y`; this gives
`(log e^L + C L) Σ ‖z i‖² Y^{2 a i} = (1+C) L Σ ‖z i‖² Y^{2 a i}`. -/
theorem HB7FreezeMain {C : ℝ} (hMVT : Work.ZeroDensity.LogFree.MvtMul C) :
    ∀ (L : ℝ), 1 ≤ L → ∀ {ι : Type*} [Fintype ι] (a γ : ι → ℝ) (z : ι → ℂ) (Y : ℝ), 0 < Y →
      (∀ i j, i ≠ j → 1 / L ≤ |γ i - γ j|) →
      (∫ y in (Y * Real.exp (-L))..Y,
          ‖∑ i, (z i * ((Y ^ (a i) : ℝ) : ℂ)) * (y : ℂ) ^ ((-(γ i : ℂ)) * Complex.I)‖ ^ 2 / y)
        ≤ (1 + C) * L * ∑ i, ‖z i‖ ^ 2 * Y ^ (2 * a i) := by
  intro L hL ι _ a γ z Y hY hsep
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hδ : 0 < 1 / L := by positivity
  have hY1 : 0 < Y * Real.exp (-L) := by positivity
  have hYle : Y * Real.exp (-L) ≤ Y := by
    have hexp : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (-L)]
  -- the mean value theorem for the frozen-amplitude family `ζ i = z i · Y^{a i}`
  have hmain := Work.ZeroDensity.LogFree.HB7MvtAny hMVT (1 / L) hδ γ
      (fun i => z i * ((Y ^ (a i) : ℝ) : ℂ)) (Y * Real.exp (-L)) Y hY1 hYle hsep
  -- the logarithmic factor collapses to `(1 + C) * L`
  have hlog : Real.log (Y / (Y * Real.exp (-L))) + C / (1 / L) = (1 + C) * L := by
    have h1 : Y / (Y * Real.exp (-L)) = Real.exp L := by
      rw [div_eq_iff (by positivity : Y * Real.exp (-L) ≠ 0), ← mul_assoc,
        mul_comm (Real.exp L) Y, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
        mul_one]
    rw [h1, Real.log_exp]
    field_simp
  -- the frozen amplitudes reproduce the weights `Y^{2 a i}`
  have hnorm : ∑ i, ‖z i * ((Y ^ (a i) : ℝ) : ℂ)‖ ^ 2
      = ∑ i, ‖z i‖ ^ 2 * Y ^ (2 * a i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_mul, mul_pow]
    have h2 : ‖((Y ^ (a i) : ℝ) : ℂ)‖ ^ 2 = Y ^ (2 * a i) := by
      have hsq : ‖((Y ^ (a i) : ℝ) : ℂ)‖ ^ 2 = (Y ^ (a i)) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
      rw [hsq, ← Real.rpow_mul_natCast hY.le (a i) 2]
      congr 1
      ring
    rw [h2]
  rw [hlog, hnorm] at hmain
  exact hmain

end Work.ZeroDensity.LogFree
