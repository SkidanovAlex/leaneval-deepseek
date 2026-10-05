import Mathlib
import Submission.Work.RPB.B5.kappaDefs
import Submission.Work.RPB.B5.kappaSmallAux

namespace Work.RPB.B5

theorem kshape_left_eq_chart (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (ρh : ℝ → ℝ → ℝ → ℝ) {δ η : ℝ} (hδ : 0 < δ) (hηδ : 4 * η ≤ δ) (k : ℤ) (τ : ℝ)
    (hcirc : ∀ t : ℝ, ∀ σ ∈ Set.Ioo (-η) 0,
      Work.RPV.uproj (W 0 t (ρh 0 t σ))
        = (Real.sqrt (2 + 2 * σ) : ℂ) * Complex.exp (t * Complex.I)) :
    ∀ σ ∈ Set.Ioo (-η) 0, ∀ t : ℝ,
      kshape CI W ρh δ k τ σ t = Work.RPV.uproj (W τ t (ρh τ t σ)) := by
  intro σ hσ t
  -- On the level interval `(-η, 0)` with `4η ≤ δ` the level `σ` is negative and `|σ| ≤ δ/2`,
  -- so the clamp is the identity, the blend cutoff `kblf` vanishes, and the phase offset
  -- `kphc` vanishes (`σ ≤ δ`).
  have hσ0 : σ < 0 := hσ.2
  have hσδ : σ ≤ δ := by have := hσ.1; linarith
  have hclamp : kclamp δ σ = σ := by
    apply kclamp_of_abs_le hδ
    rw [abs_of_neg hσ0]
    have := hσ.1
    linarith
  have hblf : kblf δ σ = 0 := by
    unfold kblf kstp
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  -- The `τ = 0` correction vanishes: the target circle is `√(2+2σ) e^{it}`, which is exactly
  -- the chart point at `τ = 0` on the level `σ`, by `hcirc`.
  have hdiff : ktarg δ k σ t - Work.RPV.uproj (W 0 t (ρh 0 t σ)) = 0 := by
    rw [ktarg_of_le hδ k hσδ, hcirc t σ hσ]
    unfold krd
    ring
  rw [kshape, knear, hblf, hclamp, hdiff]
  simp

end Work.RPB.B5
