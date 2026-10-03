import Mathlib
import Submission.Work.FIArea5.S16Hecke.gammaLowerSharpVertical
import Submission.Work.FIArea5.S16Hecke.heckeLStripAux

namespace Work.FIArea6Hecke.R

/-- Upper bound, uniform in the strip `1/2 ≤ σ ≤ 1`, for the modulus of the Gamma ratio
`Γ(2 - s/2) / Γ(1 + s/2)` at `s = σ + i t`: it is at most a constant times
`(1 + |t|/2)^(1 - σ)`.  This is the ratio which, raised to the `20`-th power, produces the
`|t|`-power `20(1-σ)` of the Phragmén–Lindelöf weight `heckeStripW`. -/
private theorem gammaRatioStripUpper :
    ∃ K : ℝ, 0 < K ∧ ∀ (σ t : ℝ), 1 / 2 ≤ σ → σ ≤ 1 →
      ‖Complex.Gamma (2 - ((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖ /
        ‖Complex.Gamma (1 + ((σ : ℂ) + (t : ℂ) * Complex.I) / 2)‖
        ≤ K * (1 + |t| / 2) ^ (1 - σ) := by
  obtain ⟨cl, hclpos, hcl⟩ := Work.FIArea5.S16Hecke.gammaLowerSharpVertical
  obtain ⟨Cu, hCupos, hCu⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
  refine ⟨Cu / cl, by positivity, ?_⟩
  intro σ t hσ1 hσ2
  -- (B) upper bound for `‖Γ(2 - s/2)‖`
  have habs : |(-(t / 2) : ℝ)| = |t| / 2 := by
    rw [abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hGu : ‖Complex.Gamma (((2 - σ / 2 : ℝ) : ℂ) + ((-(t / 2) : ℝ) : ℂ) * Complex.I)‖
      ≤ Cu * (1 + |t| / 2) ^ (3 / 2 - σ / 2) * Real.exp (-(Real.pi / 2) * (|t| / 2)) := by
    have h := hCu (2 - σ / 2) (-(t / 2)) (by linarith) (by linarith)
    rw [habs] at h
    have hexp : (2 - σ / 2) - 1 / 2 = 3 / 2 - σ / 2 := by ring
    rw [hexp] at h
    exact h
  have e1 : 2 - ((σ : ℂ) + (t : ℂ) * Complex.I) / 2
      = ((2 - σ / 2 : ℝ) : ℂ) + ((-(t / 2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  -- (C) lower bound for `‖Γ(1 + s/2)‖`
  have hGl : cl * (1 + |t| / 2) ^ (1 / 2 + σ / 2) * Real.exp (-(Real.pi / 2) * (|t| / 2))
      ≤ ‖Complex.Gamma (((1 + σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)‖ := by
    have h := hcl (1 + σ / 2) (t / 2) (by linarith) (by linarith)
    have habs2 : |(t / 2 : ℝ)| = |t| / 2 := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [habs2] at h
    have hexp : (1 + σ / 2) - 1 / 2 = 1 / 2 + σ / 2 := by ring
    rw [hexp] at h
    exact h
  have e2 : 1 + ((σ : ℂ) + (t : ℂ) * Complex.I) / 2
      = ((1 + σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hG1ne : Complex.Gamma (((1 + σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    have hre : (((1 + σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I).re = 1 + σ / 2 := by simp
    rw [hre]; linarith
  have hbase2 : (0 : ℝ) < 1 + |t| / 2 := by positivity
  have hXY : (1 + |t| / 2) ^ (3 / 2 - σ / 2)
      = (1 + |t| / 2) ^ (1 - σ) * (1 + |t| / 2) ^ (1 / 2 + σ / 2) := by
    rw [← Real.rpow_add hbase2]
    congr 1; ring
  rw [e1, e2, div_le_iff₀ (norm_pos_iff.mpr hG1ne)]
  calc ‖Complex.Gamma (((2 - σ / 2 : ℝ) : ℂ) + ((-(t / 2) : ℝ) : ℂ) * Complex.I)‖
      ≤ Cu * (1 + |t| / 2) ^ (3 / 2 - σ / 2) * Real.exp (-(Real.pi / 2) * (|t| / 2)) := hGu
    _ = (Cu / cl) * (1 + |t| / 2) ^ (1 - σ)
          * (cl * (1 + |t| / 2) ^ (1 / 2 + σ / 2) * Real.exp (-(Real.pi / 2) * (|t| / 2))) := by
        rw [hXY]; field_simp
    _ ≤ (Cu / cl) * (1 + |t| / 2) ^ (1 - σ)
          * ‖Complex.Gamma (((1 + σ / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)‖ := by
        exact mul_le_mul_of_nonneg_left hGl (by positivity)

theorem heckeStripWGammaRatioPow :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ τ : ℝ), 1 / 2 ≤ σ → σ ≤ 1 →
      (‖Complex.Gamma (2 - (((σ : ℂ) + (τ : ℂ) * Complex.I) / 2))‖ /
        ‖Complex.Gamma (1 + (((σ : ℂ) + (τ : ℂ) * Complex.I) / 2))‖) ^ (20 : ℕ)
        ≤ C * (1 + |τ| / 2) ^ (20 * (1 - σ)) := by
  obtain ⟨K, hKpos, hK⟩ := gammaRatioStripUpper
  refine ⟨K ^ (20 : ℕ), by positivity, ?_⟩
  intro σ τ hσ1 hσ2
  have hx : (0 : ℝ) ≤ 1 + |τ| / 2 := by positivity
  have hR : 0 ≤ ‖Complex.Gamma (2 - (((σ : ℂ) + (τ : ℂ) * Complex.I) / 2))‖ /
      ‖Complex.Gamma (1 + (((σ : ℂ) + (τ : ℂ) * Complex.I) / 2))‖ :=
    div_nonneg (norm_nonneg _) (norm_nonneg _)
  calc (‖Complex.Gamma (2 - (((σ : ℂ) + (τ : ℂ) * Complex.I) / 2))‖ /
        ‖Complex.Gamma (1 + (((σ : ℂ) + (τ : ℂ) * Complex.I) / 2))‖) ^ (20 : ℕ)
      ≤ (K * (1 + |τ| / 2) ^ (1 - σ)) ^ (20 : ℕ) :=
        pow_le_pow_left₀ hR (hK σ τ hσ1 hσ2) 20
    _ = K ^ (20 : ℕ) * (1 + |τ| / 2) ^ (20 * (1 - σ)) := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast ((1 + |τ| / 2) ^ (1 - σ)) 20]
        rw [← Real.rpow_mul hx]
        ring_nf

end Work.FIArea6Hecke.R
