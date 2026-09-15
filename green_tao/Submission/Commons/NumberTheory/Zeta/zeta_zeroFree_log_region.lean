import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFreeRegion_largeHeight

namespace Commons.NumberTheory.Zeta

theorem zeta_zeroFree_log_region :
    ∃ c : ℝ, 0 < c ∧ ∃ H : ℝ, (5 : ℝ) ≤ H ∧ ∀ t : ℝ, H ≤ |t| →
      ∀ σ : ℝ, (1 - c / (Real.log (|t| + 3) + 1)) ≤ σ →
        riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
  -- The large-height de la Vallée Poussin zero-free region (proved by a colleague):
  --   ∃ c₀ > 0, ∃ T₀ > 0, ∀ t (T₀ ≤ |t|) ∀ σ (1 - c₀/log(|t|+3) ≤ σ):
  --     ζ(σ + I·t) ≠ 0.
  rcases zeta_zeroFreeRegion_largeHeight with ⟨c₀, T₀, hc₀, hT₀, hmain⟩
  -- Take the same constant c₀ (positive) and any height at least both 5 and T₀.
  refine ⟨c₀, hc₀, max 5 T₀, le_max_left _ _, ?_⟩
  intro t ht σ hσ
  have htT : T₀ ≤ |t| := le_trans (le_max_right 5 T₀) ht
  -- From our (narrower) region to the colleague's (wider) region:
  --   σ ≥ 1 - c₀/(L+1) ≥ 1 - c₀/L  with  L = log(|t|+3).
  let L : ℝ := Real.log (|t| + 3)
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by nlinarith [abs_nonneg t])
  have hle : c₀ / (L + 1) ≤ c₀ / L := by
    rw [div_le_div_iff₀ (by positivity : 0 < L + 1) hLpos]
    have h : c₀ * L ≤ c₀ * (L + 1) := by nlinarith [hc₀]
    simpa [mul_add] using h
  have h1 : (1 - c₀ / L) ≤ 1 - c₀ / (L + 1) := by linarith
  have hσ' : 1 - c₀ / L ≤ σ := le_trans h1 (by simpa [L] using hσ)
  have hz := hmain t htT σ (by simpa [L] using hσ')
  -- Argument shape: (σ : ℂ) + (t : ℂ) * I  versus  (σ : ℂ) + I * (t : ℂ).
  have harg : ((σ : ℂ) + (t : ℂ) * Complex.I) = ((σ : ℂ) + Complex.I * (t : ℂ)) := by
    ring
  simpa [harg] using hz

end Commons.NumberTheory.Zeta
