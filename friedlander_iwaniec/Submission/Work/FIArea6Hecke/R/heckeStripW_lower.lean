import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeStripWBoundDefs
import Submission.Work.FIArea6Hecke.R.gammaRatioStripLower
import Submission.Work.FIArea6Hecke.R.clogLowerStrip

namespace Work.FIArea6Hecke.R

lemma heckeStripW_cpow_norm (d : ℕ) (hd : 1 ≤ d) (w : ℂ) :
    ‖(((4 * (d : ℝ)) ^ (20 : ℕ) : ℝ) : ℂ) ^ (1 - w)‖ =
      (4 * (d : ℝ)) ^ (20 * (1 - w.re)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hpos : (0 : ℝ) < (4 * (d : ℝ)) ^ (20 : ℕ) := by positivity
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (1 - w).re = 1 - w.re := by simp
  rw [hre, ← Real.rpow_natCast (4 * (d : ℝ)) 20]
  exact (Real.rpow_mul (by positivity) (20 : ℝ) (1 - w.re)).symm

theorem heckeStripW_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (σ τ : ℝ), 1 / 2 ≤ σ → σ ≤ 1 →
      c * ((4 * (d : ℝ)) * (2 + |τ|)) ^ (20 * (1 - σ)) *
          (Real.log (4 * (d : ℝ) * (2 + |τ|))) ^ (8 : ℕ) ≤
        ‖Work.FIArea6Hecke.R.heckeStripW d ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ := by
  obtain ⟨c₁, hc₁pos, hc₁⟩ := gammaRatioStripLower
  refine ⟨c₁ * (1 / 2) ^ (8 : ℕ), by positivity, ?_⟩
  intro d hd σ τ hσ1 hσ2
  set z : ℂ := (σ : ℂ) + (τ : ℂ) * Complex.I with hz
  have hzre : z.re = σ := by rw [hz]; simp
  have hzim : z.im = τ := by rw [hz]; simp
  have hgam := hc₁ σ τ hσ1 hσ2
  rw [← hz] at hgam
  have hlog := clogLowerStrip d hd z (by rw [hzre]; linarith) (by rw [hzre]; linarith)
  rw [hzim] at hlog
  set L : ℝ := Real.log (4 * (d : ℝ) * (2 + |τ|)) with hL
  have hLpos : 0 < L := by
    rw [hL]
    apply Real.log_pos
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h2t : (2 : ℝ) ≤ 2 + |τ| := by linarith [abs_nonneg τ]
    nlinarith
  have hlog' : (1 / 2) * L ≤ ‖Complex.log (((4 * (d : ℝ)) : ℂ) * (z + 2))‖ := by
    rw [hL]; exact hlog
  have hlog8 : ((1 / 2) * L) ^ (8 : ℕ)
      ≤ ‖Complex.log (((4 * (d : ℝ)) : ℂ) * (z + 2))‖ ^ (8 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hlog' 8
  have hnorm : ‖heckeStripW d z‖ =
      (4 * (d : ℝ)) ^ (20 * (1 - σ)) *
        (‖Complex.Gamma (2 - z / 2)‖ / ‖Complex.Gamma (1 + z / 2)‖) ^ (20 : ℕ) *
        ‖Complex.log (((4 * (d : ℝ)) : ℂ) * (z + 2))‖ ^ (8 : ℕ) := by
    rw [heckeStripW]
    simp only [norm_mul, norm_pow, norm_div]
    rw [heckeStripW_cpow_norm d hd, hzre]
  set rt : ℝ := ‖Complex.Gamma (2 - z / 2)‖ / ‖Complex.Gamma (1 + z / 2)‖ with hrt
  have hrtsq : c₁ * (2 + |τ|) ^ (20 * (1 - σ)) ≤ rt ^ (20 : ℕ) := by
    rw [hrt]; exact hgam
  have hlhs_eq : c₁ * (1 / 2) ^ (8 : ℕ) * ((4 * (d : ℝ)) * (2 + |τ|)) ^ (20 * (1 - σ))
        * L ^ (8 : ℕ)
      = (4 * (d : ℝ)) ^ (20 * (1 - σ)) * (c₁ * (2 + |τ|) ^ (20 * (1 - σ)))
        * ((1 / 2) ^ (8 : ℕ) * L ^ (8 : ℕ)) := by
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * (d : ℝ))
      (by positivity : (0 : ℝ) ≤ 2 + |τ|)]
    ring
  have hmid : (4 * (d : ℝ)) ^ (20 * (1 - σ)) * (c₁ * (2 + |τ|) ^ (20 * (1 - σ)))
        * ((1 / 2) ^ (8 : ℕ) * L ^ (8 : ℕ))
      ≤ (4 * (d : ℝ)) ^ (20 * (1 - σ)) * rt ^ (20 : ℕ)
        * ‖Complex.log (((4 * (d : ℝ)) : ℂ) * (z + 2))‖ ^ (8 : ℕ) := by
    have hA : 0 ≤ (4 * (d : ℝ)) ^ (20 * (1 - σ)) := Real.rpow_nonneg (by positivity) _
    have h2 : (1 / 2) ^ (8 : ℕ) * L ^ (8 : ℕ)
        ≤ ‖Complex.log (((4 * (d : ℝ)) : ℂ) * (z + 2))‖ ^ (8 : ℕ) := by
      rw [← mul_pow]; exact hlog8
    have h3 : 0 ≤ (1 / 2) ^ (8 : ℕ) * L ^ (8 : ℕ) := by positivity
    have h4 : 0 ≤ (4 * (d : ℝ)) ^ (20 * (1 - σ)) * rt ^ (20 : ℕ) := by
      apply mul_nonneg hA; positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hrtsq hA) h2 h3 h4
  calc c₁ * (1 / 2) ^ (8 : ℕ) * ((4 * (d : ℝ)) * (2 + |τ|)) ^ (20 * (1 - σ)) * L ^ (8 : ℕ)
      = (4 * (d : ℝ)) ^ (20 * (1 - σ)) * (c₁ * (2 + |τ|) ^ (20 * (1 - σ)))
          * ((1 / 2) ^ (8 : ℕ) * L ^ (8 : ℕ)) := hlhs_eq
    _ ≤ (4 * (d : ℝ)) ^ (20 * (1 - σ)) * rt ^ (20 : ℕ)
          * ‖Complex.log (((4 * (d : ℝ)) : ℂ) * (z + 2))‖ ^ (8 : ℕ) := hmid
    _ = ‖heckeStripW d z‖ := hnorm.symm

end Work.FIArea6Hecke.R
