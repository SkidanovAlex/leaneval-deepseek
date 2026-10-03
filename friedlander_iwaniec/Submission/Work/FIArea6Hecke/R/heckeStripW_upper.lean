import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeStripWBoundDefs
import Submission.Work.FIArea5.S16Hecke.gammaLowerSharpVertical
import Submission.Work.FIArea6Hecke.R.heckeStripWLog8
import Submission.Work.FIArea6Hecke.R.heckeStripWGammaRatioPow

namespace Work.FIArea6Hecke.R

/-- Strip bound `1/2 ≤ re s ≤ 1` for the Phragmén–Lindelöf weight `heckeStripW`:
`‖heckeStripW d (σ+iτ)‖ ≤ C·(4d(2+|τ|))^{20(1-σ)}·log^8(4d(2+|τ|))` with an absolute `C`.

The three factors of `heckeStripW` are bounded separately:
`‖((4d)^20)^{1-z}‖ = (4d)^{20(1-σ)}` (`Complex.norm_cpow_eq_rpow_re_of_pos`), the `20`-th power
of the Gamma ratio is `≤ C·(1+|τ|/2)^{20(1-σ)}` (`heckeStripWGammaRatioPow`), and the `8`-th power
of the logarithm is `≤ 4^8·log^8(4d(2+|τ|))` (`heckeStripWLog8`); the product
`(4d)^{20(1-σ)}·(1+|τ|/2)^{20(1-σ)} = (4d(1+|τ|/2))^{20(1-σ)} ≤ (4d(2+|τ|))^{20(1-σ)}`
absorbs the `d`- and `τ`-powers. -/
theorem heckeStripW_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (σ τ : ℝ), 1 / 2 ≤ σ → σ ≤ 1 →
      ‖Work.FIArea6Hecke.R.heckeStripW d ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
        C * ((4 * (d : ℝ)) * (2 + |τ|)) ^ (20 * (1 - σ)) *
          (Real.log (4 * (d : ℝ) * (2 + |τ|))) ^ (8 : ℕ) := by
  obtain ⟨Cg, hCgpos, hCg⟩ := heckeStripWGammaRatioPow
  refine ⟨Cg * (4 : ℝ) ^ (8 : ℕ), by positivity, ?_⟩
  intro d hd σ τ hσ1 hσ2
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hbase : (0 : ℝ) < ((4 * (d : ℝ)) ^ (20 : ℕ) : ℝ) := by positivity
  -- (A) the complex-power factor
  have hA : ‖((((4 * (d : ℝ)) ^ (20 : ℕ) : ℝ)) : ℂ) ^ (1 - ((σ : ℂ) + (τ : ℂ) * Complex.I))‖
      = (4 * (d : ℝ)) ^ (20 * (1 - σ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hbase]
    have hz : (1 - ((σ : ℂ) + (τ : ℂ) * Complex.I)).re = 1 - σ := by simp
    rw [hz, ← Real.rpow_natCast (4 * (d : ℝ)) 20, ← Real.rpow_mul (by positivity)]
    norm_num
  have hR := hCg σ τ hσ1 hσ2
  have hL := heckeStripWLog8 d hd σ τ hσ1 hσ2
  have hCnneg : (0 : ℝ) ≤ Cg * (1 + |τ| / 2) ^ (20 * (1 - σ)) :=
    mul_nonneg hCgpos.le (Real.rpow_nonneg (by positivity) _)
  -- (B) the modulus splits as the product of the three factors
  have hdecomp : ‖heckeStripW d ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
      = (4 * (d : ℝ)) ^ (20 * (1 - σ)) *
        (‖Complex.Gamma (2 - (((σ : ℂ) + (τ : ℂ) * Complex.I)) / 2)‖ /
         ‖Complex.Gamma (1 + (((σ : ℂ) + (τ : ℂ) * Complex.I)) / 2)‖) ^ (20 : ℕ) *
        ‖Complex.log (((4 * (d : ℝ)) : ℂ) * (((σ : ℂ) + (τ : ℂ) * Complex.I) + 2))‖ ^ (8 : ℕ) := by
    rw [heckeStripW, norm_mul, norm_mul, norm_pow, norm_pow, norm_div, hA]
  calc ‖Work.FIArea6Hecke.R.heckeStripW d ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
      = (4 * (d : ℝ)) ^ (20 * (1 - σ)) *
          (‖Complex.Gamma (2 - (((σ : ℂ) + (τ : ℂ) * Complex.I)) / 2)‖ /
           ‖Complex.Gamma (1 + (((σ : ℂ) + (τ : ℂ) * Complex.I)) / 2)‖) ^ (20 : ℕ) *
          ‖Complex.log (((4 * (d : ℝ)) : ℂ) * (((σ : ℂ) + (τ : ℂ) * Complex.I) + 2))‖ ^ (8 : ℕ) :=
        hdecomp
    _ ≤ (4 * (d : ℝ)) ^ (20 * (1 - σ)) * (Cg * (1 + |τ| / 2) ^ (20 * (1 - σ))) *
          ((4 : ℝ) ^ (8 : ℕ) * (Real.log (4 * (d : ℝ) * (2 + |τ|))) ^ (8 : ℕ)) := by
        refine mul_le_mul (mul_le_mul le_rfl hR (by positivity) (by positivity)) hL
          (by positivity) ?_
        exact mul_nonneg (by positivity) hCnneg
    _ = (Cg * (4 : ℝ) ^ (8 : ℕ)) *
          ((4 * (d : ℝ)) ^ (20 * (1 - σ)) * (1 + |τ| / 2) ^ (20 * (1 - σ))) *
          (Real.log (4 * (d : ℝ) * (2 + |τ|))) ^ (8 : ℕ) := by ring
    _ ≤ (Cg * (4 : ℝ) ^ (8 : ℕ)) * (4 * (d : ℝ) * (2 + |τ|)) ^ (20 * (1 - σ)) *
          (Real.log (4 * (d : ℝ) * (2 + |τ|))) ^ (8 : ℕ) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCgpos.le (by positivity))
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        apply Real.rpow_le_rpow (by positivity)
        · nlinarith [abs_nonneg τ, hd0]
        · linarith

end Work.FIArea6Hecke.R
