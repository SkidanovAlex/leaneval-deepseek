import Mathlib

namespace Work.LinnikAreas.TuranOther

theorem cpowShiftRe (c : ℂ) {n : ℕ} (hn : n ≠ 0) (σ γ : ℝ) : (c * (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (γ : ℂ)))).re = (n : ℝ) ^ (-σ) * (c * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))).re := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hx : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hexp : -((σ : ℂ) + Complex.I * (γ : ℂ)) = (-(σ : ℂ)) + (-(Complex.I * (γ : ℂ))) := by ring
  have hcast : (n : ℂ) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx (-σ)]
    simp
  rw [hexp, Complex.cpow_add _ _ hn', hcast]
  rw [show c * ((((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * (γ : ℂ))))
        = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * (c * (n : ℂ) ^ (-(Complex.I * (γ : ℂ)))) by ring]
  rw [Complex.re_ofReal_mul]

end Work.LinnikAreas.TuranOther
