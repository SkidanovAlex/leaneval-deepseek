import Mathlib

namespace Work.ZeroFreeTables.XY

/-- Pure complex-arithmetic identities used when locating the zeros of the
auxiliary function `XY` relative to the line `Re s = 1`. -/
theorem ArgIdentities {σ L a lam γ : ℝ} (hσ : σ = 1 + a/L) (hL : L ≠ 0) {ρ : ℂ}
    (hre : ρ.re = 1 - lam/L) (him : ρ.im = γ) :
    ((((σ:ℂ) + (γ:ℂ)*Complex.I) - ρ) * ((L:ℝ):ℂ) = ((a+lam:ℝ):ℂ))
  ∧ ((((σ:ℂ) + (γ:ℂ)*Complex.I) - starRingEnd ℂ ρ) * ((L:ℝ):ℂ)
      = ((a+lam:ℝ):ℂ) + (((2*γ*L:ℝ)):ℂ)*Complex.I)
  ∧ ((((σ:ℂ) + 3*(γ:ℂ)*Complex.I) - ρ) * ((L:ℝ):ℂ)
      = ((a+lam:ℝ):ℂ) + (((2*γ*L:ℝ)):ℂ)*Complex.I)
  ∧ ((((σ:ℂ) + 3*(γ:ℂ)*Complex.I) - starRingEnd ℂ ρ) * ((L:ℝ):ℂ)
      = ((a+lam:ℝ):ℂ) + (((4*γ*L:ℝ)):ℂ)*Complex.I)
  ∧ ((((σ:ℂ)) - 1) * ((L:ℝ):ℂ) = ((a:ℝ):ℂ))
  ∧ ((((σ:ℂ) + 2*(γ:ℂ)*Complex.I) - 1) * ((L:ℝ):ℂ)
      = ((a:ℝ):ℂ) + (((2*γ*L:ℝ)):ℂ)*Complex.I)
  ∧ ((((σ:ℂ) + 4*(γ:ℂ)*Complex.I) - 1) * ((L:ℝ):ℂ)
      = ((a:ℝ):ℂ) + (((4*γ*L:ℝ)):ℂ)*Complex.I) := by
  have hρ : ρ = ((1 - lam/L : ℝ) : ℂ) + (γ:ℂ) * Complex.I := by
    rw [← Complex.re_add_im ρ, hre, him]
  have hρc : starRingEnd ℂ ρ = ((1 - lam/L : ℝ) : ℂ) - (γ:ℂ) * Complex.I := by
    rw [hρ]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hLc : ((L:ℝ):ℂ) ≠ 0 := by exact_mod_cast hL
  subst hσ
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;>
    · try rw [hρc]
      try rw [hρ]
      push_cast
      field_simp
      ring

end Work.ZeroFreeTables.XY
