import Mathlib

namespace Work.Peluse.Prop36SW

theorem roundWindowGe {C₀ γ : ℝ} {K M₁ M₂ : ℕ} (hC₀ : 0 < C₀) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hK : 1 ≤ K) (hM₂ : 1 ≤ M₂) (hM₂M₁ : M₂ ≤ M₁)
    (hnd : C₀ ^ (K + 1) * γ ^ (-((K * (K + 1) : ℕ) : ℤ)) ≤ (M₂ : ℝ)) :
    M₂ ≤ (⌊(γ ^ K / C₀) * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat := by
  -- Write `U := C₀ / γ ^ K`.  The hypothesis says `U ^ (K+1) ≤ M₂`, while the conclusion needs the
  -- *window* `γ ^ K / C₀ * M₁ = M₁ / U` to be `≥ 1`, i.e. `U ≤ M₁`.
  have hM₁ : 1 ≤ M₁ := le_trans hM₂ hM₂M₁
  have hUpow : (C₀ / γ ^ K) ^ (K + 1) ≤ (M₂ : ℝ) := by
    have hT : (C₀ / γ ^ K) ^ (K + 1)
        = C₀ ^ (K + 1) * γ ^ (-((K * (K + 1) : ℕ) : ℤ)) := by
      have hz : γ ^ (-((K * (K + 1) : ℕ) : ℤ)) = (γ ^ (K * (K + 1)))⁻¹ := by
        rw [zpow_neg, zpow_natCast]
      rw [hz, div_pow, ← pow_mul, div_eq_mul_inv]
    rw [hT]
    exact hnd
  have hM₂M₁' : (M₂ : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast hM₂M₁
  -- `U ≤ M₁`, because `U ≤ max 1 (U ^ (K+1))` while `1 ≤ M₁` and `U ^ (K+1) ≤ M₂ ≤ M₁`.
  have hUle : C₀ / γ ^ K ≤ (M₁ : ℝ) := by
    rcases le_or_gt (C₀ / γ ^ K) 1 with h | h
    · exact le_trans h (by exact_mod_cast hM₁)
    · have hUU : (C₀ / γ ^ K) ^ 1 ≤ (C₀ / γ ^ K) ^ (K + 1) :=
        pow_le_pow_right₀ (le_of_lt h) (by omega)
      have hUU' : C₀ / γ ^ K ≤ (C₀ / γ ^ K) ^ (K + 1) := by simpa using hUU
      exact le_trans hUU' (le_trans hUpow hM₂M₁')
  have hprod : (1 : ℝ) ≤ (γ ^ K / C₀) * (M₁ : ℝ) := by
    have h1 : C₀ ≤ (M₁ : ℝ) * γ ^ K := (div_le_iff₀ (pow_pos hγ0 K)).mp hUle
    rw [show (γ ^ K / C₀) * (M₁ : ℝ) = ((M₁ : ℝ) * γ ^ K) / C₀ by ring]
    rw [one_le_div hC₀]
    linarith
  have hx : (M₂ : ℝ) ≤ (γ ^ K / C₀) * (M₁ : ℝ) * (M₂ : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hprod (by positivity : (0 : ℝ) ≤ (M₂ : ℝ))
    simpa using h
  have hfloor : (M₂ : ℤ) ≤ ⌊(γ ^ K / C₀) * (M₁ : ℝ) * (M₂ : ℝ)⌋ := Int.le_floor.mpr hx
  have h2 := Int.toNat_le_toNat hfloor
  rwa [Int.toNat_natCast] at h2

end Work.Peluse.Prop36SW
