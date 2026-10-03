import Mathlib

namespace Work.Peluse.SwapA

/-- The nondegeneracy hypothesis of the heart gives `M₂` large: from
`(M₁M₂)^e ≤ C(γηD)^e M₂` and `D ≤ C(γη)^e (M₁M₂)` (with `0 < γ, η ≤ 1`, `0 < C ≤ 1`, `e ≥ 1`)
one gets `1/M₂ ≤ C γ^e`. -/
theorem inv_le_of_nondegenerate {γ η M₁ M₂ D C : ℝ} {e : ℕ}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hC0 : 0 < C) (hC1 : C ≤ 1) (he : 1 ≤ e) (hD1 : 1 ≤ D)
    (hM₂1 : 1 ≤ M₂) (hM₂M₁ : M₂ ≤ M₁)
    (hD : D ≤ C * (γ * η) ^ e * (M₁ * M₂))
    (hnd : (M₁ * M₂) ^ e ≤ C * (γ * η * D) ^ e * M₂) :
    M₂⁻¹ ≤ C * γ ^ e := by
  have hγη_pos : 0 < γ * η := mul_pos hγ0 hη0
  have hM₂pos : 0 < M₂ := by linarith
  have hM₁pos : 0 < M₁ := by linarith
  have hDpos : 0 < D := by linarith
  have hApos : 0 < (M₁ * M₂) ^ e := pow_pos (mul_pos hM₁pos hM₂pos) e
  have hγηD_pos : 0 < γ * η * D := mul_pos hγη_pos hDpos
  -- `D ≤ C (γη)^e (M₁M₂)` multiplied by `γη > 0` gives `γηD ≤ C (γη)^{e+1} (M₁M₂)`.
  have hA : γ * η * D ≤ C * (γ * η) ^ (e + 1) * (M₁ * M₂) := by
    calc γ * η * D ≤ γ * η * (C * (γ * η) ^ e * (M₁ * M₂)) :=
          mul_le_mul_of_nonneg_left hD (le_of_lt hγη_pos)
      _ = C * (γ * η) ^ (e + 1) * (M₁ * M₂) := by rw [pow_succ']; ring
  have hB : (γ * η * D) ^ e ≤ (C * (γ * η) ^ (e + 1) * (M₁ * M₂)) ^ e :=
    pow_le_pow_left₀ (le_of_lt hγηD_pos) hA e
  have hCexpand : (C * (γ * η) ^ (e + 1) * (M₁ * M₂)) ^ e
      = C ^ e * (γ * η) ^ ((e + 1) * e) * (M₁ * M₂) ^ e := by
    rw [mul_pow, mul_pow, ← pow_mul]
  -- Insert the bound for `(γηD)^e` into `hnd` and cancel `(M₁M₂)^e > 0`.
  have hstep : (M₁ * M₂) ^ e
      ≤ C * (C ^ e * (γ * η) ^ ((e + 1) * e) * (M₁ * M₂) ^ e) * M₂ := by
    calc (M₁ * M₂) ^ e ≤ C * (γ * η * D) ^ e * M₂ := hnd
      _ ≤ C * (C * (γ * η) ^ (e + 1) * (M₁ * M₂)) ^ e * M₂ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB (le_of_lt hC0)) (by linarith)
      _ = C * (C ^ e * (γ * η) ^ ((e + 1) * e) * (M₁ * M₂) ^ e) * M₂ := by rw [hCexpand]
  have hstep2 : 1 * (M₁ * M₂) ^ e
      ≤ (C * C ^ e * (γ * η) ^ ((e + 1) * e) * M₂) * (M₁ * M₂) ^ e := by
    rw [one_mul]
    calc (M₁ * M₂) ^ e ≤ C * (C ^ e * (γ * η) ^ ((e + 1) * e) * (M₁ * M₂) ^ e) * M₂ := hstep
      _ = (C * C ^ e * (γ * η) ^ ((e + 1) * e) * M₂) * (M₁ * M₂) ^ e := by ring
  have hdivide : 1 ≤ C * C ^ e * (γ * η) ^ ((e + 1) * e) * M₂ :=
    le_of_mul_le_mul_right hstep2 hApos
  -- Bound the surviving constants: `C^{e+1} (γη)^{(e+1)e} ≤ C γ^e`.
  have hγη_le_one : γ * η ≤ 1 := by nlinarith [hγ1, hη1, le_of_lt hγ0, le_of_lt hη0]
  have hCpow : C ^ (e + 1) ≤ C := by
    calc C ^ (e + 1) ≤ C ^ 1 := pow_le_pow_of_le_one (le_of_lt hC0) hC1 (by omega)
      _ = C := pow_one C
  have hγηpow : (γ * η) ^ ((e + 1) * e) ≤ γ ^ e := by
    have h1 : (γ * η) ^ ((e + 1) * e) ≤ (γ * η) ^ e :=
      pow_le_pow_of_le_one (le_of_lt hγη_pos) hγη_le_one (by nlinarith [he])
    have h2 : (γ * η) ^ e ≤ γ ^ e :=
      pow_le_pow_left₀ (le_of_lt hγη_pos) (mul_le_of_le_one_right (le_of_lt hγ0) hη1) e
    linarith
  have hprod : C ^ (e + 1) * (γ * η) ^ ((e + 1) * e) ≤ C * γ ^ e :=
    mul_le_mul hCpow hγηpow (by positivity) (le_of_lt hC0)
  have hkey : 1 ≤ C * γ ^ e * M₂ := by
    have h1 : C * C ^ e * (γ * η) ^ ((e + 1) * e) ≤ C * γ ^ e := by
      have h2 : C * C ^ e = C ^ (e + 1) := by rw [pow_succ]; ring
      rw [h2]; exact hprod
    calc 1 ≤ C * C ^ e * (γ * η) ^ ((e + 1) * e) * M₂ := hdivide
      _ ≤ C * γ ^ e * M₂ := mul_le_mul_of_nonneg_right h1 (by linarith)
  have h1 : (C * γ ^ e * M₂) * M₂⁻¹ = C * γ ^ e := by
    rw [mul_assoc (C * γ ^ e) M₂ M₂⁻¹, mul_inv_cancel₀ (ne_of_gt hM₂pos), mul_one]
  calc M₂⁻¹ = 1 * M₂⁻¹ := by rw [one_mul]
    _ ≤ (C * γ ^ e * M₂) * M₂⁻¹ := mul_le_mul_of_nonneg_right hkey (inv_nonneg.mpr (le_of_lt hM₂pos))
    _ = C * γ ^ e := h1

end Work.Peluse.SwapA
