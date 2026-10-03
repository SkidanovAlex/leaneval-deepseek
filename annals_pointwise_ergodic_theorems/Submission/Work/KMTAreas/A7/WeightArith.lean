import Mathlib

namespace Work.KMTAreas.A7

/-- Elementary arithmetic core (used by `weightArith_exp` and `WeightArith`):

for `A ≥ 0` and any real `x`,  `A * 2^x - 2^{4x} ≤ A * A^{1/3}`.

The point of the cutoff at the exponent `1/3` is that the two terms
`A · 2^x` and `2^{4x}` are never simultaneously large: as long as the
negative term is non-positive the bound is trivial, and once the negative
term goes negative `A ≤ 2^{3x}`, i.e. `2^x ≤ A^{1/3}`. -/
lemma weightArith_rpowCore (A x : ℝ) (hA : 0 ≤ A) :
    A * (2:ℝ)^x - (2:ℝ)^(4*x) ≤ A * A^((1:ℝ)/3) := by
  by_cases h : (2:ℝ)^(3*x) ≤ A
  · have h2x : (2:ℝ)^x ≤ A^((1:ℝ)/3) := by
      have h1 := Real.rpow_le_rpow (show (0:ℝ) ≤ (2:ℝ)^(3*x) by positivity) h
        (show (0:ℝ) ≤ (1:ℝ)/3 by norm_num)
      have he : ((2:ℝ)^(3*x))^((1:ℝ)/3) = (2:ℝ)^x := by
        rw [← Real.rpow_mul (show (0:ℝ) ≤ (2:ℝ) by norm_num) (3*x) ((1:ℝ)/3)]
        congr 1; ring
      rwa [he] at h1
    have h3 := mul_le_mul_of_nonneg_left h2x hA
    have h4 : (0:ℝ) ≤ (2:ℝ)^(4*x) := Real.rpow_nonneg (by norm_num) _
    linarith
  · have hlt : A < (2:ℝ)^(3*x) := not_le.mp h
    have hfac : A * (2:ℝ)^x - (2:ℝ)^(4*x) = (2:ℝ)^x * (A - (2:ℝ)^(3*x)) := by
      rw [mul_sub, ← Real.rpow_add (show (0:ℝ) < 2 by norm_num) x (3*x)]
      ring_nf
    rw [hfac]
    apply le_trans _ (mul_nonneg hA (Real.rpow_nonneg hA _))
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (by norm_num) x) (by linarith)

/-- The exponent bookkeeping behind `WeightArith`: the loss coming from the
`A · 2^{ρL}` factor is absorbed by `A · A^{1/3}`, and the exponential gain
`2^{-2^{L/C₀}}` controls the term `-2^{4ρL}`, which is all that is needed since
`ρ ≤ 1/(4C₀)` and `L ≥ 0` give `4ρL ≤ L/C₀`. -/
lemma weightArith_exp (A ρ L : ℝ) (C₀ : ℕ) (hA : 0 ≤ A) (hρ : 0 < ρ) (hC₀ : 1 ≤ C₀)
    (hρle : ρ ≤ 1 / (4 * (C₀ : ℝ))) (hL : 0 ≤ L) :
    A * (2:ℝ)^(ρ*L) - (2:ℝ)^(L/(C₀:ℝ)) + 2
      ≤ A * A^((1:ℝ)/3) + 7 + (A+2)*ρ*L := by
  have hC0pos : (0:ℝ) < (C₀:ℝ) := by
    have h1 : (1:ℝ) ≤ (C₀:ℝ) := by exact_mod_cast hC₀
    linarith
  have h4rho : 4 * ρ ≤ 1 / (C₀:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hρle (show (0:ℝ) ≤ 4 by norm_num)
    have he : 4 * (1 / (4 * (C₀:ℝ))) = 1 / (C₀:ℝ) := by
      field_simp
    rw [he] at h
    exact h
  have hxL : 4 * ρ * L ≤ L / (C₀:ℝ) := by
    have h := mul_le_mul_of_nonneg_right h4rho hL
    rw [one_div] at h
    simpa [div_eq_mul_inv, mul_comm] using h
  have hpow2 : (2:ℝ)^(4*ρ*L) ≤ (2:ℝ)^(L/(C₀:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hxL
  have hcore : A * (2:ℝ)^(ρ*L) - (2:ℝ)^(4*ρ*L) ≤ A * A^((1:ℝ)/3) := by
    have hc := weightArith_rpowCore A (ρ*L) hA
    have h4eq : (2:ℝ)^(4*(ρ*L)) = (2:ℝ)^(4*ρ*L) := by
      rw [show 4*(ρ*L) = 4*ρ*L by ring]
    rwa [h4eq] at hc
  have hnn : (0:ℝ) ≤ (A+2)*ρ*L := by positivity
  linarith

theorem WeightArith (A ρ L D : ℝ) (C₀ : ℕ) (hA : 0 ≤ A) (hρ : 0 < ρ) (hC₀ : 1 ≤ C₀)
    (hρle : ρ ≤ 1 / (4 * (C₀ : ℝ))) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    (1 + L) ^ A * (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * L)) * D
        * (2 : ℝ) ^ (-((2 : ℝ) ^ (L / (C₀ : ℝ))) + 2)
      ≤ (8 * max D 1 * (2 : ℝ) ^ (A * A ^ ((1 : ℝ) / 3) + 4))
        * ((1 + L) ^ (A + 2) * (2 : ℝ) ^ ((A + 2) * ρ * L)) := by
  have hExp := weightArith_exp A ρ L C₀ hA hρ hC₀ hρle hL
  have hc : (0:ℝ) ≤ max D 1 := le_trans hD (le_max_left D 1)
  have hDle : D ≤ max D 1 := le_max_left D 1
  have hX : (0:ℝ) ≤ (1+L)^A * (2:ℝ)^(A * (2:ℝ)^(ρ*L)) := by positivity
  have h1 : (1+L)^A * (2:ℝ)^(A * (2:ℝ)^(ρ*L)) * D
      ≤ (1+L)^A * (2:ℝ)^(A * (2:ℝ)^(ρ*L)) * max D 1 :=
    mul_le_mul_of_nonneg_left hDle hX
  have hZ : (0:ℝ) ≤ (2:ℝ)^(-((2:ℝ)^(L/(C₀:ℝ))) + 2) := by positivity
  have h2 : ((1+L)^A * (2:ℝ)^(A * (2:ℝ)^(ρ*L)) * D) * (2:ℝ)^(-((2:ℝ)^(L/(C₀:ℝ))) + 2)
      ≤ ((1+L)^A * (2:ℝ)^(A * (2:ℝ)^(ρ*L)) * max D 1) * (2:ℝ)^(-((2:ℝ)^(L/(C₀:ℝ))) + 2) :=
    mul_le_mul_of_nonneg_right h1 hZ
  have hQ : (1+L)^A * (2:ℝ)^(A * (2:ℝ)^(ρ*L)) * (2:ℝ)^(-((2:ℝ)^(L/(C₀:ℝ))) + 2)
      ≤ 8 * (2:ℝ)^(A*A^((1:ℝ)/3)+4) * ((1+L)^(A+2) * (2:ℝ)^((A+2)*ρ*L)) := by
    have hLHS : (1+L)^A * (2:ℝ)^(A * (2:ℝ)^(ρ*L)) * (2:ℝ)^(-((2:ℝ)^(L/(C₀:ℝ))) + 2)
        = (1+L)^A * (2:ℝ)^(A * (2:ℝ)^(ρ*L) - (2:ℝ)^(L/(C₀:ℝ)) + 2) := by
      rw [mul_assoc]
      have heq : (2:ℝ)^(A * (2:ℝ)^(ρ*L)) * (2:ℝ)^(-((2:ℝ)^(L/(C₀:ℝ))) + 2)
          = (2:ℝ)^(A * (2:ℝ)^(ρ*L) - (2:ℝ)^(L/(C₀:ℝ)) + 2) := by
        rw [← Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
        congr 1
        ring
      rw [heq]
    rw [hLHS]
    have hb : (1+L)^A ≤ (1+L)^(A+2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hpow : (2:ℝ)^(A * (2:ℝ)^(ρ*L) - (2:ℝ)^(L/(C₀:ℝ)) + 2)
        ≤ (2:ℝ)^(A*A^((1:ℝ)/3) + 7 + (A+2)*ρ*L) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
    have h8 : (8:ℝ) * (2:ℝ)^(A*A^((1:ℝ)/3)+4) * (2:ℝ)^((A+2)*ρ*L)
        = (2:ℝ)^(A*A^((1:ℝ)/3) + 7 + (A+2)*ρ*L) := by
      rw [show (8:ℝ) = (2:ℝ)^(3:ℝ) by norm_num]
      rw [← Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
      rw [← Real.rpow_add (show (0:ℝ) < 2 by norm_num)]
      congr 1
      ring
    calc (1+L)^A * (2:ℝ)^(A * (2:ℝ)^(ρ*L) - (2:ℝ)^(L/(C₀:ℝ)) + 2)
        ≤ (1+L)^(A+2) * (2:ℝ)^(A * (2:ℝ)^(ρ*L) - (2:ℝ)^(L/(C₀:ℝ)) + 2) :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ ≤ (1+L)^(A+2) * (2:ℝ)^(A*A^((1:ℝ)/3) + 7 + (A+2)*ρ*L) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 8 * (2:ℝ)^(A*A^((1:ℝ)/3)+4) * ((1+L)^(A+2) * (2:ℝ)^((A+2)*ρ*L)) := by
          rw [← h8]
          ring
  calc ((1+L)^A * (2:ℝ)^(A * (2:ℝ)^(ρ*L)) * D) * (2:ℝ)^(-((2:ℝ)^(L/(C₀:ℝ))) + 2)
      ≤ ((1+L)^A * (2:ℝ)^(A * (2:ℝ)^(ρ*L)) * max D 1) * (2:ℝ)^(-((2:ℝ)^(L/(C₀:ℝ))) + 2) := h2
    _ = ((1+L)^A * (2:ℝ)^(A * (2:ℝ)^(ρ*L)) * (2:ℝ)^(-((2:ℝ)^(L/(C₀:ℝ))) + 2)) * max D 1 := by ring
    _ ≤ (8 * (2:ℝ)^(A*A^((1:ℝ)/3)+4) * ((1+L)^(A+2) * (2:ℝ)^((A+2)*ρ*L))) * max D 1 :=
        mul_le_mul_of_nonneg_right hQ hc
    _ = (8 * max D 1 * (2:ℝ)^(A*A^((1:ℝ)/3)+4)) * ((1+L)^(A+2) * (2:ℝ)^((A+2)*ρ*L)) := by ring

end Work.KMTAreas.A7
