import Mathlib

namespace Work.WilE3.MPsi

set_option autoImplicit false

/-- Real-`rpow` bookkeeping for the lower bound on `P = ∏ g`: from `(A ρ)^s ≤ Φ ≤ P^(4q+1)`,
`A > 0`, `0 < ρ ≤ 1`, `P ≥ 0`, `Φ ≥ 0`, `0 < s`, `s ≤ Kexp`, deduce
`A^(s/(4q+1)) * ρ^Kexp ≤ P`. -/
theorem rpow_P_bound {A ρ Φ P s : ℝ} {Kexp q : ℕ}
    (hA : 0 < A) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hP : 0 ≤ P) (hΦ0 : 0 ≤ Φ)
    (hs : s ≤ (Kexp : ℝ)) (hqs : 0 < s)
    (h1 : (A * ρ) ^ s ≤ Φ) (h2 : Φ ≤ P ^ (4 * q + 1)) :
    A ^ (s / (4 * q + 1)) * ρ ^ Kexp ≤ P := by
  -- `N` is the (real) degree `4q+1`, appearing both as the exponent denominator and as the
  -- exponent of `P`.
  set N : ℝ := 4 * (q : ℝ) + 1 with hN
  have hNpos : 0 < N := by rw [hN]; have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q; linarith
  have hN1 : 1 ≤ N := by rw [hN]; have : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q; linarith
  have hcast : ((4 * q + 1 : ℕ) : ℝ) = N := by rw [hN]; push_cast; ring
  have hAρ : 0 ≤ A * ρ := le_of_lt (mul_pos hA hρ)
  -- Combine the two hypotheses into `(A ρ)^s ≤ P^N`, `P^N` being an `rpow`.
  have h12 : (A * ρ) ^ s ≤ P ^ N := by
    have h := le_trans h1 h2
    rw [← Real.rpow_natCast P (4 * q + 1), hcast] at h
    exact h
  -- Raise both sides to the positive power `1/N`.
  have hraise : ((A * ρ) ^ s) ^ (1 / N) ≤ (P ^ N) ^ (1 / N) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hAρ s) h12 (one_div_nonneg.mpr hNpos.le)
  have hlhs : ((A * ρ) ^ s) ^ (1 / N) = (A * ρ) ^ (s / N) := by
    rw [← Real.rpow_mul hAρ s (1 / N), one_div, div_eq_mul_inv]
  have hrhs : (P ^ N) ^ (1 / N) = P := by
    rw [← Real.rpow_mul hP N (1 / N)]
    have hNN : N * (1 / N) = 1 := by rw [one_div, mul_inv_cancel₀ (ne_of_gt hNpos)]
    rw [hNN, Real.rpow_one]
  have hAρ_le : (A * ρ) ^ (s / N) ≤ P := by
    rw [hlhs, hrhs] at hraise
    exact hraise
  -- Since `ρ ≤ 1` and `Kexp ≥ s ≥ s/N`, the nat power `ρ^Kexp` is dominated by `ρ^(s/N)`.
  have hsN_le : s / N ≤ (Kexp : ℝ) := by
    have hsN_s : s / N ≤ s := (div_le_iff₀ hNpos).mpr (le_mul_of_one_le_right hqs.le hN1)
    exact le_trans hsN_s hs
  have hρK : ρ ^ Kexp ≤ ρ ^ (s / N) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 hsN_le
    rwa [← Real.rpow_natCast ρ Kexp]
  have hmono : A ^ (s / N) * ρ ^ Kexp ≤ A ^ (s / N) * ρ ^ (s / N) :=
    mul_le_mul_of_nonneg_left hρK (Real.rpow_nonneg hA.le _)
  calc
    A ^ (s / N) * ρ ^ Kexp ≤ A ^ (s / N) * ρ ^ (s / N) := hmono
    _ = (A * ρ) ^ (s / N) := (Real.mul_rpow hA.le hρ.le).symm
    _ ≤ P := hAρ_le

end Work.WilE3.MPsi
