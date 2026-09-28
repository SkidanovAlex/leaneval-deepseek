import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.Sig2.NN_ge_add_two

namespace Work.HP.MM2

open Work.HP

/-! ## Elementary helpers used by `bad_term_le` -/

/-- A nonzero integer vector has positive Euclidean norm. -/
private lemma eNorm_pos_btl {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) :
    0 < eNorm v := by
  rw [eNorm, Real.sqrt_pos]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv (funext h)
  refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
  have : (v i : ℝ) ≠ 0 := by exact_mod_cast hi
  positivity

/-- For nonnegative `a, b` one has `(max a b)^k ≤ a^k + b^k`. -/
private lemma max_pow_le_btl (a b : ℝ) (k : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (max a b) ^ k ≤ a ^ k + b ^ k := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; exact le_add_of_nonneg_left (pow_nonneg ha k)
  · rw [max_eq_left h]; exact le_add_of_nonneg_right (pow_nonneg hb k)

/-- Conversion of the `ν`-lower bound `c₁‖x‖^d ≤ ‖ν(x)‖` into the reciprocal-power
estimate `‖x‖^{n-1}/‖ν(x)‖ ≤ c₁⁻¹‖x‖^{(n:ℝ)-1-d}`. -/
private lemma rpow_div_le_btl (X W c₁ : ℝ) (d n : ℕ) (hX : 0 < X) (hc : 0 < c₁)
    (hW : c₁ * X ^ d ≤ W) (hn : 1 ≤ n) :
    X ^ (n - 1) / W ≤ c₁⁻¹ * X ^ ((n : ℝ) - 1 - d) := by
  have hWpos : 0 < W := lt_of_lt_of_le (mul_pos hc (pow_pos hX d)) hW
  rw [div_le_iff₀ hWpos]
  calc X ^ (n - 1) = X ^ (((n - 1 : ℕ)) : ℝ) := (Real.rpow_natCast X (n - 1)).symm
    _ = X ^ (((n : ℝ) - 1 - d) + (d : ℝ)) := by
          congr 1; push_cast [Nat.cast_sub hn]; ring
    _ = X ^ ((n : ℝ) - 1 - d) * X ^ (d : ℝ) := Real.rpow_add hX _ _
    _ = X ^ ((n : ℝ) - 1 - d) * X ^ d := by rw [Real.rpow_natCast]
    _ = c₁⁻¹ * X ^ ((n : ℝ) - 1 - d) * (c₁ * X ^ d) := by field_simp
    _ ≤ c₁⁻¹ * X ^ ((n : ℝ) - 1 - d) * W :=
          mul_le_mul_of_nonneg_left hW (by positivity)

/-- Per-vector arithmetic behind `Σ₂^{mix}`.  With `N = NN d n`, `𝔡₂(x) = dmin 2 {x}` and
`μ(x) = max A (C‖x‖/𝔡₂(x))`, one has, for `1 ≤ A`, `1 ≤ C`, `x ≠ 0` and `1 ≤ 𝔡₂(x)`,

`(A^{N-2} + A^{N-n-1} μ(x)^{n-1}) / ‖ν(x)‖ ≤ K·(2A^{N-2}/‖ν(x)‖ + A^{N-n-1}C^{n-1}‖x‖^{n-1-d})`.

Route: `(max a b)^{n-1} ≤ a^{n-1} + b^{n-1}`; `𝔡₂(x)^{n-1} ≥ 1` kills the `𝔡₂` in the denominator;
`A^{N-n-1}·A^{n-1} = A^{N-2}` because `n + 2 ≤ NN d n` (`Work.HP.Sig2.NN_ge_add_two`, so
`NN d n - n - 1 + (n - 1) = NN d n - 2` as natural numbers); and finally
`c₁‖x‖^d ≤ ‖ν(x)‖` (`Work.HP.eNorm_veronese_bounds`, `1 ≤ d`) turns the remaining
`‖x‖^{n-1}/‖ν(x)‖` into `≪ ‖x‖^{n-1-d}` with the constant `1/c₁` absorbed into `K`.  Note `d ≤ n`,
so the real exponent `(n:ℝ) - 1 - d` is `≥ -1`; when `d = n` it is `-1` and
`‖x‖^{n-1}/‖x‖^d = ‖x‖^{-1}` must be read as a real power (`Real.rpow`, use `x ≠ 0` for
`eNorm x > 0`).  Only import modules whose proofs are `sorry`-free. -/
theorem bad_term_le (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A C : ℝ) (x : Fin (n + 1) → ℤ),
      1 ≤ A → 1 ≤ C → x ≠ 0 →
        1 ≤ dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) →
      (A ^ (NN d n - 2) + A ^ (NN d n - n - 1) *
            (max A (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) ^ (n - 1)) /
          eNorm (veronese d n x)
        ≤ K * (2 * A ^ (NN d n - 2) / eNorm (veronese d n x)
            + A ^ (NN d n - n - 1) * C ^ (n - 1) * eNorm x ^ ((n : ℝ) - 1 - d)) := by
  obtain ⟨c₁, c₂, hc1, hc2, hvb⟩ := eNorm_veronese_bounds d n (by omega : 1 ≤ d)
  refine ⟨1 + c₁⁻¹, by positivity, ?_⟩
  intro A C x hA hC hx hD
  have hn1 : 1 ≤ n := by omega
  have hN : n + 2 ≤ NN d n := Work.HP.Sig2.NN_ge_add_two d n hd hdn
  have hXd : 0 < eNorm x := eNorm_pos_btl hx
  have hX0 : 0 ≤ eNorm x := le_of_lt hXd
  have hA0 : 0 ≤ A := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hD1 : (1 : ℝ) ≤ dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) := hD
  have hW : 0 < eNorm (veronese d n x) :=
    lt_of_lt_of_le (mul_pos hc1 (pow_pos hXd d)) (hvb x).1
  have hW0 : 0 ≤ eNorm (veronese d n x) := le_of_lt hW
  have hpow : A ^ (NN d n - n - 1) * A ^ (n - 1) = A ^ (NN d n - 2) := by
    rw [← pow_add]; congr 1; omega
  have hmu : (max A (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) ^ (n - 1)
      ≤ A ^ (n - 1) + C ^ (n - 1) * eNorm x ^ (n - 1) := by
    have hCX : 0 ≤ C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) :=
      div_nonneg (mul_nonneg hC0 hX0) (by linarith)
    have hCXk : 0 ≤ C ^ (n - 1) * eNorm x ^ (n - 1) :=
      mul_nonneg (pow_nonneg hC0 _) (pow_nonneg hX0 _)
    have hDk : (0 : ℝ) < (dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) ^ (n - 1) :=
      pow_pos (by linarith) _
    have hDk1 : (1 : ℝ) ≤ (dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) ^ (n - 1) := one_le_pow₀ hD1
    calc (max A (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) ^ (n - 1)
        ≤ A ^ (n - 1) + (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) ^ (n - 1) :=
            max_pow_le_btl A (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) (n - 1) hA0 hCX
      _ = A ^ (n - 1) + C ^ (n - 1) * eNorm x ^ (n - 1) /
            (dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) ^ (n - 1) := by
            rw [div_pow, mul_pow]
      _ ≤ A ^ (n - 1) + C ^ (n - 1) * eNorm x ^ (n - 1) := by
            have h : C ^ (n - 1) * eNorm x ^ (n - 1) /
                (dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) ^ (n - 1)
                ≤ C ^ (n - 1) * eNorm x ^ (n - 1) := by
              rw [div_le_iff₀ hDk]; nlinarith [hCXk, hDk1]
            linarith
  have hrpow : eNorm x ^ (n - 1) / eNorm (veronese d n x)
      ≤ (1 + c₁⁻¹) * eNorm x ^ ((n : ℝ) - 1 - d) := by
    have h := rpow_div_le_btl (eNorm x) (eNorm (veronese d n x)) c₁ d n hXd hc1 (hvb x).1 hn1
    calc eNorm x ^ (n - 1) / eNorm (veronese d n x) ≤ c₁⁻¹ * eNorm x ^ ((n : ℝ) - 1 - d) := h
      _ ≤ (1 + c₁⁻¹) * eNorm x ^ ((n : ℝ) - 1 - d) := by
            have hx0 : (0 : ℝ) ≤ eNorm x ^ ((n : ℝ) - 1 - d) := Real.rpow_nonneg hX0 _
            nlinarith
  calc (A ^ (NN d n - 2) + A ^ (NN d n - n - 1) *
            (max A (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) ^ (n - 1)) /
          eNorm (veronese d n x)
      = A ^ (NN d n - 2) / eNorm (veronese d n x)
        + (A ^ (NN d n - n - 1) *
            (max A (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) ^ (n - 1)) /
          eNorm (veronese d n x) := by
          rw [add_div]
    _ ≤ A ^ (NN d n - 2) / eNorm (veronese d n x)
        + (A ^ (NN d n - n - 1) * (A ^ (n - 1) + C ^ (n - 1) * eNorm x ^ (n - 1))) /
          eNorm (veronese d n x) := by
          apply add_le_add le_rfl
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmu (pow_nonneg hA0 _)) hW0
    _ = 2 * A ^ (NN d n - 2) / eNorm (veronese d n x)
        + A ^ (NN d n - n - 1) * C ^ (n - 1) * (eNorm x ^ (n - 1) / eNorm (veronese d n x)) := by
          rw [mul_add, add_div, hpow]; ring
    _ ≤ 2 * A ^ (NN d n - 2) / eNorm (veronese d n x)
        + A ^ (NN d n - n - 1) * C ^ (n - 1) * ((1 + c₁⁻¹) * eNorm x ^ ((n : ℝ) - 1 - d)) := by
          apply add_le_add le_rfl
          exact mul_le_mul_of_nonneg_left hrpow (mul_nonneg (pow_nonneg hA0 _) (pow_nonneg hC0 _))
    _ = 2 * A ^ (NN d n - 2) / eNorm (veronese d n x)
        + (1 + c₁⁻¹) * (A ^ (NN d n - n - 1) * C ^ (n - 1) * eNorm x ^ ((n : ℝ) - 1 - d)) := by
          ring
    _ ≤ (1 + c₁⁻¹) * (2 * A ^ (NN d n - 2) / eNorm (veronese d n x)
        + A ^ (NN d n - n - 1) * C ^ (n - 1) * eNorm x ^ ((n : ℝ) - 1 - d)) := by
          have hK1 : (1 : ℝ) ≤ 1 + c₁⁻¹ := le_add_of_nonneg_right (by positivity)
          have ha : 0 ≤ 2 * A ^ (NN d n - 2) / eNorm (veronese d n x) := by positivity
          have hZ : 0 ≤ A ^ (NN d n - n - 1) * C ^ (n - 1) * eNorm x ^ ((n : ℝ) - 1 - d) :=
            mul_nonneg (mul_nonneg (pow_nonneg hA0 _) (pow_nonneg hC0 _)) (Real.rpow_nonneg hX0 _)
          nlinarith [mul_nonneg ha (sub_nonneg.mpr hK1)]

end Work.HP.MM2
