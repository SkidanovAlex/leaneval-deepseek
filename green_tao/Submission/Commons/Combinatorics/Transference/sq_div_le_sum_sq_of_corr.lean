import Mathlib.Algebra.Order.Star.Real

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- **Cauchy–Schwarz lower bound on a weighted `L²` norm.**  If a weighted sum is bounded below in
absolute value, `γ ≤ |∑_{x∈S} f x · h x|`, and the weight `h` is bounded by `M > 0`, then the
weighted `L²` norm of `f` is bounded below by `γ²/(|X| M²)`. -/
theorem sq_div_le_sum_sq_of_corr {X : Type*} [Fintype X] [Nonempty X]
    {S : Finset X} {f h : X → ℝ} {M γ : ℝ} (hM : 0 < M) (hγ0 : 0 ≤ γ)
    (hh : ∀ x, |h x| ≤ M) (hγ : γ ≤ |∑ x ∈ S, f x * h x|) :
    γ ^ 2 / ((Fintype.card X : ℝ) * M ^ 2) ≤ ∑ x ∈ S, (f x) ^ 2 := by
  have hM2 : (0 : ℝ) < M ^ 2 := pow_pos hM 2
  have hcardpos : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hQ : (0 : ℝ) < (Fintype.card X : ℝ) * M ^ 2 := mul_pos hcardpos hM2
  -- Cauchy–Schwarz on `S`
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S f h
  have hf2 : 0 ≤ ∑ x ∈ S, (f x) ^ 2 := Finset.sum_nonneg (fun x _ => sq_nonneg (f x))
  -- the weight `h` is bounded on `S`, so its mass is at most `|X| M²`
  have hh2 : ∑ x ∈ S, (h x) ^ 2 ≤ (Fintype.card X : ℝ) * M ^ 2 := by
    calc
      ∑ x ∈ S, (h x) ^ 2 ≤ ∑ x ∈ S, M ^ 2 := by
        apply Finset.sum_le_sum
        intro x _
        exact sq_le_sq.mpr (by rw [abs_of_pos hM]; exact hh x)
      _ = (S.card : ℝ) * M ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Fintype.card X : ℝ) * M ^ 2 := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast Finset.card_le_univ S
        · exact hM2.le
  have hbound : (∑ x ∈ S, f x * h x) ^ 2 ≤
      (∑ x ∈ S, (f x) ^ 2) * ((Fintype.card X : ℝ) * M ^ 2) :=
    le_trans hCS (mul_le_mul_of_nonneg_left hh2 hf2)
  have hs : γ ^ 2 ≤ (∑ x ∈ S, f x * h x) ^ 2 := by
    have := pow_le_pow_left₀ hγ0 hγ 2
    rwa [sq_abs] at this
  rw [div_le_iff₀ hQ]
  exact le_trans hs hbound

end Commons.Combinatorics.Transference