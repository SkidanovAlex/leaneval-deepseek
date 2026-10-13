/-
  WilG5 / PolyEval — the crude polynomial-growth bound.

  For a real multivariate polynomial `c` in `m` variables there are a constant `C ≥ 0` and an
  exponent `N` with `|c.eval x| ≤ C * (1 + ∑ i, |x i|)^N` for every `x : Fin m → ℝ`.

  The proof is the structural induction on `MvPolynomial` (`C`, `+`, `· X n`), with the
  *same* weight `S x = 1 + ∑ i, |x i|` used throughout: `S x ≥ 1`, `S x ≥ 0`, and
  `|x n| ≤ S x` (a coordinate is at most the sum of the absolute values).  Addition takes
  `C₁ + C₂` and `max N₁ N₂`; multiplication by a variable takes the same `C` and `N + 1`.

  Note (Mathlib API in this snapshot): the monotonicity of `n ↦ a ^ n` for `1 ≤ a` over `ℝ`
  must be invoked as `pow_le_pow_right₀`; the variant `pow_le_pow_right'` is stated for
  `MulLeftMono`, a class that is *not* instantiated for `ℝ` here (only `PosMulMono`).
-/
import Mathlib

namespace Work.WilG5.PolyEval

/-- `1 + ∑ i, |x i|` is at least `1`, hence nonnegative. -/
lemma one_le_one_add_sum_abs {m : ℕ} (x : Fin m → ℝ) : 1 ≤ 1 + ∑ i, |x i| :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => abs_nonneg (x i))

/-- Every coordinate is dominated by the weight `1 + ∑ i, |x i|`. -/
lemma abs_apply_le_one_add_sum_abs {m : ℕ} (x : Fin m → ℝ) (n : Fin m) :
    |x n| ≤ 1 + ∑ i, |x i| :=
  (Finset.single_le_sum (fun i _ => abs_nonneg (x i)) (Finset.mem_univ n)).trans
    (le_add_of_nonneg_left zero_le_one)

theorem poly_abs_bound {m : ℕ} (c : MvPolynomial (Fin m) ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ x : Fin m → ℝ,
      |MvPolynomial.eval x c| ≤ C * (1 + ∑ i, |x i|) ^ N := by
  induction c using MvPolynomial.induction_on with
  | C a =>
    exact ⟨|a|, 0, abs_nonneg a, fun x => by simp [MvPolynomial.eval_C]⟩
  | add p q hp hq =>
    obtain ⟨C₁, N₁, hC₁, hb₁⟩ := hp
    obtain ⟨C₂, N₂, hC₂, hb₂⟩ := hq
    refine ⟨C₁ + C₂, max N₁ N₂, add_nonneg hC₁ hC₂, fun x => ?_⟩
    have hS1 : (1 : ℝ) ≤ 1 + ∑ i, |x i| := one_le_one_add_sum_abs x
    calc |MvPolynomial.eval x (p + q)|
        = |MvPolynomial.eval x p + MvPolynomial.eval x q| := by rw [MvPolynomial.eval_add]
      _ ≤ |MvPolynomial.eval x p| + |MvPolynomial.eval x q| := abs_add_le _ _
      _ ≤ C₁ * (1 + ∑ i, |x i|) ^ N₁ + C₂ * (1 + ∑ i, |x i|) ^ N₂ :=
          add_le_add (hb₁ x) (hb₂ x)
      _ ≤ C₁ * (1 + ∑ i, |x i|) ^ (max N₁ N₂) + C₂ * (1 + ∑ i, |x i|) ^ (max N₁ N₂) :=
          add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS1 (le_max_left _ _)) hC₁)
                     (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS1 (le_max_right _ _)) hC₂)
      _ = (C₁ + C₂) * (1 + ∑ i, |x i|) ^ (max N₁ N₂) := by ring
  | mul_X p n hp =>
    obtain ⟨C, N, hC, hb⟩ := hp
    refine ⟨C, N + 1, hC, fun x => ?_⟩
    have hS1 : (1 : ℝ) ≤ 1 + ∑ i, |x i| := one_le_one_add_sum_abs x
    have hS0 : (0 : ℝ) ≤ 1 + ∑ i, |x i| := le_trans zero_le_one hS1
    have hxn : |x n| ≤ 1 + ∑ i, |x i| := abs_apply_le_one_add_sum_abs x n
    calc |MvPolynomial.eval x (p * MvPolynomial.X n)|
        = |MvPolynomial.eval x p * x n| := by rw [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      _ = |MvPolynomial.eval x p| * |x n| := abs_mul _ _
      _ ≤ (C * (1 + ∑ i, |x i|) ^ N) * (1 + ∑ i, |x i|) :=
          mul_le_mul (hb x) hxn (abs_nonneg _) (mul_nonneg hC (pow_nonneg hS0 N))
      _ = C * (1 + ∑ i, |x i|) ^ (N + 1) := by rw [pow_succ]; ring

end Work.WilG5.PolyEval
