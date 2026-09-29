import Mathlib

/-!
# Summability of the pentagonal-type series `∑ q^{(k+1)n} ∏_{i≤n} (1 - q^{k+i+1})`

For `‖q‖ < 1` and `k : ℕ`, the terms
`q ^ ((k+1)*n) * ∏_{i=0}^{n} (1 - q ^ (k+i+1))` decay geometrically.

The estimate: `‖q‖ = r < 1`, and
`‖∏_{i=0}^n (1 - q^{k+i+1})‖ ≤ ∏_{i=0}^n (1 + r^{k+i+1})
  ≤ exp (∑_{i=0}^n r^{k+i+1}) ≤ exp ((1-r)⁻¹)`,
so the `n`-th term is bounded by the geometric sequence
`(r^{k+1})^n * exp ((1-r)⁻¹)` with ratio `r^{k+1} < 1`.
-/

namespace Work.Haupt

lemma penta_summable_a (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    Summable (fun n : ℕ => q ^ ((k + 1) * n) *
      ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))) := by
  set r : ℝ := ‖q‖ with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact norm_nonneg q
  have hr1 : r < 1 := by rw [hr]; exact hq
  have hgeom : Summable (fun i : ℕ => r^i) := summable_geometric_of_lt_one hr0 hr1
  have hgeomtsum : ∑' i : ℕ, r^i = (1-r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  have hbound : ∀ n : ℕ,
      ‖q ^ ((k+1)*n) * ∏ i ∈ Finset.range (n+1), (1 - q^(k+i+1))‖
        ≤ (r^(k+1))^n * Real.exp ((1-r)⁻¹) := by
    intro n
    have hA : ‖q ^ ((k+1)*n)‖ = r ^ ((k+1)*n) := by rw [norm_pow, ← hr]
    have hB : ‖∏ i ∈ Finset.range (n+1), (1 - q^(k+i+1))‖
        = ∏ i ∈ Finset.range (n+1), ‖1 - q^(k+i+1)‖ := norm_prod _ _
    have hC : ∏ i ∈ Finset.range (n+1), ‖1 - q^(k+i+1)‖
        ≤ Real.exp ((1-r)⁻¹) := by
      calc ∏ i ∈ Finset.range (n+1), ‖1 - q^(k+i+1)‖
          ≤ ∏ i ∈ Finset.range (n+1), (1 + r^(k+i+1)) := by
            apply Finset.prod_le_prod₀
            · intro i hi; exact norm_nonneg _
            · intro i hi
              calc ‖1 - q^(k+i+1)‖ ≤ ‖(1:ℂ)‖ + ‖q^(k+i+1)‖ := norm_sub_le _ _
                _ = 1 + r^(k+i+1) := by rw [norm_one, norm_pow, ← hr]
        _ ≤ ∏ i ∈ Finset.range (n+1), Real.exp (r^(k+i+1)) := by
            apply Finset.prod_le_prod₀
            · intro i hi; positivity
            · intro i hi
              have := Real.add_one_le_exp (r^(k+i+1))
              linarith
        _ = Real.exp (∑ i ∈ Finset.range (n+1), r^(k+i+1)) := by
            rw [Real.exp_sum]
        _ ≤ Real.exp ((1-r)⁻¹) := by
            apply Real.exp_le_exp.mpr
            calc ∑ i ∈ Finset.range (n+1), r^(k+i+1)
                ≤ ∑ i ∈ Finset.range (n+1), r^i := by
                  apply Finset.sum_le_sum
                  intro i hi
                  exact pow_le_pow_of_le_one hr0 (le_of_lt hr1) (by omega)
              _ ≤ (1-r)⁻¹ := by
                  rw [← hgeomtsum]
                  exact hgeom.sum_le_tsum _ (fun i _ => pow_nonneg hr0 i)
    calc ‖q ^ ((k+1)*n) * ∏ i ∈ Finset.range (n+1), (1 - q^(k+i+1))‖
        = r^((k+1)*n) * ∏ i ∈ Finset.range (n+1), ‖1 - q^(k+i+1)‖ := by
          rw [norm_mul, hA, hB]
      _ ≤ r^((k+1)*n) * Real.exp ((1-r)⁻¹) := by
          apply mul_le_mul_of_nonneg_left hC
          exact pow_nonneg hr0 _
      _ = (r^(k+1))^n * Real.exp ((1-r)⁻¹) := by rw [pow_mul]
  have hg : Summable (fun n : ℕ => (r^(k+1))^n * Real.exp ((1-r)⁻¹)) := by
    have h2 : Summable (fun n : ℕ => (r^(k+1))^n) :=
      summable_geometric_of_lt_one (pow_nonneg hr0 _) (pow_lt_one₀ hr0 hr1 (by omega))
    exact h2.mul_right _
  exact Summable.of_norm_bounded hg hbound

end Work.Haupt

namespace Work.Haupt
namespace Work.Haupt

set_option linter.dupNamespace false in
/-- The statement as originally placed in this file (doubled namespace). -/
lemma penta_summable_a (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    Summable (fun n : ℕ => q ^ ((k + 1) * n) *
      ∏ i ∈ Finset.range (n + 1), (1 - q ^ (k + i + 1))) :=
  _root_.Work.Haupt.penta_summable_a q hq k

end Work.Haupt
end Work.Haupt
