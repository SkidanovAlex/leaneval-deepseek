import Mathlib

namespace Work.Mostow

/-- If `x : Fin r → ℝ` is nonnegative (`r > 0`) and its sum is at most `δ ^ 2` with `δ > 0`,
then the product of the entries is at most `δ ^ (2 * r)`.

Indeed every entry is at most the total sum, hence at most `δ ^ 2`, and the product of
`r` numbers each bounded by `δ ^ 2` is at most `(δ ^ 2) ^ r = δ ^ (2 * r)`. -/
theorem prodLePowOfSumLe {r : ℕ} (hr : 0 < r) {x : Fin r → ℝ} (hx : ∀ i, 0 ≤ x i) {δ : ℝ}
    (hδ : 0 < δ) (h : ∑ i, x i ≤ δ ^ 2) : ∏ i, x i ≤ δ ^ (2 * r) := by
  -- Each entry is bounded by the total sum, hence by `δ ^ 2`.
  have hle : ∀ i, x i ≤ δ ^ 2 := fun i =>
    (Finset.single_le_sum (f := x) (fun j _ => hx j) (Finset.mem_univ i)).trans h
  calc ∏ i, x i ≤ ∏ _i : Fin r, δ ^ 2 :=
        Finset.prod_le_prod₀ (fun i _ => hx i) (fun i _ => hle i)
    _ = (δ ^ 2) ^ r := by simp
    _ = δ ^ (2 * r) := (pow_mul δ 2 r).symm

end Work.Mostow
