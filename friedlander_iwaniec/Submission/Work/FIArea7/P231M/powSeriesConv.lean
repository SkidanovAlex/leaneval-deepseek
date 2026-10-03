import Mathlib
import Submission.Work.FIArea7.P231.normConvSummable_le

namespace Work.FIArea7.P231M

/-- Multiplication of two absolutely convergent Laurent series on the unit circle.

If `∑_k a_k u^k = A` and `∑_k b_k u^k = B` with `‖u‖ = 1` and `(a_k), (b_k) ∈ ℓ¹(ℤ)`,
then the convolution series `∑_n (∑_j a_j b_{n-j}) u^n` sums to `A * B`. -/
theorem powSeriesConv {a b : ℤ → ℂ} {u A B : ℂ} (hu : ‖u‖ = 1)
    (ha : HasSum (fun k : ℤ => a k * u ^ k) A)
    (hb : HasSum (fun k : ℤ => b k * u ^ k) B)
    (hsa : Summable fun k : ℤ => ‖a k‖) (hsb : Summable fun k : ℤ => ‖b k‖) :
    HasSum (fun n : ℤ => (∑' j : ℤ, a j * b (n - j)) * u ^ n) (A * B) := by
  classical
  have hu0 : u ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  -- `‖u ^ k‖ = 1` for every integer `k`, so absolute convergence of `a` and `b` is preserved.
  have hnorm_a : ∀ k : ℤ, ‖a k * u ^ k‖ = ‖a k‖ := by
    intro k; rw [norm_mul, norm_zpow, hu, one_zpow, mul_one]
  have hnorm_b : ∀ k : ℤ, ‖b k * u ^ k‖ = ‖b k‖ := by
    intro k; rw [norm_mul, norm_zpow, hu, one_zpow, mul_one]
  -- The product family over `ℤ × ℤ` is absolutely summable.
  have hFsum : Summable (fun p : ℤ × ℤ => (a p.1 * u ^ p.1) * (b p.2 * u ^ p.2)) := by
    refine Summable.of_norm_bounded
      (Summable.mul_of_nonneg hsa hsb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _))
      (fun p => ?_)
    simp only [norm_mul, hnorm_a, hnorm_b, le_refl]
  -- Cauchy product for the double series.
  have hProd : HasSum (fun p : ℤ × ℤ => (a p.1 * u ^ p.1) * (b p.2 * u ^ p.2)) (A * B) := by
    have h := HasSum.mul (f := fun k : ℤ => a k * u ^ k) (g := fun k : ℤ => b k * u ^ k)
      ha hb hFsum
    simpa using h
  -- Reindex `(j, m) ↦ (n, j) = (j + m, j)`, so that the first coordinate is the convolution
  -- index `n = j + m`.
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun x => (x.2, x.1 - x.2)
      invFun := fun p => (p.1 + p.2, p.1)
      left_inv := by rintro ⟨n, j⟩; simp
      right_inv := by rintro ⟨j, m⟩; simp }
  have hReindex : HasSum
      (fun x : ℤ × ℤ => (a x.2 * u ^ x.2) * (b (x.1 - x.2) * u ^ (x.1 - x.2))) (A * B) := by
    have h := (Equiv.hasSum_iff e).mpr hProd
    convert h using 1
    ext x
    rfl
  -- Collect the powers: `u ^ j * u ^ (n - j) = u ^ n`.
  have hProd' : HasSum (fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) * u ^ p.1) (A * B) :=
    hReindex.congr_fun (fun p => by
      have hz : u ^ p.1 = u ^ p.2 * u ^ (p.1 - p.2) := by
        rw [← zpow_add₀ hu0 p.2 (p.1 - p.2)]
        congr 1
        ring
      rw [hz]
      ring)
  -- Each fibre series over `j` converges absolutely.
  have hbtot : ∀ m : ℤ, ‖b m‖ ≤ ∑' k : ℤ, ‖b k‖ :=
    fun m => hsb.le_tsum m (fun k _ => norm_nonneg _)
  have hcn : ∀ n : ℤ, Summable (fun j : ℤ => a j * b (n - j)) := by
    intro n
    refine Summable.of_norm_bounded (hsa.mul_right (∑' k : ℤ, ‖b k‖)) (fun j => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbtot (n - j)) (norm_nonneg _)
  -- Sum the fibres: for each `n` the `j`-sum gives `(∑'_j a_j b_{n-j}) * u^n`.
  refine HasSum.prod_fiberwise hProd' (fun n => ?_)
  exact ((hcn n).hasSum).mul_right (u ^ n)

end Work.FIArea7.P231M
