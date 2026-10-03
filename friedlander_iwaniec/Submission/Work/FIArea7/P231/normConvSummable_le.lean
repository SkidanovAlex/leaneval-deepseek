import Mathlib

namespace Work.FIArea7.P231

open scoped Topology

/-- The (absolutely summable) convolution of two absolutely summable functions on `ℤ`
is absolutely summable, with `l¹` norm controlled by the product of the `l¹` norms.

The proof proceeds by reindexing the double sum `∑' p : ℤ × ℤ, ‖a p.1‖ * ‖b p.2‖`
along the bijection `(x, y) ↦ (y, x - y)` of `ℤ × ℤ` (so that the second coordinate
of the image is the convolution index), and applying Tonelli's theorem for nonnegative
series (`Summable.tsum_prod`, `Summable.prod`). -/
theorem normConvSummable_le {a b : ℤ → ℂ}
    (hsa : Summable fun k : ℤ => ‖a k‖) (hsb : Summable fun k : ℤ => ‖b k‖) :
    Summable (fun n : ℤ => ‖∑' j : ℤ, a j * b (n - j)‖) ∧
    (∑' n : ℤ, ‖∑' j : ℤ, a j * b (n - j)‖) ≤ (∑' k : ℤ, ‖a k‖) * (∑' k : ℤ, ‖b k‖) := by
  classical
  -- `F p = ‖a p.1‖ * ‖b p.2‖`: the product of the norm sequences.
  let F : ℤ × ℤ → ℝ := fun p => ‖a p.1‖ * ‖b p.2‖
  have hF_sum : Summable F := by
    simpa [F] using Summable.mul_of_nonneg hsa hsb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hF_tsum : (∑' k : ℤ, ‖a k‖) * (∑' k : ℤ, ‖b k‖) = ∑' p : ℤ × ℤ, F p := by
    simpa [F] using tsum_mul_tsum_of_summable_norm (R := ℝ)
      (f := fun k : ℤ => ‖a k‖) (g := fun k : ℤ => ‖b k‖) (by simpa using hsa) (by simpa using hsb)
  -- The bijection `(x, y) ↦ (y, x - y)` of `ℤ × ℤ`.
  let e : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun q => (q.2, q.1 - q.2)
      invFun := fun p => (p.1 + p.2, p.1)
      left_inv := by rintro ⟨x, y⟩; simp
      right_inv := by rintro ⟨x, y⟩; simp }
  -- `G (n, j) = ‖a j‖ * ‖b (n - j)‖`: the summand of the iterated (Tonelli) form.
  let G : ℤ × ℤ → ℝ := fun q => ‖a q.2‖ * ‖b (q.1 - q.2)‖
  have hG_sum : Summable G := by
    have h := (Equiv.summable_iff (f := F) e).mpr hF_sum
    simpa [G, F, e, Function.comp_def] using h
  have hG_tsum : ∑' q : ℤ × ℤ, G q = (∑' k : ℤ, ‖a k‖) * (∑' k : ℤ, ‖b k‖) := by
    have h : (∑' q : ℤ × ℤ, F (e q)) = ∑' p : ℤ × ℤ, F p := Equiv.tsum_eq e F
    rw [← hF_tsum] at h
    simpa [G, F, e] using h
  -- `d n = ∑' j, ‖a j‖ * ‖b (n - j)‖` is the (norm-)convolution envelope.
  set d : ℤ → ℝ := fun n => ∑' j : ℤ, ‖a j‖ * ‖b (n - j)‖ with hd_def
  have hd_sum : Summable d := by
    rw [hd_def]
    simpa [G] using Summable.prod hG_sum
  have hd_tsum : ∑' n : ℤ, d n = (∑' k : ℤ, ‖a k‖) * (∑' k : ℤ, ‖b k‖) := by
    rw [hd_def]
    have h := Summable.tsum_prod hG_sum
    rw [hG_tsum] at h
    simpa [G] using h.symm
  -- `‖b‖` is bounded by its total mass.
  have hB_bound : ∀ k : ℤ, ‖b k‖ ≤ ∑' k : ℤ, ‖b k‖ :=
    fun k => hsb.le_tsum k (fun j _ => norm_nonneg _)
  -- Each convolution series converges absolutely.
  have hcn_sum : ∀ n : ℤ, Summable (fun j : ℤ => a j * b (n - j)) := by
    intro n
    refine Summable.of_norm_bounded (hsa.mul_right (∑' k : ℤ, ‖b k‖)) (fun j => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB_bound (n - j)) (norm_nonneg _)
  have hcn_norm : ∀ n : ℤ, Summable (fun j : ℤ => ‖a j * b (n - j)‖) := by
    intro n
    refine Summable.of_norm_bounded (hsa.mul_right (∑' k : ℤ, ‖b k‖)) (fun j => ?_)
    rw [norm_norm, norm_mul]
    exact mul_le_mul_of_nonneg_left (hB_bound (n - j)) (norm_nonneg _)
  -- Pointwise domination of the convolution by `d`.
  have hbound : ∀ n : ℤ, ‖∑' j : ℤ, a j * b (n - j)‖ ≤ d n := by
    intro n
    rw [hd_def]
    calc ‖∑' j : ℤ, a j * b (n - j)‖
        ≤ ∑' j : ℤ, ‖a j * b (n - j)‖ := norm_tsum_le_tsum_norm (hcn_norm n)
      _ = ∑' j : ℤ, ‖a j‖ * ‖b (n - j)‖ := by
            refine tsum_congr fun j => ?_; rw [norm_mul]
  refine ⟨Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hd_sum, ?_⟩
  calc (∑' n : ℤ, ‖∑' j : ℤ, a j * b (n - j)‖)
      ≤ ∑' n : ℤ, d n := Summable.tsum_le_tsum hbound
          (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hd_sum) hd_sum
    _ = (∑' k : ℤ, ‖a k‖) * (∑' k : ℤ, ‖b k‖) := hd_tsum

end Work.FIArea7.P231
