import Mathlib

/-!
# Associativity of the discrete convolution on `ℤ` with a bounded function

If `c` is the discrete convolution `c m = ∑' j, a j * b (m - j)` of two absolutely
summable sequences `a`, `b : ℤ → ℂ`, and `f : ℤ → ℂ` is bounded by `B`, then

  `∑' j, a j * (∑' i, b i * f (n - j - i)) = ∑' m, c m * f (n - m)`,

i.e. `a ∗ (b ∗ f) = (a ∗ b) ∗ f` at the point `n`.  The proof is Fubini for `tsum`
over `ℤ × ℤ`: the left-hand side is reindexed (in the inner variable, `i ↦ m - j`)
into the double sum `∑' j ∑' m a j * (b (m - j) * f (n - m))`, which is absolutely
summable, and then the two sums are interchanged.
-/

namespace Work.KMTPlan.A6

/-- Summability of the doubly indexed family appearing in the interchange of sums:
`(j, m) ↦ a j * (b (m - j) * f (n - m))` is absolutely summable when `a`, `b` are
absolutely summable and `f` is bounded by `B`. -/
private lemma summable_conv_bilinear {a b : ℤ → ℂ} (ha : Summable fun j : ℤ => ‖a j‖)
    (hb : Summable fun j : ℤ => ‖b j‖) {f : ℤ → ℂ} {B : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ B)
    (n : ℤ) :
    Summable (fun p : ℤ × ℤ => a p.1 * (b (p.2 - p.1) * f (n - p.2))) := by
  -- the norm majorant `‖a p.1‖ * ‖b (p.2 - p.1)‖` is summable, by the change of
  -- variables `(j, m) ↦ (j, m - j)` in the product of the two summable sequences
  have hprod : Summable (fun p : ℤ × ℤ => ‖a p.1‖ * ‖b (p.2 - p.1)‖) := by
    have h2 : Summable (fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖) :=
      ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    let e : ℤ × ℤ ≃ ℤ × ℤ :=
      { toFun := fun p => (p.1, p.2 - p.1)
        invFun := fun q => (q.1, q.2 + q.1)
        left_inv := by rintro ⟨x, y⟩; simp
        right_inv := by rintro ⟨x, y⟩; simp }
    have := (Equiv.summable_iff e).mpr h2
    simpa [e, Function.comp_def] using this
  exact Summable.of_norm_bounded (hprod.mul_right B) (fun p => by
    calc ‖a p.1 * (b (p.2 - p.1) * f (n - p.2))‖
        = ‖a p.1‖ * (‖b (p.2 - p.1)‖ * ‖f (n - p.2)‖) := by rw [norm_mul, norm_mul]
      _ ≤ ‖a p.1‖ * (‖b (p.2 - p.1)‖ * B) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)) (norm_nonneg _)
      _ = ‖a p.1‖ * ‖b (p.2 - p.1)‖ * B := by ring)

/-- Reindexing the inner sum by the bijection `i ↦ m - j` of `ℤ`. -/
private lemma tsum_shift_mul (b f : ℤ → ℂ) (n j : ℤ) :
    (∑' i : ℤ, b i * f (n - j - i)) = ∑' m : ℤ, b (m - j) * f (n - m) := by
  rw [← Equiv.tsum_eq (Equiv.addRight (-j)) (fun i : ℤ => b i * f (n - j - i))]
  refine tsum_congr (fun m => ?_)
  simp only [Equiv.coe_addRight, sub_eq_add_neg]
  ring_nf

theorem tsum_convAssoc {a b c : ℤ → ℂ}
    (hc : ∀ m : ℤ, c m = ∑' j : ℤ, a j * b (m - j))
    (ha : Summable fun j : ℤ => ‖a j‖) (hb : Summable fun j : ℤ => ‖b j‖)
    {f : ℤ → ℂ} {B : ℝ} (hf : ∀ m : ℤ, ‖f m‖ ≤ B) (n : ℤ) :
    ∑' j : ℤ, a j * (∑' i : ℤ, b i * f (n - j - i))
      = ∑' m : ℤ, c m * f (n - m) := by
  have hFsum := summable_conv_bilinear ha hb hf n
  calc
    ∑' j : ℤ, a j * (∑' i : ℤ, b i * f (n - j - i))
        = ∑' j : ℤ, ∑' m : ℤ, a j * (b (m - j) * f (n - m)) := by
          refine tsum_congr (fun j => ?_)
          rw [tsum_shift_mul b f n j, tsum_mul_left]
    _ = ∑' m : ℤ, ∑' j : ℤ, a j * (b (m - j) * f (n - m)) :=
          (Summable.tsum_comm hFsum).symm
    _ = ∑' m : ℤ, c m * f (n - m) := by
          refine tsum_congr (fun m => ?_)
          rw [hc m, ← tsum_mul_right]
          refine tsum_congr (fun j => ?_)
          ring

end Work.KMTPlan.A6
