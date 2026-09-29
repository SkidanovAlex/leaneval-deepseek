import Mathlib
import Submission.Work.CPull.defs

/-!
# Area CPull — auxiliary lemmas for `evp_subst`

`evp f z = ∑' n, (coeff n f : ℂ) * z ^ n` (see `Submission.Work.CPull.defs`).

This file collects the small shared ingredients of the proof that evaluation commutes with
substitution of power series:

* `coeff_mul_mul_pow` : the pointwise Cauchy-product identity expressing the `n`-th coefficient
  of a product as a convolution over `Finset.range (n+1)` (rather than `antidiagonal`);
* `norm_coeff_mul_mul_pow_le` : its norm version;
* `summable_range_mul` : the Cauchy product of two summable nonnegative real sequences;
* `evpMul` : the Cauchy product formula for `evp` itself, together with the ℓ¹-norm bound
  `∑ ‖coeff n (g*h) z^n‖ ≤ (∑ ‖coeff n g z^n‖) * (∑ ‖coeff n h z^n‖)`.

They are used by `Work.CPull.evpPow` and `Work.CPull.evp_subst`.
-/

namespace Work.CPull

open PowerSeries

/-- The `n`-th coefficient of a product, as a convolution over `Finset.range (n+1)`, with the
factor `z ^ n` distributed over the two terms. -/
lemma coeff_mul_mul_pow (g h : PowerSeries ℚ) (z : ℂ) (n : ℕ) :
    ((PowerSeries.coeff n (g * h) : ℚ) : ℂ) * z ^ n
      = ∑ k ∈ Finset.range (n + 1),
          (((PowerSeries.coeff k g : ℚ) : ℂ) * z ^ k) *
            (((PowerSeries.coeff (n - k) h : ℚ) : ℂ) * z ^ (n - k)) := by
  rw [PowerSeries.coeff_mul]
  push_cast
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => ((PowerSeries.coeff a g : ℚ) : ℂ) * ((PowerSeries.coeff b h : ℚ) : ℂ)) n]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hz : z ^ n = z ^ k * z ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hk']
  rw [hz]
  ring

/-- Norm version of `coeff_mul_mul_pow`. -/
lemma norm_coeff_mul_mul_pow_le (g h : PowerSeries ℚ) (z : ℂ) (n : ℕ) :
    ‖((PowerSeries.coeff n (g * h) : ℚ) : ℂ) * z ^ n‖
      ≤ ∑ k ∈ Finset.range (n + 1),
          ‖(((PowerSeries.coeff k g : ℚ) : ℂ) * z ^ k)‖ *
            ‖(((PowerSeries.coeff (n - k) h : ℚ) : ℂ) * z ^ (n - k))‖ := by
  rw [coeff_mul_mul_pow]
  calc ‖∑ k ∈ Finset.range (n + 1),
          (((PowerSeries.coeff k g : ℚ) : ℂ) * z ^ k) *
            (((PowerSeries.coeff (n - k) h : ℚ) : ℂ) * z ^ (n - k))‖
      ≤ ∑ k ∈ Finset.range (n + 1),
          ‖(((PowerSeries.coeff k g : ℚ) : ℂ) * z ^ k) *
            (((PowerSeries.coeff (n - k) h : ℚ) : ℂ) * z ^ (n - k))‖ :=
        norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n + 1),
          ‖(((PowerSeries.coeff k g : ℚ) : ℂ) * z ^ k)‖ *
            ‖(((PowerSeries.coeff (n - k) h : ℚ) : ℂ) * z ^ (n - k))‖ := by
        simp

/-- Cauchy product of two summable sequences of nonnegative real numbers, in the `range`
formulation: the convolution is summable and its sum is the product of the sums. -/
lemma summable_range_mul {f g : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n)
    (hf : Summable f) (hg : Summable g) :
    Summable (fun n => ∑ k ∈ Finset.range (n + 1), f k * g (n - k)) ∧
      (∑' n, ∑ k ∈ Finset.range (n + 1), f k * g (n - k)) = (∑' k, f k) * (∑' k, g k) := by
  have hf' : Summable fun x : ℕ => ‖f x‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 _)] using hf
  have hg' : Summable fun x : ℕ => ‖g x‖ := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using hg
  have hsum : Summable fun n => ∑ k ∈ Finset.range (n + 1), f k * g (n - k) :=
    Summable.of_norm (summable_norm_sum_mul_range_of_summable_norm hf' hg')
  have hval := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf' hg'
  exact ⟨hsum, hval.symm⟩

/-- **Cauchy product formula for `evp`.**  If the coefficient series of `g` and `h` (weighted by
`z ^ n`) are absolutely summable, then so is that of the product, the ℓ¹ masses are
submultiplicative, and evaluation at `z` is multiplicative. -/
lemma evpMul (g h : PowerSeries ℚ) (z : ℂ)
    (hg : Summable fun n : ℕ => ‖((PowerSeries.coeff n g : ℚ) : ℂ) * z ^ n‖)
    (hh : Summable fun n : ℕ => ‖((PowerSeries.coeff n h : ℚ) : ℂ) * z ^ n‖) :
    Summable (fun n : ℕ => ‖((PowerSeries.coeff n (g * h) : ℚ) : ℂ) * z ^ n‖) ∧
      (∑' n : ℕ, ‖((PowerSeries.coeff n (g * h) : ℚ) : ℂ) * z ^ n‖)
        ≤ (∑' n : ℕ, ‖((PowerSeries.coeff n g : ℚ) : ℂ) * z ^ n‖)
          * (∑' n : ℕ, ‖((PowerSeries.coeff n h : ℚ) : ℂ) * z ^ n‖) ∧
      Summable (fun n : ℕ => ((PowerSeries.coeff n (g * h) : ℚ) : ℂ) * z ^ n) ∧
      evp (g * h) z = evp g z * evp h z := by
  set F : ℕ → ℝ := fun k => ‖((PowerSeries.coeff k g : ℚ) : ℂ) * z ^ k‖ with hF
  set G : ℕ → ℝ := fun l => ‖((PowerSeries.coeff l h : ℚ) : ℂ) * z ^ l‖ with hG
  obtain ⟨hsum, hval⟩ :=
    summable_range_mul (f := F) (g := G) (fun k => norm_nonneg _) (fun l => norm_nonneg _)
      hg hh
  have key : ∀ n : ℕ, ‖((PowerSeries.coeff n (g * h) : ℚ) : ℂ) * z ^ n‖
      ≤ ∑ k ∈ Finset.range (n + 1), F k * G (n - k) := fun n =>
    norm_coeff_mul_mul_pow_le g h z n
  have hnorm : Summable fun n : ℕ => ‖((PowerSeries.coeff n (g * h) : ℚ) : ℂ) * z ^ n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) key hsum
  have hnormle :
      (∑' n : ℕ, ‖((PowerSeries.coeff n (g * h) : ℚ) : ℂ) * z ^ n‖)
        ≤ (∑' n : ℕ, ‖((PowerSeries.coeff n g : ℚ) : ℂ) * z ^ n‖)
          * (∑' n : ℕ, ‖((PowerSeries.coeff n h : ℚ) : ℂ) * z ^ n‖) := by
    rw [← hval]
    exact Summable.tsum_le_tsum key hnorm hsum
  have hsum' : Summable fun n : ℕ => ((PowerSeries.coeff n (g * h) : ℚ) : ℂ) * z ^ n :=
    Summable.of_norm hnorm
  have hval' : evp (g * h) z = evp g z * evp h z := by
    have hkey := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm
      (f := fun n : ℕ => ((PowerSeries.coeff n g : ℚ) : ℂ) * z ^ n)
      (g := fun n : ℕ => ((PowerSeries.coeff n h : ℚ) : ℂ) * z ^ n) hg hh
    have hpoint : ∀ n : ℕ,
        ∑ k ∈ Finset.range (n + 1),
            (((PowerSeries.coeff k g : ℚ) : ℂ) * z ^ k) *
              (((PowerSeries.coeff (n - k) h : ℚ) : ℂ) * z ^ (n - k))
          = ((PowerSeries.coeff n (g * h) : ℚ) : ℂ) * z ^ n :=
      fun n => (coeff_mul_mul_pow g h z n).symm
    rw [tsum_congr hpoint] at hkey
    simpa only [evp] using hkey.symm
  exact ⟨hnorm, hnormle, hsum', hval'⟩

end Work.CPull
