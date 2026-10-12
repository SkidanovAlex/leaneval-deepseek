import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Lemmas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Fourier

open scoped BigOperators

theorem hasSum_even_int_to_nat {f : ℤ → ℝ} (hf : ∀ n : ℤ, f (-n) = f n) {L : ℝ}
    (h : HasSum f L) :
    HasSum (fun k : ℕ => (if k = 0 then (1 : ℝ) else 2) * f (k : ℤ)) L := by
  -- Write the target series as `g`.
  set g : ℕ → ℝ := fun k => (if k = 0 then (1 : ℝ) else 2) * f (k : ℤ) with hgdef
  have hs : Summable f := h.summable
  -- The restriction of `f` to `ℕ` is summable.
  have hsf : Summable fun n : ℕ => f (n : ℤ) := hs.comp_injective Nat.cast_injective
  -- The total ℤ-sum is `f 0 + 2 * ∑'_{n ≥ 1} f n`, because `f` is even.
  have hL : L = f 0 + 2 * ∑' n : ℕ+, f (n : ℤ) := by
    rw [← h.tsum_eq, tsum_int_eq_zero_add_two_mul_tsum_pnat hf hs]
    simp only [nsmul_eq_mul]
    norm_num
  -- `g` is summable: it is dominated by `2 * ‖f ·‖`.
  have hgsum : Summable g := by
    refine Summable.of_norm_bounded (hsf.norm.mul_left 2) fun k => ?_
    have h1 : ‖g k‖ = (if k = 0 then (1 : ℝ) else 2) * ‖f (k : ℤ)‖ := by
      rw [hgdef]
      simp only [norm_mul]
      congr 1
      split <;> simp
    rw [h1]
    split <;> linarith [norm_nonneg (f (k : ℤ))]
  have hg0 : g 0 = f 0 := by simp [hgdef]
  -- Summing `g` over `ℕ` splits off its `0`-th term.
  have hgsucc : ∑' b : ℕ, g (b + 1) = 2 * ∑' n : ℕ+, f (n : ℤ) := by
    have h1 : ∑' b : ℕ, g (b + 1) = ∑' b : ℕ, (2 * f (((b + 1 : ℕ) : ℤ))) := by
      apply tsum_congr; intro b
      simp [hgdef]
    rw [h1, tsum_mul_left]
    congr 1
    rw [← tsum_pnat_eq_tsum_succ (f := fun m : ℕ => f (m : ℤ))]
  have hgtsum : ∑' k : ℕ, g k = f 0 + 2 * ∑' n : ℕ+, f (n : ℤ) := by
    rw [hgsum.tsum_eq_zero_add, hg0, hgsucc]
  have hfin : ∑' k : ℕ, g k = L := hgtsum.trans hL.symm
  rw [← hfin]
  exact hgsum.hasSum

end Commons.Analysis.Fourier