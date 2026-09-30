import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open BoundedMultiplicativeFunctions
open scoped ComplexConjugate

/-- The `p`-th summand of `𝔻` is nonnegative for one-bounded `f`, `g`. -/
private lemma D_term_nonneg {f g : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (p : ℕ) : 0 ≤ (1 - (f p * conj (g p)).re) / (p : ℝ) := by
  have h1 : ‖f p * conj (g p)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖f p‖ * ‖g p‖ ≤ 1 * 1 :=
          mul_le_mul (hf p) (hg p) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have h2 : (f p * conj (g p)).re ≤ 1 := by
    have := Complex.re_le_norm (f p * conj (g p)); linarith
  exact div_nonneg (by linarith) (Nat.cast_nonneg p)

theorem D_mono (f g : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    {X Y : ℝ} (hXY : X ≤ Y) :
    BoundedMultiplicativeFunctions.𝔻 f g X ≤ BoundedMultiplicativeFunctions.𝔻 f g Y := by
  unfold BoundedMultiplicativeFunctions.𝔻
  apply Real.rpow_le_rpow _ _ (by norm_num)
  · exact Finset.sum_nonneg (fun p _ => D_term_nonneg hf hg p)
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (Nat.primesLE_mono (Nat.floor_mono hXY))
      (fun p _ _ => D_term_nonneg hf hg p)

end Work.BMF.mr_direct
