import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.GN

theorem sum_rpow_le_of_each {ι : Type*} [Fintype ι] (A : ι → ℝ) (C e : ℝ)
    (hA : ∀ l, 0 ≤ A l) (hC : 0 ≤ C) (he : 0 < e) (h1 : ∀ l, A l ^ e ≤ C) :
    (∑ l, A l) ^ e ≤ (Fintype.card ι : ℝ) ^ e * C := by
  -- Since `x ↦ x ^ e` is monotone on `[0, ∞)`, each `A l ^ e ≤ C` gives `A l ≤ C ^ (1/e)`.
  have he1 : 0 ≤ 1 / e := le_of_lt (one_div_pos.mpr he)
  have hAle : ∀ l, A l ≤ C ^ (1 / e) := by
    intro l
    calc A l = (A l ^ e) ^ (1 / e) := by
          rw [← Real.rpow_mul (hA l) e (1 / e), mul_one_div_cancel (ne_of_gt he),
            Real.rpow_one]
      _ ≤ C ^ (1 / e) := Real.rpow_le_rpow (Real.rpow_nonneg (hA l) e) (h1 l) he1
  -- Hence the sum is at most `card ι * C ^ (1/e)`.
  have hsum : ∑ l, A l ≤ (Fintype.card ι : ℝ) * C ^ (1 / e) := by
    calc ∑ l, A l ≤ ∑ _l : ι, C ^ (1 / e) := Finset.sum_le_sum (fun l _ => hAle l)
      _ = (Fintype.card ι : ℝ) * C ^ (1 / e) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Raise to the power `e`.
  have hcard : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  calc (∑ l, A l) ^ e ≤ ((Fintype.card ι : ℝ) * C ^ (1 / e)) ^ e :=
        Real.rpow_le_rpow (Finset.sum_nonneg (fun l _ => hA l)) hsum (le_of_lt he)
    _ = (Fintype.card ι : ℝ) ^ e * C := by
        rw [Real.mul_rpow hcard (Real.rpow_nonneg hC _)]
        congr 1
        rw [← Real.rpow_mul hC (1 / e) e, one_div_mul_cancel (ne_of_gt he), Real.rpow_one]

end Work.Diff.STE.GN
