import Mathlib
import Submission.Commons.NumberTheory.NumberField.ncard_norm_le

namespace Commons.NumberTheory.NumberField

/-- The product over the infinite places of `K` of the `w.mult`-th powers of the place norms of the
mixed embedding of `x` equals `|Algebra.norm ℚ x|`.

Indeed for each infinite place `w`, `normAtPlace w (mixedEmbedding K x) = w x`
(`NumberField.mixedEmbedding.normAtPlace_apply`), and `∏ w, (w x) ^ w.mult = |Algebra.norm ℚ x|`
(`NumberField.InfinitePlace.prod_eq_abs_norm`). -/
theorem prod_normAtPlace_eq_abs_norm (K : Type*) [Field K] [NumberField K] (x : K) :
    (∏ w : NumberField.InfinitePlace K,
        (NumberField.mixedEmbedding.normAtPlace w
          (NumberField.mixedEmbedding K x)) ^ w.mult)
      = |Algebra.norm ℚ x| := by
  simp only [NumberField.mixedEmbedding.normAtPlace_apply]
  exact NumberField.InfinitePlace.prod_eq_abs_norm x

theorem ncard_mahler_le {K : Type*} [Field K] [NumberField K] (hn : 2 ≤ Module.finrank ℚ K)
    (Y lam : ℝ) (hY : 1 ≤ Y) (hlam : 1 ≤ lam)
    (hsep : ∀ α : NumberField.RingOfIntegers K, ((α : K)) ∉ Set.range (algebraMap ℤ K) →
      lam ≤ NumberField.house ((α : K))) :
    (Nat.card {α : NumberField.RingOfIntegers K // ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧
        (∏ w : NumberField.InfinitePlace K,
            (NumberField.mixedEmbedding.normAtPlace w
              (NumberField.mixedEmbedding K ((α : K)))) ^ w.mult) ≤ Y} : ℝ) ≤
      (100000 : ℝ) ^ Module.finrank ℚ K * Y *
        (1 + Real.log Y) ^ (Module.finrank ℚ K - 1) / lam := by
  have hcard : Nat.card {α : NumberField.RingOfIntegers K //
        ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧
        (∏ w : NumberField.InfinitePlace K,
            (NumberField.mixedEmbedding.normAtPlace w
              (NumberField.mixedEmbedding K ((α : K)))) ^ w.mult) ≤ Y}
      = Nat.card {α : NumberField.RingOfIntegers K //
        ((α : K)) ∉ Set.range (algebraMap ℤ K) ∧ |Algebra.norm ℚ ((α : K))| ≤ Y} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun α => by
      rw [prod_normAtPlace_eq_abs_norm]))
  rw [hcard]
  exact ncard_norm_le hn Y lam hY hlam hsep

end Commons.NumberTheory.NumberField
