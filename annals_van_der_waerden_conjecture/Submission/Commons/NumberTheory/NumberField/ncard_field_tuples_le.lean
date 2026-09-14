import Mathlib
import Submission.Commons.NumberTheory.NumberField.ncard_mahler_one_le

set_option maxHeartbeats 1000000

open NumberField
open scoped Classical

namespace Commons.NumberTheory.NumberField

noncomputable section

/-- The number of `k`-tuples all of whose entries lie in a set is the `k`-th power of the number
of elements of that set.  (`Set.ncard` of the ambient set `s^k` equals `s.ncard^k`.) -/
lemma ncard_pi_const_pow {α : Type*} (p : α → Prop) (k : ℕ) :
    (({v : Fin k → α | ∀ i, p (v i)} : Set (Fin k → α)).ncard) =
      (({a : α | p a} : Set α).ncard) ^ k := by
  rw [← Nat.card_coe_set_eq (s := {v : Fin k → α | ∀ i, p (v i)}),
      ← Nat.card_coe_set_eq (s := {a : α | p a})]
  have h1 : Nat.card {v : Fin k → α // ∀ i, p (v i)} =
      Nat.card ((i : Fin k) → {a : α // p a}) :=
    Nat.card_congr Equiv.subtypePiEquivPi
  have h2 : Nat.card ((i : Fin k) → {a : α // p a}) = (Nat.card {a : α // p a}) ^ k := by
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  change Nat.card {v : Fin k → α // ∀ i, p (v i)} = (Nat.card {a : α // p a}) ^ k
  rw [h1, h2]

theorem ncard_field_tuples_le {K : Type*} [Field K] [NumberField K]
    (hk : 2 ≤ Module.finrank ℚ K) (k : ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    (({v : Fin k → NumberField.RingOfIntegers K |
        ∀ i, (∏ w : NumberField.InfinitePlace K,
          (max 1 (NumberField.mixedEmbedding.normAtPlace w
            (NumberField.mixedEmbedding K (((v i) : NumberField.RingOfIntegers K) : K)))) ^
              NumberField.InfinitePlace.mult w) ≤ Y} : Set (Fin k → NumberField.RingOfIntegers K)).ncard : ℝ)
      ≤ ((200000 : ℝ) ^ (Module.finrank ℚ K) * Y *
          (1 + Real.log Y) ^ (Module.finrank ℚ K - 1)) ^ k := by
  classical
  -- Fold the product into the Mahler measure `mahlerK`.
  change (({v : Fin k → NumberField.RingOfIntegers K |
      ∀ i, mahlerK K (((v i) : NumberField.RingOfIntegers K) : K) ≤ Y} :
        Set (Fin k → NumberField.RingOfIntegers K)).ncard : ℝ)
      ≤ ((200000 : ℝ) ^ (Module.finrank ℚ K) * Y *
          (1 + Real.log Y) ^ (Module.finrank ℚ K - 1)) ^ k
  set S : Set (NumberField.RingOfIntegers K) :=
    {α | mahlerK K (((α : NumberField.RingOfIntegers K) : K)) ≤ Y} with hS
  -- The set of admissible tuples is the `k`-th power of the set of admissible elements.
  have hT : (({v : Fin k → NumberField.RingOfIntegers K |
      ∀ i, mahlerK K (((v i) : NumberField.RingOfIntegers K) : K) ≤ Y} : Set _).ncard)
      = S.ncard ^ k := by
    rw [hS]
    exact ncard_pi_const_pow (fun α : NumberField.RingOfIntegers K =>
      mahlerK K (((α : NumberField.RingOfIntegers K) : K)) ≤ Y) k
  -- The single-element count: `mahler_card_le`.
  have hSbound : (S.ncard : ℝ)
      ≤ (200000 : ℝ) ^ (Module.finrank ℚ K) * Y * (1 + Real.log Y) ^ (Module.finrank ℚ K - 1) := by
    rw [← Nat.card_coe_set_eq (s := S)]
    change (Nat.card {α : NumberField.RingOfIntegers K //
      mahlerK K (((α : NumberField.RingOfIntegers K) : K)) ≤ Y} : ℝ) ≤ _
    exact mahler_card_le hk Y hY
  have hT' : (({v : Fin k → NumberField.RingOfIntegers K |
      ∀ i, mahlerK K (((v i) : NumberField.RingOfIntegers K) : K) ≤ Y} : Set _).ncard : ℝ)
      = (S.ncard : ℝ) ^ k := by
    rw [hT, Nat.cast_pow]
  rw [hT']
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hSbound k

end

end Commons.NumberTheory.NumberField
