import Mathlib
import Submission.Commons.NumberTheory.NumberField.ncard_mahler_one_le
import Submission.Commons.NumberTheory.NumberField.ncard_field_tuples_le

set_option autoImplicit false

open NumberField

namespace Commons.NumberTheory.NumberField

/-- **Integral tuple count for the Mahler measure.**
The number of `k`-tuples of integral elements of a number field `K` of degree `m ≥ 2` all of whose
entries have Mahler measure at most `Y` is at most
`(200000 ^ m * Y * (1 + log Y) ^ (m - 1)) ^ k`.

Every integral element of `K` lies in the ring of integers `𝓞 K`, so the count of integral `k`-tuples
is the count of `k`-tuples of `𝓞 K` with bounded Mahler measure, which is estimated by
`ncard_field_tuples_le`. -/
theorem ncard_integral_tuple_mahler_le {K : Type*} [Field K] [NumberField K] (m : ℕ) (hm : 2 ≤ m)
    (hfr : Module.finrank ℚ K = m) (k : ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    (Nat.card {v : Fin k → K // (∀ i, IsIntegral ℤ (v i)) ∧
        ∀ i, Commons.NumberTheory.NumberField.mahlerK K (v i) ≤ Y} : ℝ)
      ≤ ((200000 : ℝ) ^ m * Y * (1 + Real.log Y) ^ (m - 1)) ^ k := by
  classical
  have hk : 2 ≤ Module.finrank ℚ K := by omega
  -- Integral elements of `K` are exactly the elements of the ring of integers `𝓞 K`, so the
  -- integral `k`-tuples correspond bijectively to the `k`-tuples of `𝓞 K`.
  have hcard : Nat.card {v : Fin k → K // (∀ i, IsIntegral ℤ (v i)) ∧
        ∀ i, mahlerK K (v i) ≤ Y}
      = Nat.card {v : Fin k → 𝓞 K // ∀ i, mahlerK K (((v i : 𝓞 K) : K)) ≤ Y} :=
    Nat.card_congr
      { toFun := fun v => ⟨fun i => ⟨v.1 i, v.2.1 i⟩, fun i => v.2.2 i⟩
        invFun := fun w => ⟨fun i => ((w.1 i : 𝓞 K) : K), ⟨fun i => (w.1 i).2, fun i => w.2 i⟩⟩
        left_inv := fun v => rfl
        right_inv := fun w => rfl }
  rw [hcard]
  -- Rewrite the `Nat.card` of the subtype as a `Set.ncard`, unfolding `mahlerK` into its
  -- defining product, so that `ncard_field_tuples_le` applies.
  have hEq : (Nat.card {v : Fin k → 𝓞 K // ∀ i, mahlerK K (((v i : 𝓞 K) : K)) ≤ Y} : ℝ)
      = (({v : Fin k → 𝓞 K | ∀ i, (∏ w : NumberField.InfinitePlace K,
          (max 1 (NumberField.mixedEmbedding.normAtPlace w
            (NumberField.mixedEmbedding K (((v i) : 𝓞 K) : K)))) ^
              NumberField.InfinitePlace.mult w) ≤ Y} : Set (Fin k → 𝓞 K)).ncard : ℝ) := rfl
  rw [hEq]
  have hle := ncard_field_tuples_le (K := K) hk k Y hY
  rw [hfr] at hle
  exact hle

end Commons.NumberTheory.NumberField
