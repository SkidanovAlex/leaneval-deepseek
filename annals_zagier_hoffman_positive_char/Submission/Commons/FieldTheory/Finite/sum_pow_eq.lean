import Mathlib.FieldTheory.Finite.Basic

namespace Commons.FieldTheory.Finite

theorem sum_pow_eq {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {i : ℕ} (hi : 0 < i) :
    (∑ x : K, x ^ i) = if Fintype.card K - 1 ∣ i then (-1 : K) else 0 := by
  classical
  let φ : Kˣ ↪ K := ⟨fun x ↦ x, Units.val_injective⟩
  have hmap : Finset.univ.map φ = Finset.univ \ {0} := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Finset.mem_singleton, φ]
    exact isUnit_iff_ne_zero
  calc
    (∑ x : K, x ^ i) = ∑ x ∈ Finset.univ \ {(0 : K)}, x ^ i := by
      rw [← Finset.sum_sdiff (Finset.singleton_subset_iff.mpr (Finset.mem_univ 0))]
      simp [zero_pow (Nat.ne_of_gt hi)]
    _ = ∑ x : Kˣ, (x ^ i : K) := by
      rw [← hmap, Finset.sum_map]
      simp [φ]
    _ = if Fintype.card K - 1 ∣ i then (-1 : K) else 0 :=
      FiniteField.sum_pow_units K i

end Commons.FieldTheory.Finite
