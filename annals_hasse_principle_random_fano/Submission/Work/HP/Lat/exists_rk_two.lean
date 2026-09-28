import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP.Lat

open Work.HP

/-- A nonzero vector of `ℤ^ι` (`card ι ≥ 2`) is contained in a sublattice of rank two.

Suggested route: choose `j` such that `x` is not a `ℤ`-multiple of `Pi.single j 1` (possible since
`x ≠ 0` and there are at least two coordinates), and take `L = Submodule.span ℤ {x, Pi.single j 1}`;
the two vectors are `ℤ`-independent, so `L` has rank two
(`LinearIndependent.finrank_span_eq_card`) and contains `x` by `Submodule.subset_span`. -/
theorem exists_rk_two {ι : Type*} [Fintype ι] (x : ι → ℤ) (hx : x ≠ 0)
    (hcard : 2 ≤ Fintype.card ι) : ∃ L : Submodule ℤ (ι → ℤ), rk L = 2 ∧ x ∈ L := by
  classical
  -- A nonzero vector has a nonzero coordinate.
  have hk_ex : ∃ k, x k ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hx (funext h)
  obtain ⟨k, hk⟩ := hk_ex
  -- Since there are at least two coordinates, pick a coordinate `j ≠ k`.
  obtain ⟨j, hjk⟩ := Fintype.exists_ne_of_one_lt_card (show 1 < Fintype.card ι by omega) k
  -- `x` and the standard basis vector `e_j` are `ℤ`-linearly independent.
  have hind : LinearIndependent ℤ ![x, Pi.single j (1 : ℤ)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have hk0 : s * x k = 0 := by
      have h1 := congr_fun hst k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Pi.single_eq_of_ne (Ne.symm hjk), mul_zero, add_zero] at h1
      exact h1
    have hs : s = 0 := by
      rcases mul_eq_zero.mp hk0 with h | h
      · exact h
      · exact absurd h hk
    have ht : t = 0 := by
      have h1 := congr_fun hst j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        Pi.single_eq_same, mul_one] at h1
      rw [hs, zero_mul, zero_add] at h1
      exact h1
    exact ⟨hs, ht⟩
  refine ⟨Submodule.span ℤ (Set.range ![x, Pi.single j (1 : ℤ)]), ?_, ?_⟩
  · rw [rk, finrank_span_eq_card hind, Fintype.card_fin]
  · exact Submodule.subset_span ⟨0, by simp⟩

end Work.HP.Lat
