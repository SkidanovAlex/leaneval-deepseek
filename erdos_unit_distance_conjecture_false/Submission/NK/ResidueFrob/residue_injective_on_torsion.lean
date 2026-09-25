import Mathlib

namespace NK.ResidueFrob

/-- In a local ring, a unit plus an element of the maximal ideal is a unit. -/
lemma isUnit_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : IsUnit a) (hb : b ∈ IsLocalRing.maximalIdeal R) : IsUnit (a + b) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add,
    (IsLocalRing.residue_eq_zero_iff b).mpr hb, add_zero]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit a).mpr ha

theorem residue_injective_on_torsion {R : Type*} [CommRing R] [IsLocalRing R]
    {d : ℕ} (hd : IsUnit ((d : ℕ) : R)) {w : R} (hw : w ^ d = 1)
    (hres : IsLocalRing.residue R w = 1) : w = 1 := by
  rcases eq_or_ne d 0 with hd0 | hd0
  · -- `d = 0`: the hypothesis `IsUnit 0` forces the ring to be trivial.
    subst hd0
    simp only [Nat.cast_zero] at hd
    have h01 : (0 : R) = 1 := isUnit_zero_iff.mp hd
    have h10 : (1 : R) = 0 := h01.symm
    have hw0 : w = 0 := by rw [← mul_one w, h10, mul_zero]
    rw [hw0, h01]
  · -- `d ≠ 0`: geometric-sum argument.
    have hmem : ∀ i, w ^ i - 1 ∈ IsLocalRing.maximalIdeal R := by
      intro i
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, hres, map_one, one_pow,
        sub_self]
    have hone : (∑ i ∈ Finset.range d, (1 : R)) = (d : R) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    set S : R := ∑ i ∈ Finset.range d, w ^ i with hS
    have hSsub : S - (d : R) ∈ IsLocalRing.maximalIdeal R := by
      rw [hS, ← hone, ← Finset.sum_sub_distrib]
      exact Ideal.sum_mem _ fun i _ => hmem i
    have hSunit : IsUnit S := by
      have : S = (d : R) + (S - (d : R)) := by ring
      rw [this]
      exact isUnit_add_of_mem_maximalIdeal hd hSsub
    have hprod : (w - 1) * S = 0 := by
      rw [hS, mul_comm (w - 1), geom_sum_mul, hw, sub_self]
    have hfinal : w - 1 = 0 := (IsUnit.mul_left_eq_zero hSunit).mp hprod
    exact sub_eq_zero.mp hfinal

end NK.ResidueFrob
