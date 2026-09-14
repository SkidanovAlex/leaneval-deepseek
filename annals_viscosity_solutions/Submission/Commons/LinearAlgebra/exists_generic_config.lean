import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra

/-- In a nontrivial real vector space `E` (in particular infinite), given two configurations
`x y : Fin N → E`, there is a configuration `z` whose coordinates are pairwise distinct and
distinct from all coordinates of `x` and of `y`. -/
theorem exists_generic_config {E : Type*} [AddCommGroup E] [Module ℝ E] [Nontrivial E] {N : ℕ}
    (x y : Fin N → E) :
    ∃ z : Fin N → E, (∀ i j, i ≠ j → z i ≠ z j) ∧ (∀ i j, z i ≠ x j) ∧ (∀ i j, z i ≠ y j) := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  -- For a fixed target `w`, the set of scalars `a` with `a • v = w` is a subsingleton.
  have hsub : ∀ w : E, Set.Subsingleton {a : ℝ | a • v = w} := by
    intro w a₁ h₁ a₂ h₂
    have h : (a₁ - a₂) • v = 0 := by rw [sub_smul, h₁, h₂, sub_self]
    have h' : a₁ - a₂ = 0 := by
      rcases smul_eq_zero.mp h with h0 | h0
      · exact h0
      · exact absurd h0 hv
    exact sub_eq_zero.mp h'
  -- The set of "bad" scalars: those whose affine line through `v` hits some `x j` or `y j`.
  have hfin1 : (⋃ (i : Fin N), ⋃ (j : Fin N), {a : ℝ | a • v = x j - (i : ℝ) • v}).Finite := by
    refine Set.finite_iUnion fun i => Set.finite_iUnion fun j => ?_
    exact (hsub _).finite
  have hfin2 : (⋃ (i : Fin N), ⋃ (j : Fin N), {a : ℝ | a • v = y j - (i : ℝ) • v}).Finite := by
    refine Set.finite_iUnion fun i => Set.finite_iUnion fun j => ?_
    exact (hsub _).finite
  obtain ⟨a, ha⟩ := (hfin1.union hfin2).exists_notMem
  rw [Set.mem_union, not_or] at ha
  refine ⟨fun i => a • v + (i : ℝ) • v, ?_, ?_, ?_⟩
  · -- pairwise distinct
    intro i j hij h
    have h₂ : (i : ℝ) • v = (j : ℝ) • v := add_left_cancel h
    have h₃ : ((i : ℝ) - (j : ℝ)) • v = 0 := by rw [sub_smul, h₂, sub_self]
    have h₄ : (i : ℝ) - (j : ℝ) = 0 := by
      rcases smul_eq_zero.mp h₃ with h0 | h0
      · exact h0
      · exact absurd h0 hv
    exact hij (Fin.ext (Nat.cast_injective (sub_eq_zero.mp h₄)))
  · -- distinct from the coordinates of `x`
    intro i j h
    have hx : a • v = x j - (i : ℝ) • v := eq_sub_iff_add_eq.mpr h
    exact ha.1 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hx⟩⟩)
  · -- distinct from the coordinates of `y`
    intro i j h
    have hy : a • v = y j - (i : ℝ) • v := eq_sub_iff_add_eq.mpr h
    exact ha.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hy⟩⟩)

end Commons.LinearAlgebra