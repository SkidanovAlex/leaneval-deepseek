import Mathlib

namespace Commons.Combinatorics.Transference

/-- The conditional-expectation operator on a finite type with respect to a
partition `part` (given by a map `X → Finset X` whose values are the parts) is
self-adjoint for the standard inner product `⟨f, g⟩ = ∑ x, f x * g x`, in the
sense that `∑ x, (E f) x * h x = ∑ x, f x * h x` for every function `h` that is
constant on each part (i.e. `h` lies in the range of `E`). -/
theorem condExp_selfadjoint {X : Type*} [Fintype X] [DecidableEq X] (part : X → Finset X)
    (hmem : ∀ x, x ∈ part x) (heq : ∀ x y : X, y ∈ part x → part y = part x) (f h : X → ℝ)
    (hh : ∀ x y : X, y ∈ part x → h y = h x) :
    ∑ x, (((part x).card : ℝ)⁻¹ * ∑ y ∈ part x, f y) * h x = ∑ x, f x * h x := by
  -- The parts are the equivalence classes of the relation `y ∈ part x`: consequently
  -- `y ∈ part x ↔ x ∈ part y`.
  have hsymm : ∀ x y : X, y ∈ part x ↔ x ∈ part y := by
    intro x y
    constructor
    · intro hy
      rw [heq x y hy]
      exact hmem x
    · intro hx
      rw [heq y x hx]
      exact hmem y
  have hcard_ne : ∀ y : X, (part y).card ≠ 0 := by
    intro y
    exact Nat.pos_iff_ne_zero.mp (Finset.card_pos.mpr ⟨y, hmem y⟩)
  calc
    ∑ x, (((part x).card : ℝ)⁻¹ * ∑ y ∈ part x, f y) * h x
        = ∑ x, ∑ y ∈ part x, ((part y).card : ℝ)⁻¹ * f y * h y := by
          apply Finset.sum_congr rfl
          intro x _
          rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y hy
          rw [← heq x y hy, ← hh x y hy]
          ring
    -- Swap the order of summation; the double sum ranges over pairs `y ∈ part x`,
    -- i.e. equivalently over pairs `x ∈ part y`.
    _ = ∑ y, ∑ x ∈ part y, ((part y).card : ℝ)⁻¹ * f y * h y := by
          apply Finset.sum_comm'
          intro x y
          simp only [Finset.mem_univ, true_and, and_true]
          exact hsymm x y
    -- Each inner sum has `(part y).card` terms equal to `(part y).card⁻¹ * f y * h y`.
    _ = ∑ y, f y * h y := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_const, nsmul_eq_mul]
          have hc : ((part y).card : ℝ) ≠ 0 := by exact_mod_cast hcard_ne y
          field_simp

end Commons.Combinatorics.Transference
