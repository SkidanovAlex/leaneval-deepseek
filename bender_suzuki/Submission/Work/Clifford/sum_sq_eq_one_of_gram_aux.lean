import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Clifford

/-- Expansion of `Σ_x (Σ_y a x y * f y)^2` as a double sum over `Y`,
using nonnegativity of the entries. -/
theorem sum_sq_sum_eq_gram {X Y : Type*} [Fintype X] [Fintype Y] (a : X → Y → ℕ) (f : Y → ℕ) :
    ∑ x : X, (∑ y : Y, a x y * f y) ^ 2
      = ∑ y : Y, ∑ y' : Y, f y * f y' * ∑ x : X, a x y * a x y' := by
  calc ∑ x : X, (∑ y : Y, a x y * f y) ^ 2
      = ∑ x : X, ∑ y : Y, ∑ y' : Y, (a x y * f y) * (a x y' * f y') := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ y : Y, ∑ y' : Y, ∑ x : X, (a x y * f y) * (a x y' * f y') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ y : Y, ∑ y' : Y, f y * f y' * ∑ x : X, a x y * a x y' := by
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring

theorem sum_sq_eq_one_of_gram_aux {X Y : Type*} [Fintype X] [Fintype Y] (a : X → Y → ℕ) (f : Y → ℕ)
    (hdiag : ∀ y, 1 ≤ ∑ x : X, a x y * a x y)
    (hkey : ∑ x : X, (∑ y : Y, a x y * f y) ^ 2 = ∑ y : Y, f y * f y) :
    ∀ y, f y ≠ 0 → ∑ x : X, a x y * a x y = 1 := by
  intro y₀ hy₀
  -- The "diagonal" double sum equals the total sum of squares.
  have hgram : ∑ y : Y, ∑ y' : Y, f y * f y' * ∑ x : X, a x y * a x y'
      = ∑ y : Y, f y * f y := by
    rw [← sum_sq_sum_eq_gram, hkey]
  -- The diagonal part is bounded by the full double sum.
  have h1 : ∑ y : Y, f y * f y * ∑ x : X, a x y * a x y
      ≤ ∑ y : Y, ∑ y' : Y, f y * f y' * ∑ x : X, a x y * a x y' := by
    refine Finset.sum_le_sum fun y _ => ?_
    exact Finset.single_le_sum (f := fun y' => f y * f y' * ∑ x : X, a x y * a x y')
      (fun y' _ => Nat.zero_le _) (Finset.mem_univ y)
  -- And `Σ f y * f y` is bounded by the diagonal part, using `1 ≤ Σ_x a x y * a x y`.
  have h2 : ∑ y : Y, f y * f y ≤ ∑ y : Y, f y * f y * ∑ x : X, a x y * a x y := by
    refine Finset.sum_le_sum fun y _ => ?_
    calc f y * f y = f y * f y * 1 := (mul_one _).symm
      _ ≤ f y * f y * ∑ x : X, a x y * a x y := Nat.mul_le_mul_left _ (hdiag y)
  -- Combining with `hkey` all three quantities coincide.
  have heq : ∑ y : Y, f y * f y * ∑ x : X, a x y * a x y = ∑ y : Y, f y * f y := by
    refine le_antisymm ?_ h2
    rw [hgram] at h1
    exact h1
  -- Termwise equality follows from an equality of sums of a pointwise inequality.
  have hle_term : ∀ y ∈ (Finset.univ : Finset Y),
      f y * f y ≤ f y * f y * ∑ x : X, a x y * a x y := fun y _ => by
    calc f y * f y = f y * f y * 1 := (mul_one _).symm
      _ ≤ f y * f y * ∑ x : X, a x y * a x y := Nat.mul_le_mul_left _ (hdiag y)
  have hterm : f y₀ * f y₀ * ∑ x : X, a x y₀ * a x y₀ = f y₀ * f y₀ :=
    ((Finset.sum_eq_sum_iff_of_le hle_term).1 heq.symm y₀ (Finset.mem_univ y₀)).symm
  -- Cancel the positive factor `f y₀ * f y₀`.
  have hne : f y₀ * f y₀ ≠ 0 := Nat.mul_ne_zero hy₀ hy₀
  have hterm' : f y₀ * f y₀ * ∑ x : X, a x y₀ * a x y₀ = f y₀ * f y₀ * 1 := by
    rw [mul_one]
    exact hterm
  exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hne) hterm'

end Work.Clifford
