import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Commons.Algebra.Multinomial

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The operator "multiply the coefficient function `Q` by the monomial `x_v`", i.e. the
downward shift of the `v`-th multi-index (with the empty monomial on the boundary). -/
private def shift (v : ι) (Q : (ι → ℕ) → ℕ) : (ι → ℕ) → ℕ :=
  fun m => if 1 ≤ m v then Q (m - (Pi.single v (1:ℕ) : ι → ℕ)) else 0

/-- The operator `Q ↦ (c + Σ_v d_v x_v)·Q` of the statement, written in the same (`if`-based)
shape as the goal so that `change` can recognise it definitionally. -/
private def op (c : ℕ) (d : ι → ℕ) (Q : (ι → ℕ) → ℕ) : (ι → ℕ) → ℕ :=
  fun m => c * Q m + ∑ v, if 1 ≤ m v then d v * Q (m - (Pi.single v (1:ℕ) : ι → ℕ)) else 0

private lemma ite_ite_zero (p q : Prop) [Decidable p] [Decidable q] (A : ℕ) :
    (if p then (if q then A else 0) else 0) = if p ∧ q then A else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

omit [Fintype ι] in
private lemma sub_shift_comm (m : ι → ℕ) (u v : ι) :
    (m - (Pi.single v (1:ℕ) : ι → ℕ)) - (Pi.single u (1:ℕ) : ι → ℕ)
      = (m - (Pi.single u (1:ℕ) : ι → ℕ)) - (Pi.single v (1:ℕ) : ι → ℕ) := by
  funext x
  simp only [Pi.sub_apply]
  omega

omit [Fintype ι] in
private lemma cond_iff (m : ι → ℕ) (u v : ι) :
    (1 ≤ m v ∧ 1 ≤ (m - (Pi.single v (1:ℕ) : ι → ℕ)) u)
      ↔ (1 ≤ m u ∧ 1 ≤ (m - (Pi.single u (1:ℕ) : ι → ℕ)) v) := by
  by_cases huv : u = v
  · subst huv; rfl
  · have h1 : (m - (Pi.single v (1:ℕ) : ι → ℕ)) u = m u := by
      simp [Pi.sub_apply, huv]
    have h2 : (m - (Pi.single u (1:ℕ) : ι → ℕ)) v = m v := by
      simp [Pi.sub_apply, Ne.symm huv]
    rw [h1, h2]
    constructor <;> intro h <;> exact ⟨h.2, h.1⟩

/-- The elementary shifts `x_v`, `x_u` commute as operators on coefficient functions. -/
private lemma shift_comm (v u : ι) (Q : (ι → ℕ) → ℕ) :
    shift v (shift u Q) = shift u (shift v Q) := by
  funext m
  simp only [shift]
  rw [ite_ite_zero, ite_ite_zero]
  rw [sub_shift_comm m u v]
  exact if_congr (cond_iff m u v) rfl rfl

private lemma op_apply (c : ℕ) (d : ι → ℕ) (Q : (ι → ℕ) → ℕ) (m : ι → ℕ) :
    op c d Q m = c * Q m + ∑ v, d v * shift v Q m := by
  simp only [op, shift, mul_ite, mul_zero]

private lemma shift_op_apply (v : ι) (c : ℕ) (d : ι → ℕ) (Q : (ι → ℕ) → ℕ) (m : ι → ℕ) :
    shift v (op c d Q) m = c * shift v Q m + ∑ u, d u * shift v (shift u Q) m := by
  unfold op shift
  by_cases h : 1 ≤ m v
  · simp only [h, if_true, mul_ite, mul_zero]
  · simp only [h, if_false, mul_zero, Finset.sum_const_zero, add_zero]

/-- The two double sums arising from `(Σ_v d_v x_v)(Σ_u d'_u x_u)Q` agree, using that the
shifts commute. -/
private lemma dsum (d d' : ι → ℕ) (Q : (ι → ℕ) → ℕ) (m : ι → ℕ) :
    (∑ x, ∑ y, d y * (d' x * shift x (shift y Q) m))
      = (∑ x, ∑ y, d x * (d' y * shift x (shift y Q) m)) := by
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [shift_comm]

private lemma op_comm (c c' : ℕ) (d d' : ι → ℕ) (Q : (ι → ℕ) → ℕ) (m : ι → ℕ) :
    op c d (op c' d' Q) m = op c' d' (op c d Q) m := by
  simp only [op_apply, shift_op_apply]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  simp only [mul_left_comm, mul_comm, mul_assoc]
  conv_rhs => rw [dsum]
  ring

/-- **Commutativity of "binomial" coefficient operators.**  For a finite index type `ι`, the
operator `Q ↦ (c + Σ_v d_v x_v)·Q` on coefficient functions `(ι → ℕ) → ℕ` of a polynomial ring
with `ι` variables, applied to a second such operator with data `(c', d')`, commutes.  Concretely,
the two iterated sums in the expansion of `(c + Σ d_v x_v)(c' + Σ d'_u x_u)·Q` agree. -/
theorem mulBin_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (c c' : ℕ) (d d' : ι → ℕ)
    (Q : (ι → ℕ) → ℕ) (m : ι → ℕ) :
    (c * (c' * Q m + ∑ v : ι, if 1 ≤ m v then d' v * Q (m - (Pi.single v (1:ℕ) : ι → ℕ)) else 0)
      + ∑ v : ι, if 1 ≤ m v then
          d v * (c' * Q (m - (Pi.single v (1:ℕ) : ι → ℕ))
            + ∑ u : ι, if 1 ≤ (m - (Pi.single v (1:ℕ) : ι → ℕ)) u then
                d' u * Q ((m - (Pi.single v (1:ℕ) : ι → ℕ)) - (Pi.single u (1:ℕ) : ι → ℕ)) else 0)
        else 0)
    = (c' * (c * Q m + ∑ v : ι, if 1 ≤ m v then d v * Q (m - (Pi.single v (1:ℕ) : ι → ℕ)) else 0)
      + ∑ v : ι, if 1 ≤ m v then
          d' v * (c * Q (m - (Pi.single v (1:ℕ) : ι → ℕ))
            + ∑ u : ι, if 1 ≤ (m - (Pi.single v (1:ℕ) : ι → ℕ)) u then
                d u * Q ((m - (Pi.single v (1:ℕ) : ι → ℕ)) - (Pi.single u (1:ℕ) : ι → ℕ)) else 0)
        else 0) := by
  change op c d (op c' d' Q) m = op c' d' (op c d Q) m
  exact op_comm c c' d d' Q m

end Commons.Algebra.Multinomial
