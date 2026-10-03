/-
The `A × A`-sum of the box form of a shifted product family.

For a finite index set `A`, a shift `β : A → ℤ` and a family of slots `u`, the doubly indexed
sum of the box forms

  `∑_{a, a'} winForm n Q W (u_ω (· + β a) · conj (u_ω (· + β a')))`

reassembles, after `winForm_shift_prod_halfProd` and an exchange of the `(a, a')`-sums with the
`(z, z', x)`-sums, into `∑_{z,z'} ∑_{x∈W} |∑_a halfProd n Q u z z' x (β a)|²`, i.e. into the
squared modulus of the sum of the half-products over the shift family.  This is the
"sum over the shift family" identity used in the Cauchy--Schwarz step of the box-norm induction.
-/
import Mathlib
import Submission.Work.Peluse.BoxNorm.WinHalf

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.BoxNorm

noncomputable section

/-- Exchange of the two inner sums with the `p`-sum: for a doubly indexed family `g`,
`∑ a ∑ a' ∑ p ∑ x∈W g = ∑ p ∑ x∈W ∑ a ∑ a' g`.  (Four nested sums, moved from the order
`a, a', p, W` to the order `p, W, a, a'`; only the two innermost sums over `A` have equal type,
so the rewrites are done in the order `(a', p)`, `(a, p)`, `(a', W)`, `(a, W)`.) -/
lemma sum_reorder_prod {A P : Type*} [Fintype A] [Fintype P] (W : Finset ℤ)
    (g : A → A → P → ℤ → ℂ) :
    (∑ a : A, ∑ a' : A, ∑ p : P, ∑ x ∈ W, g a a' p x)
      = ∑ p : P, ∑ x ∈ W, ∑ a : A, ∑ a' : A, g a a' p x := by
  calc (∑ a : A, ∑ a' : A, ∑ p : P, ∑ x ∈ W, g a a' p x)
      = ∑ a : A, ∑ p : P, ∑ a' : A, ∑ x ∈ W, g a a' p x := by
          refine Finset.sum_congr rfl fun a _ => ?_
          exact Finset.sum_comm
    _ = ∑ p : P, ∑ a : A, ∑ a' : A, ∑ x ∈ W, g a a' p x := Finset.sum_comm
    _ = ∑ p : P, ∑ x ∈ W, ∑ a : A, ∑ a' : A, g a a' p x := by
          refine Finset.sum_congr rfl fun p _ => ?_
          calc (∑ a : A, ∑ a' : A, ∑ x ∈ W, g a a' p x)
              = ∑ a : A, ∑ x ∈ W, ∑ a' : A, g a a' p x := by
                  refine Finset.sum_congr rfl fun a _ => ?_
                  exact Finset.sum_comm
            _ = ∑ x ∈ W, ∑ a : A, ∑ a' : A, g a a' p x := Finset.sum_comm

theorem winForm_shift_sum_star {n : ℕ} {A : Type*} [Fintype A] (Q : Fin n → Finset ℤ)
    (W : Finset ℤ) (u : (Fin n → Bool) → ℤ → ℂ) (β : A → ℤ) :
    (∑ a : A, ∑ a' : A,
        winForm n Q W (fun ω y => u ω (y + β a) * star (u ω (y + β a'))))
      = ∑ p : Tuple n Q × Tuple n Q, ∑ x ∈ W,
          ((‖∑ a : A, halfProd n Q u p.1 p.2 x (β a)‖ ^ 2 : ℝ) : ℂ) := by
  -- Expand each box form into the double sum of half-products.
  have hL : (∑ a : A, ∑ a' : A,
        winForm n Q W (fun ω y => u ω (y + β a) * star (u ω (y + β a'))))
      = ∑ a : A, ∑ a' : A, ∑ z : Tuple n Q, ∑ z' : Tuple n Q, ∑ x ∈ W,
          halfProd n Q u z z' x (β a) * star (halfProd n Q u z z' x (β a')) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [winForm_shift_prod_halfProd]
  rw [hL]
  -- Regroup the two `Tuple`-sums as a sum over the product type.
  have hstep : (∑ a : A, ∑ a' : A, ∑ z : Tuple n Q, ∑ z' : Tuple n Q, ∑ x ∈ W,
        halfProd n Q u z z' x (β a) * star (halfProd n Q u z z' x (β a')))
      = ∑ a : A, ∑ a' : A, ∑ p : Tuple n Q × Tuple n Q, ∑ x ∈ W,
        halfProd n Q u p.1 p.2 x (β a) * star (halfProd n Q u p.1 p.2 x (β a')) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    rw [← Finset.sum_product']
    simp
  rw [hstep]
  -- Move the `p`-sum outside the `(a, a')`-sums.
  rw [sum_reorder_prod W (fun (a : A) (a' : A) (p : Tuple n Q × Tuple n Q) (x : ℤ) =>
        halfProd n Q u p.1 p.2 x (β a) * star (halfProd n Q u p.1 p.2 x (β a')))]
  -- Inner identity: `∑ a ∑ a' H a · conj (H a') = ‖∑ a H a‖²`.
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun x _ => ?_
  exact pairSum_star (fun a : A => halfProd n Q u p.1 p.2 x (β a))

end

end Work.Peluse.BoxNorm
