import Mathlib

/-!
# The residue identity `∑ A(β)/B'(β) = [X^{n-1}] A`

If `B` is a monic polynomial with distinct roots over an algebraically closed field (`B.roots.Nodup`)
and `A` has degree `< deg B`, then

  `∑_{β ∈ B.roots} A(β) / B'(β) = A.coeff (B.natDegree - 1)`.

This is the classical Lagrange-interpolation / residue-at-infinity identity: the Lagrange
interpolation theorem for the polynomial `A` at the nodes `B.roots` expresses the coefficient of
`X^{n-1}` of `A` as the sum of `A(β)` divided by the derivative of the nodal polynomial at `β`,
and for a monic polynomial with exactly `natDegree` roots (over an algebraically closed field) the
nodal polynomial is `B` itself.
-/

namespace Work.C17

open Polynomial

/-- Over an algebraically closed field, a monic polynomial with distinct roots is the product
`∏_{β ∈ B.roots} (X - β)`; in the Lagrange notation this says that `B` is the nodal polynomial
of its own root set. -/
theorem nodal_roots_eq {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (B : Polynomial K) (hB : B.Monic) (hnodup : B.roots.Nodup) :
    Lagrange.nodal B.roots.toFinset (fun x : K => x) = B := by
  classical
  have hcard : B.roots.card = B.natDegree :=
    (IsAlgClosed.splits B).natDegree_eq_card_roots.symm
  have hval : B.roots.toFinset.val = B.roots := by
    rw [Multiset.toFinset_val, hnodup.dedup]
  rw [Lagrange.nodal_eq, Finset.prod_eq_multiset_prod, hval]
  exact prod_multiset_X_sub_C_of_monic_of_roots_card_eq hB hcard

theorem roots_sum_div_derivative {K : Type*} [Field K] [IsAlgClosed K] (A B : Polynomial K)
    (hB : B.Monic) (hnodup : B.roots.Nodup) (hdeg : A.natDegree < B.natDegree) :
    (B.roots.map (fun β => A.eval β / B.derivative.eval β)).sum = A.coeff (B.natDegree - 1) := by
  classical
  have hnodal : Lagrange.nodal B.roots.toFinset (fun x : K => x) = B :=
    nodal_roots_eq B hB hnodup
  have hval : B.roots.toFinset.val = B.roots := by
    rw [Multiset.toFinset_val, hnodup.dedup]
  have hcard : B.roots.toFinset.card = B.natDegree := by
    rw [Multiset.toFinset_card_of_nodup hnodup]
    exact (IsAlgClosed.splits B).natDegree_eq_card_roots.symm
  -- The derivative of `B` at a root `a` is the product of `a - j` over the other roots.
  have hderiv : ∀ a ∈ B.roots, B.derivative.eval a = ∏ j ∈ B.roots.toFinset.erase a, (a - j) := by
    intro a ha
    have hi : a ∈ B.roots.toFinset := Multiset.mem_toFinset.mpr ha
    have h1 := Lagrange.eval_nodal_derivative_eval_node_eq (v := fun x : K => x) hi
    rw [hnodal, Lagrange.eval_nodal] at h1
    exact h1
  have hdeg' : A.degree < ↑(B.roots.toFinset.card) := by
    rw [hcard]
    exact lt_of_le_of_lt A.degree_le_natDegree (WithBot.coe_lt_coe.mpr hdeg)
  -- Lagrange interpolation: the coefficient of `X ^ (#s - 1)` is the nodal sum.
  have key := Lagrange.coeff_eq_sum (s := B.roots.toFinset) (v := fun x : K => x)
    (Set.injOn_id _) hdeg'
  rw [← hcard, key, Finset.sum_eq_multiset_sum, hval]
  apply congrArg Multiset.sum
  exact Multiset.map_congr rfl (fun a ha => by rw [hderiv a ha])

end Work.C17
