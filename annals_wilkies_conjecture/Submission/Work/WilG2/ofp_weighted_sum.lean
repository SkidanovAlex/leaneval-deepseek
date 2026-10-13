import Submission.Work.WilG2.Bijection
import Submission.Work.WilG2.InvData.left_inv
import Submission.Work.WilG2.InvData.right_inv
import Mathlib.Combinatorics.Enumerative.Composition

set_option autoImplicit false
noncomputable section

open Finset

namespace Work.WilG2

/-- The bijection between decorated ordered finpartitions of `Fin m` and pairs
(size datum of `m`, permutation of `Fin m`). -/
@[reducible] noncomputable def ofpDataEquiv (m : ℕ) :
    OFPData m ≃ (SizeData m × Equiv.Perm (Fin m)) where
  toFun := toMid
  invFun p := invData p.1 p.2
  left_inv := fun x => InvData.left_inv m x
  right_inv := fun p => InvData.right_inv m p

/-- **The weighted sum over ordered finpartitions, rewritten as a sum over compositions.**

The number of ordered set partitions of `Fin m` with a given ordered sequence of block sizes
`(s i)` is `m!/∏ i, (s i)!`, and each contributes the weight of its block sizes; summing over
all decorated ordered finpartitions (block sizes, block order, internal orders) is exactly the
bijection between decorated ordered finpartitions and pairs (composition, permutation). -/
theorem ofp_weighted_sum (m : ℕ) (a bg : ℕ → ℝ) :
    (∑ c : OrderedFinpartition m,
        ((c.length.factorial : ℝ) * ∏ i : Fin c.length, ((c.partSize i).factorial : ℝ)) *
          (bg c.length * ∏ i : Fin c.length, a (c.partSize i)))
      = (m.factorial : ℝ) *
          ∑ c : Composition m, bg c.length * ∏ i : Fin c.length, a (c.blocksFun i) := by
  rw [← sum_ofpData a bg]
  rw [Fintype.sum_equiv (ofpDataEquiv m) (ofpDataWeight a bg) (midWeight a bg)
    (fun x => ofpDataWeight_eq_midWeight a bg x)]
  rw [Fintype.sum_prod_type]
  have h1 : ∀ y : SizeData m,
      (∑ ρ : Equiv.Perm (Fin m), midWeight a bg (y, ρ)) =
      (m.factorial : ℝ) * (bg (SizeData.len y) *
        ∏ i : Fin (SizeData.len y), a (SizeData.sizes y i)) := by
    intro y
    show (∑ _ : Equiv.Perm (Fin m), (bg (SizeData.len y) *
        ∏ i : Fin (SizeData.len y), a (SizeData.sizes y i))) = _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul]
  rw [Finset.sum_congr rfl fun y _ => h1 y]
  rw [← Finset.mul_sum]
  congr 1
  exact (Fintype.sum_equiv (sizeDataEquiv m).symm
    (fun c : Composition m => bg c.length * ∏ i : Fin c.length, a (c.blocksFun i))
    (fun y : SizeData m => bg (SizeData.len y) *
      ∏ i : Fin (SizeData.len y), a (SizeData.sizes y i))
    (fun c => rfl)).symm

end Work.WilG2
