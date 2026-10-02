import Mathlib
import Submission.Work.Whitney.ChernRelDefs
import Submission.Work.Whitney.ChernRelSeries

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Commutativity of the convolution of two even-degree series

`Work.LerayHirsch.convSeries x y k = ∑_{i ≤ k} x_i ⌣ y_{k-i}` is the `k`-th coefficient of the
graded product of the two series `x`, `y : (i : ℕ) → Coh ℤ (2*i) B`.  Because every term lives in
an *even* degree, the cup product is commutative *without sign* (`Work.Cohomology.gradedComm` with
`(-1)^{(2i)(2(k-i))} = 1`), and hence the convolution itself is commutative:

`Work.Whitney.convSeries_comm : convSeries x y = convSeries y x`.

The only substance is the bookkeeping: `convTerm x y k i` is built from `x i` and `y (k-i)`, while
`convTerm y x k (k-i)` is built from `y (k-i)` and `x (k-(k-i))`, so the second factor has to be
transported along the degree cast of `k - (k-i) = i` (`Work.Whitney.apply_cohTransport`).  The
reindexing `i ↦ k-i` of the finite sum is `Finset.sum_range_reflect`.

* `Work.Whitney.apply_cohTransport` — a dependent function on `ℕ` is transported by the degree cast
  along an equality of indices;
* `Work.Whitney.convTerm_comm` — the summand of the convolution is symmetric;
* `Work.Whitney.convSeries_comm` — **the convolution is commutative**.
-/

namespace Work.Whitney

noncomputable section

/-- **Transport of a series along an equality of indices.**  For a family of types
`t ↦ Coh ℤ (2*t) B` and a dependent function `x` on the indices, `x n` is the degree cast of
`x m` when `n = m`: this is the degree cast bookkeeping that lets one reindex such a series by a
propositionally equal (but not definitionally equal) index. -/
theorem apply_cohTransport {B : Type} [TopologicalSpace B] {n m : ℕ} (h : n = m)
    (x : (t : ℕ) → Work.Thom.Coh ℤ (2 * t) B) :
    x n = Work.Thom.cohTransport (congrArg (fun t : ℕ => 2 * t) h).symm (x m) := by
  cases h
  rw [Work.Thom.cohTransport_rfl]

/-- **The summand of the convolution is symmetric.**  For `i ≤ k`,
`Work.LerayHirsch.convTerm x y k i = Work.LerayHirsch.convTerm y x k (k - i)`: the cup product
`x i ⌣ y (k-i)` equals `y (k-i) ⌣ x i` because both degrees `2*i` and `2*(k-i)` are even (so the
Koszul sign is `+1`, `Work.Cohomology.gradedComm`), and the two sides are compared after the degree
bookkeeping `k - (k-i) = i`. -/
theorem convTerm_comm {B : Type} [TopologicalSpace B]
    {x y : (i : ℕ) → Work.Thom.Coh ℤ (2 * i) B} {k i : ℕ} (h : i ≤ k) :
    Work.LerayHirsch.convTerm x y k i = Work.LerayHirsch.convTerm y x k (k - i) := by
  rw [Work.LerayHirsch.convTerm_pos h, Work.LerayHirsch.convTerm_pos (Nat.sub_le k i)]
  -- the second factor `x (k - (k - i))` of the right-hand side is the cast of `x i`
  have hx : x (k - (k - i))
      = Work.Thom.cohTransport
          (congrArg (fun t : ℕ => 2 * t) (Nat.sub_sub_self h)).symm (x i) :=
    apply_cohTransport (Nat.sub_sub_self h) x
  rw [hx]
  rw [Work.LerayHirsch.cupH'_cast_right (n := 2 * (k - i)) (m := 2 * i)
    (m' := 2 * (k - (k - i))) (congrArg (fun t : ℕ => 2 * t) (Nat.sub_sub_self h)).symm
    (y (k - i)) (x i)]
  rw [Work.Whitney.cohTransport_trans]
  -- even-degree commutativity of the cup product: the sign is `(-1)^(4 i (k-i)) = 1`
  have hsign : (-1 : ℤ) ^ ((2 * i) * (2 * (k - i))) = 1 := by
    rw [show (2 * i) * (2 * (k - i)) = 2 * (2 * (i * (k - i))) by ring]
    exact Even.neg_one_pow ⟨2 * (i * (k - i)), by ring⟩
  have hg := Work.Cohomology.gradedComm ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i))
    (x i) (y (k - i))
  rw [hsign, one_smul] at hg
  rw [Work.LerayHirsch.eqRec_eq_cohTransport] at hg
  have hg' : Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * i) (2 * (k - i))
        (x i) (y (k - i))
      = Work.Thom.cohTransport (Nat.add_comm (2 * i) (2 * (k - i))).symm
          (Work.Cohomology.cupH' ℤ (Work.Whitney.ssB B) (2 * (k - i)) (2 * i)
            (y (k - i)) (x i)) :=
    (Work.Whitney.ChernRel.cohTransport_apply_symm _ _).symm.trans
      (congrArg (Work.Thom.cohTransport (Nat.add_comm (2 * i) (2 * (k - i))).symm) hg)
  rw [hg']
  refine (Work.Whitney.cohTransport_trans _ _ _).trans ?_
  exact Work.LerayHirsch.cohTransport_congr_proof _ _

/-- **Commutativity of the convolution of two even-degree series**:
`Work.LerayHirsch.convSeries x y = Work.LerayHirsch.convSeries y x`. -/
theorem convSeries_comm {B : Type} [TopologicalSpace B]
    (x y : (i : ℕ) → Work.Thom.Coh ℤ (2 * i) B) (k : ℕ) :
    Work.LerayHirsch.convSeries x y k = Work.LerayHirsch.convSeries y x k := by
  unfold Work.LerayHirsch.convSeries
  -- swap each summand, then reindex the sum by the involution `i ↦ k - i`
  rw [show (∑ i ∈ Finset.range (k + 1), Work.LerayHirsch.convTerm x y k i)
      = ∑ i ∈ Finset.range (k + 1), Work.LerayHirsch.convTerm y x k (k - i) from
    Finset.sum_congr rfl (fun i hi =>
      convTerm_comm (by simpa [Finset.mem_range] using hi))]
  rw [← Finset.sum_range_reflect (fun j => Work.LerayHirsch.convTerm y x k j) (k + 1)]
  exact Finset.sum_congr rfl
    (fun i _ => congrArg (Work.LerayHirsch.convTerm y x k) (by omega))

end

end Work.Whitney
