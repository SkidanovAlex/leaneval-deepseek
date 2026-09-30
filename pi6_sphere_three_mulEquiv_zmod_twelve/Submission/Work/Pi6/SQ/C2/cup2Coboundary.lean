import Mathlib
import Submission.Work.Pi6.SQM.Defs
import Submission.Work.Pi6.SQ.C2.Cup2Setup
import Submission.Work.Pi6.SQ.C2.lhsExpand
import Submission.Work.Pi6.SQ.C2.rhsExpandT12
import Submission.Work.Pi6.SQ.C2.rhsExpandC34
import Submission.Work.Pi6.SQ.C2.cobTerm_swap
import Submission.Work.Pi6.SQ.C2.cobSwap_involutive
import Submission.Work.Pi6.SQ.C2.cobSwap_ne
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! The mod-2 `∪₂` coboundary formula (area SQ, SQM piece).

`Work.Pi6.SQM.Cup2Cob` states

  `δ(u ∪₂ v) = u ∪₁ v + v ∪₁ u + (δu) ∪₂ v + u ∪₂ (δv)`

for area SQ's `cup2`/`cup1m` (Steenrod's interval products) over `𝔽₂`.

The proof evaluates both sides of the cochain identity at an `(n+m-1)`-simplex `σ` as sums of
products `u(F)·v(G)` over explicit families of faces (`Cup2CobSetup.lhsExpand`,
`rhsExpandT12`, `rhsExpandC34`), and concludes with the fixed-point-free pairing involution
`cobSwap` of `Cup2CobSetup`, which preserves the term (`cobTerm_swap`) and has no fixed point
(`cobSwap_ne`) and is involutive (`cobSwap_involutive`): `Finset.sum_involution` then gives
that the sum of all terms is zero, i.e. `LHS + RHS = 0`, hence `LHS = RHS`.
-/

set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQ.C2

open Work.Pi6.SQM (F2)

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

/-- The coboundary formula with the four degree transports as explicit hypotheses. -/
theorem cup2Cob_aux (X : SSet) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m)
    (hcast : (n + m - 2) + 1 = n + m - 1) (h1 : m + n - 1 = n + m - 1)
    (h2 : (n + 1) + m - 2 = n + m - 1) (h3 : n + (m + 1) - 2 = n + m - 1) :
    hcast ▸ cochainDiff F2 X (Work.Pi6.SQ.cup2 X n m u v)
      = Work.Pi6.SQ.cup1m X n m u v + h1 ▸ Work.Pi6.SQ.cup1m X m n v u +
        h2 ▸ Work.Pi6.SQ.cup2 X (n + 1) m (cochainDiff F2 X u) v +
        h3 ▸ Work.Pi6.SQ.cup2 X n (m + 1) u (cochainDiff F2 X v) := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Cohomology.genEval_add, Work.Cohomology.genEval_add, Work.Cohomology.genEval_add]
  rw [lhsExpand X n m hn hm u v σ hcast,
    (rhsExpandT12 X n m hn hm u v σ h1).1, (rhsExpandT12 X n m hn hm u v σ h1).2,
    (rhsExpandC34 X n m hn hm u v σ h2 h3).1, (rhsExpandC34 X n m hn hm u v σ h2 h3).2]
  -- the sum over the disjoint union of all five index families vanishes
  have hsum : ∑ x : cobIdx n m, cobTerm X n m hn hm u v σ x = 0 := by
    refine Finset.sum_involution (s := Finset.univ)
      (f := cobTerm X n m hn hm u v σ) (g := fun x _ => cobSwap n m hn hm x) ?_ ?_ ?_ ?_
    · intro x _
      rw [cobTerm_swap X n m hn hm u v σ x]
      exact CharTwo.add_self_eq_zero _
    · intro x _ _
      exact cobSwap_ne n m hn hm x
    · intro x _
      exact Finset.mem_univ (cobSwap n m hn hm x)
    · intro x _
      exact cobSwap_involutive n m hn hm x
  have hdecomp : ∑ x : cobIdx n m, cobTerm X n m hn hm u v σ x
      = (∑ i : LIdx n m, lTerm X n m hn hm u v σ i)
        + ((∑ i : C3Idx n m, c3Term X n m u v σ i)
          + ((∑ i : C4Idx n m, c4Term X n m u v σ i)
            + ((∑ s : Fin n, t1Term X n m u v σ s)
              + (∑ s : Fin m, t2Term X n m u v σ s)))) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [cobTerm, Sum.elim_inl, Sum.elim_inr]
  have h5 : (∑ i : LIdx n m, lTerm X n m hn hm u v σ i)
      + ((∑ i : C3Idx n m, c3Term X n m u v σ i)
        + ((∑ i : C4Idx n m, c4Term X n m u v σ i)
          + ((∑ s : Fin n, t1Term X n m u v σ s)
            + (∑ s : Fin m, t2Term X n m u v σ s)))) = 0 := by
    rw [← hdecomp]
    exact hsum
  have h6 : (∑ i : LIdx n m, lTerm X n m hn hm u v σ i)
      = (∑ s : Fin n, t1Term X n m u v σ s) + (∑ s : Fin m, t2Term X n m u v σ s)
        + (∑ i : C3Idx n m, c3Term X n m u v σ i)
        + (∑ i : C4Idx n m, c4Term X n m u v σ i) := by
    have h7 := eq_neg_of_add_eq_zero_left h5
    rw [h7, CharTwo.neg_eq]
    abel
  rw [h6]

theorem cup2CoboundaryM : Work.Pi6.SQM.Cup2Cob := by
  intro X n m u v hn hm
  exact cup2Cob_aux X n m hn hm u v (by omega) (by omega) (by omega) (by omega)

end

end Work.Pi6.SQ.C2
