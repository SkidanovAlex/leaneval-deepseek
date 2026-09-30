import Mathlib
import Submission.Work.Pi6.SQM.Defs
import Submission.Work.Pi6.SQM.Cup3CobSetup
import Submission.Work.Pi6.SQM.Cup3Expand
import Submission.Work.Pi6.SQM.cup3SwapNe
import Submission.Work.Pi6.SQM.cup3SwapInvol
import Submission.Work.Pi6.SQM.cup3FaceSwapL
import Submission.Work.Pi6.SQM.cup3FaceSwapC3
import Submission.Work.Pi6.SQM.cup3FaceSwapC4
import Submission.Work.Pi6.SQM.cup3FaceSwapT1
import Submission.Work.Pi6.SQM.cup3FaceSwapT2
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The mod-2 coboundary formula for the cup-3 product

`Work.Pi6.SQM.Cup3Cob` states

  `δ(u ∪₃ v) = u ∪₂ v + v ∪₂ u + (δu) ∪₃ v + u ∪₃ (δv)`

for area SQ's `cup2` and SQM's `cup3` (Steenrod's interval products) over `𝔽₂`.

The proof evaluates both sides of the cochain identity at an `(n+m-2)`-simplex `σ` as sums of
products `u(F)·v(G)` over explicit families of faces
(`Cup3CobSetup.lhsExpand3`, `t1Expand3`, `t2Expand3`, `t3Expand3`, `t4Expand3` of
`Submission/Work/Pi6/SQM/Cup3Expand.lean`), and concludes with the fixed-point-free pairing
involution `cup3Swap` of `Cup3CobSetup`, which preserves the term (`cup3Term_swap`) and has no
fixed point (`cup3Swap_ne`) and is involutive (`cup3Swap_involutive`): `Finset.sum_involution`
then gives that the sum of all terms over the disjoint union `Idx3` of the five index families
is zero, i.e. `LHS + RHS = 0`, hence `LHS = RHS`.
-/

set_option maxHeartbeats 3200000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff)

/-- `cup3Swap` preserves the `u`-face. -/
theorem faceU_swap (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (x : Idx3 n m) :
    faceU n m hn hm (cup3Swap n m hn hm x) = faceU n m hn hm x := by
  cases x with
  | inl p => simpa using (cup3FaceSwapL n m hn hm p).1
  | inr x =>
    cases x with
    | inl p => simpa using (cup3FaceSwapC3 n m hn hm p).1
    | inr x =>
      cases x with
      | inl p => simpa using (cup3FaceSwapC4 n m hn hm p).1
      | inr x =>
        cases x with
        | inl p => simpa using (cup3FaceSwapT1 n m hn hm p).1
        | inr p => simpa using (cup3FaceSwapT2 n m hn hm p).1

/-- `cup3Swap` preserves the `v`-face. -/
theorem faceV_swap (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (x : Idx3 n m) :
    faceV n m hn hm (cup3Swap n m hn hm x) = faceV n m hn hm x := by
  cases x with
  | inl p => simpa using (cup3FaceSwapL n m hn hm p).2
  | inr x =>
    cases x with
    | inl p => simpa using (cup3FaceSwapC3 n m hn hm p).2
    | inr x =>
      cases x with
      | inl p => simpa using (cup3FaceSwapC4 n m hn hm p).2
      | inr x =>
        cases x with
        | inl p => simpa using (cup3FaceSwapT1 n m hn hm p).2
        | inr p => simpa using (cup3FaceSwapT2 n m hn hm p).2

/-- The term function is invariant under the pairing involution. -/
theorem cup3Term_swap (X : SSet) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m) (σ : X _⦋N3 n m⦌) (x : Idx3 n m) :
    cup3Term X n m hn hm u v σ (cup3Swap n m hn hm x) =
      cup3Term X n m hn hm u v σ x := by
  simp only [cup3Term]
  rw [faceU_swap, faceV_swap]

/-- The coboundary formula with the four degree transports as explicit hypotheses. -/
theorem cup3Cob_aux (X : SSet) (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m)
    (u : Cochain F2 X n) (v : Cochain F2 X m)
    (hcast : (n + m - 3) + 1 = n + m - 2) (h1 : m + n - 2 = n + m - 2)
    (h2 : (n + 1) + m - 3 = n + m - 2) (h3 : n + (m + 1) - 3 = n + m - 2) :
    hcast ▸ cochainDiff F2 X (cup3 X n m u v)
      = Work.Pi6.SQ.cup2 X n m u v + h1 ▸ Work.Pi6.SQ.cup2 X m n v u +
        h2 ▸ cup3 X (n + 1) m (cochainDiff F2 X u) v +
        h3 ▸ cup3 X n (m + 1) u (cochainDiff F2 X v) := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Cohomology.genEval_add, Work.Cohomology.genEval_add, Work.Cohomology.genEval_add]
  have e0 := Work.Cohomology.genEval_cast (p := (n + m - 3) + 1) (q := n + m - 2) hcast
    (cochainDiff F2 X (cup3 X n m u v)) σ
  have e1 := Work.Cohomology.genEval_cast (p := m + n - 2) (q := n + m - 2) h1
    (Work.Pi6.SQ.cup2 X m n v u) σ
  have e2 := Work.Cohomology.genEval_cast (p := (n + 1) + m - 3) (q := n + m - 2) h2
    (cup3 X (n + 1) m (cochainDiff F2 X u) v) σ
  have e3 := Work.Cohomology.genEval_cast (p := n + (m + 1) - 3) (q := n + m - 2) h3
    (cup3 X n (m + 1) u (cochainDiff F2 X v)) σ
  rw [e0, e1, e2, e3]
  rw [lhsExpand3 X n m hn hm u v σ hcast, t1Expand3 X n m hn hm u v σ,
    t2Expand3 X n m hn hm u v σ h1, t3Expand3 X n m hn hm u v σ h2,
    t4Expand3 X n m hn hm u v σ h3]
  -- the sum over the disjoint union of all five index families vanishes
  have hsum : ∑ x : Idx3 n m, cup3Term X n m hn hm u v σ x = 0 := by
    refine Finset.sum_involution (s := Finset.univ)
      (f := cup3Term X n m hn hm u v σ) (g := fun x _ => cup3Swap n m hn hm x) ?_ ?_ ?_ ?_
    · intro x _
      rw [cup3Term_swap X n m hn hm u v σ x]
      exact CharTwo.add_self_eq_zero _
    · intro x _ _
      exact cup3SwapNe n m hn hm x
    · intro x _
      exact Finset.mem_univ (cup3Swap n m hn hm x)
    · intro x _
      exact cup3SwapInvol n m hn hm x
  have hdecomp : ∑ x : Idx3 n m, cup3Term X n m hn hm u v σ x
      = (∑ i : L3Idx n m, cup3Term X n m hn hm u v σ (Sum.inl i))
        + ((∑ i : T3Idx n m, cup3Term X n m hn hm u v σ (idxC3 i))
          + ((∑ i : T4Idx n m, cup3Term X n m hn hm u v σ (idxC4 i))
            + ((∑ i : T1Idx n m, cup3Term X n m hn hm u v σ (idxT1 i))
              + (∑ i : T2Idx n m, cup3Term X n m hn hm u v σ (idxT2 i))))) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [idxC3, idxC4, idxT1, idxT2]
  have hzero : (∑ i : L3Idx n m, cup3Term X n m hn hm u v σ (Sum.inl i))
      + ((∑ i : T3Idx n m, cup3Term X n m hn hm u v σ (idxC3 i))
        + ((∑ i : T4Idx n m, cup3Term X n m hn hm u v σ (idxC4 i))
          + ((∑ i : T1Idx n m, cup3Term X n m hn hm u v σ (idxT1 i))
            + (∑ i : T2Idx n m, cup3Term X n m hn hm u v σ (idxT2 i))))) = 0 := by
    rw [← hdecomp]
    exact hsum
  have h7 : (∑ i : L3Idx n m, cup3Term X n m hn hm u v σ (Sum.inl i))
      = ((∑ i : T1Idx n m, cup3Term X n m hn hm u v σ (idxT1 i))
          + (∑ i : T2Idx n m, cup3Term X n m hn hm u v σ (idxT2 i)))
        + (∑ i : T3Idx n m, cup3Term X n m hn hm u v σ (idxC3 i))
        + (∑ i : T4Idx n m, cup3Term X n m hn hm u v σ (idxC4 i)) := by
    have h8 : (∑ i : L3Idx n m, cup3Term X n m hn hm u v σ (Sum.inl i))
        = -((∑ i : T3Idx n m, cup3Term X n m hn hm u v σ (idxC3 i))
          + ((∑ i : T4Idx n m, cup3Term X n m hn hm u v σ (idxC4 i))
            + ((∑ i : T1Idx n m, cup3Term X n m hn hm u v σ (idxT1 i))
              + (∑ i : T2Idx n m, cup3Term X n m hn hm u v σ (idxT2 i))))) := by
      rw [eq_neg_iff_add_eq_zero]
      exact hzero
    rw [CharTwo.neg_eq] at h8
    rw [h8]
    abel
  rw [h7]

theorem cup3Coboundary : Work.Pi6.SQM.Cup3Cob := by
  intro X n m u v hn hm
  exact cup3Cob_aux X n m hn hm u v (by omega) (by omega) (by omega) (by omega)

end

end Work.Pi6.SQM
