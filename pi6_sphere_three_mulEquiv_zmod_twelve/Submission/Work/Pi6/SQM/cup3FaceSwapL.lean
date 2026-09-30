import Mathlib
import Submission.Work.Pi6.SQM.Cup3CobSetup
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `faceU`/`faceV` are invariant under the `L3`-branch `swapL` of the `∪₃` pairing

`swapL` (defined in `Cup3CobSetup.lean`) is the `L3`-branch of the fixed-point-free pairing
involution `cup3Swap` of the master index set of the mod-2 `∪₃` coboundary formula.  It sends
an `L3`-index `p = (k,a,b,c)` (deleted vertex `k`, `∪₃`-configuration `(a,b,c)`) into the `T3`
or `T4` family according to which of the five *regimes* of `k` (relative to the cut points of
the `∪₃`-configuration) holds:

* `k ≤ a`                 → `T3 (a+1, b, c)`, deleted vertex `k`;
* `a+1 ≤ k ≤ a+b+1`       → `T4 (a, b+1, c)`, deleted vertex `k-a`;
* `a+b+2 ≤ k ≤ a+b+c+2`   → `T3 (a, b, c+1)`, deleted vertex `k-b`;
* `a+b+c+3 ≤ k ≤ a+c+m`   → `T4 (a, b, c+1)`, deleted vertex `k-a-c`;
* `k ≥ a+c+m+1`           → `T3 (a, b, c)`, deleted vertex `k-m+3`.

The `u`- and `v`-faces attached to the two indices agree on the nose; this is exactly the
content of the five *LHS-reindexing* identities `reg1u/v … reg5u/v` of
`Submission/Work/Pi6/SQM/Cup3Identities.lean`, which compare the interval maps
`cup3U n m a (b+1) (c+1) ≫ δ_k ≫ shL` and `cup3V n m a (b+1) (c+1) ≫ δ_k ≫ shL`
with `δ_{j} ≫ … ≫ sh3` (classes `T3`) or `… ≫ sh4` (classes `T4`).

The only point that is not pure rewriting is the arithmetic of the two "truncated" branches
(regimes 3 and 4), where the deleted vertex of the image is a *difference* `k-b` resp.
`k-a-c`; the natural-number identity relating that difference to the parametrised form in the
`reg*` statements is discharged by `omega` and then used as a simplification rule (a plain
`rw` cannot be used there, because the value also occurs in the well-formedness proof attached
to the `T3`/`T4` index).
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

theorem cup3FaceSwapL (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (p : Work.Pi6.SQM.L3Idx n m) :
    Work.Pi6.SQM.faceU n m hn hm (Work.Pi6.SQM.swapL n m hn hm p) = Work.Pi6.SQM.faceU n m hn hm (Sum.inl p) ∧
    Work.Pi6.SQM.faceV n m hn hm (Work.Pi6.SQM.swapL n m hn hm p) = Work.Pi6.SQM.faceV n m hn hm (Sum.inl p) := by
  have ha := (L3a p).isLt
  have hb := (L3b p).isLt
  have hc := (L3c p).isLt
  have hk := (L3k p).isLt
  have hp := L3h p
  constructor
  · -- the `u`-face
    rw [swapL]
    split_ifs with h1 h2 h3 h4
    · exact (@reg1u n m n m (L3a p).val ((L3b p).val + 1) ((L3c p).val + 1) (L3k p).val hn hm
        (by omega) (by omega) (by omega) (by omega) (by omega)).symm
    · exact (@reg2u n m n m (L3a p).val ((L3b p).val + 1) ((L3c p).val + 1) (L3k p).val hn hm
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm
    · have hidx : (L3k p).val - (L3b p).val = (L3k p).val - ((L3b p).val + 1) + 1 := by omega
      simp only [hidx]
      exact (@reg3u n m n m (L3a p).val ((L3b p).val + 1) ((L3c p).val + 1) (L3k p).val hn hm
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm
    · exact (@reg4u n m n m (L3a p).val ((L3b p).val + 1) ((L3c p).val + 1) (L3k p).val hn hm
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm
    · exact (@reg5u n m n m (L3a p).val ((L3b p).val + 1) ((L3c p).val + 1) (L3k p).val hn hm
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hk (by omega)).symm
  · -- the `v`-face
    rw [swapL]
    split_ifs with h1 h2 h3 h4
    · exact (@reg1v n m n m (L3a p).val ((L3b p).val + 1) ((L3c p).val + 1) (L3k p).val hn hm
        (by omega) (by omega) (by omega) (by omega) (by omega)).symm
    · exact (@reg2v n m n m (L3a p).val ((L3b p).val + 1) ((L3c p).val + 1) (L3k p).val hn hm
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm
    · exact (@reg3v n m n m (L3a p).val ((L3b p).val + 1) ((L3c p).val + 1) (L3k p).val hn hm
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm
    · have hidx : (L3k p).val - (L3a p).val - (L3c p).val
          = (L3k p).val - (L3a p).val - ((L3c p).val + 1) + 1 := by omega
      simp only [hidx]
      exact (@reg4v n m n m (L3a p).val ((L3b p).val + 1) ((L3c p).val + 1) (L3k p).val hn hm
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).symm
    · exact (@reg5v n m n m (L3a p).val ((L3b p).val + 1) ((L3c p).val + 1) (L3k p).val hn hm
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hk).symm

end

end Work.Pi6.SQM
