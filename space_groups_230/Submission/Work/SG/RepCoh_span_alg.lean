import Mathlib
import Submission.Work.SG.SGRepDefs
import Submission.Work.SG.RedBlDefs

/-!
# The `ℤ`-span of the echelon rows is closed under the algebraic operations

`RC.InSpan rows N v` says that the coordinates of `v` below `N` are the coordinates of an
integral linear combination of the rows.  Because the property only inspects the coordinates
below `N`, it is a congruence on the zero-padded values and is closed under addition,
subtraction and scalar multiplication; the coefficient arithmetic is
`RB.addC`/`RB.subC`/`RB.smulC` with the linearity lemmas `RB.linC_addC`,
`RB.linC_subC`, `RB.linC_smulC`.
-/

namespace Work.SG

theorem RepCoh_span_alg :
    (∀ (rows : List (List ℤ)) (N : ℕ) (v : List ℤ),
        (∀ q, q < N → v.getD q 0 = 0) → Work.SG.RC.InSpan rows N v) ∧
    (∀ (rows : List (List ℤ)) (N : ℕ) (u v : List ℤ),
        (∀ q, q < N → u.getD q 0 = v.getD q 0) → Work.SG.RC.InSpan rows N u →
          Work.SG.RC.InSpan rows N v) ∧
    (∀ (rows : List (List ℤ)) (N : ℕ) (u v w : List ℤ),
        Work.SG.RC.InSpan rows N u → Work.SG.RC.InSpan rows N v →
          (∀ q, q < N → w.getD q 0 = u.getD q 0 + v.getD q 0) → Work.SG.RC.InSpan rows N w) ∧
    (∀ (rows : List (List ℤ)) (N : ℕ) (u v w : List ℤ),
        Work.SG.RC.InSpan rows N u → Work.SG.RC.InSpan rows N v →
          (∀ q, q < N → w.getD q 0 = u.getD q 0 - v.getD q 0) → Work.SG.RC.InSpan rows N w) ∧
    (∀ (rows : List (List ℤ)) (N : ℕ) (k : ℤ) (u w : List ℤ),
        Work.SG.RC.InSpan rows N u →
          (∀ q, q < N → w.getD q 0 = k * u.getD q 0) → Work.SG.RC.InSpan rows N w) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the zero vector is in the span (`cs = []`)
    intro rows N v hv
    exact ⟨[], fun q _ => by rw [hv q ‹q < N›, RB.linC_nil_right]⟩
  · -- `InSpan` only sees the coordinates below `N`
    intro rows N u v huv hu
    obtain ⟨cs, hcs⟩ := hu
    exact ⟨cs, fun q hq => by rw [← huv q hq, hcs q hq]⟩
  · -- closed under pointwise sums
    intro rows N u v w hu hv hw
    obtain ⟨csu, hcsu⟩ := hu
    obtain ⟨csv, hcsv⟩ := hv
    refine ⟨RB.addC rows.length csu csv, fun q hq => ?_⟩
    rw [hw q hq, hcsu q hq, hcsv q hq, RB.linC_addC]
  · -- closed under pointwise differences
    intro rows N u v w hu hv hw
    obtain ⟨csu, hcsu⟩ := hu
    obtain ⟨csv, hcsv⟩ := hv
    refine ⟨RB.subC rows.length csu csv, fun q hq => ?_⟩
    rw [hw q hq, hcsu q hq, hcsv q hq, RB.linC_subC]
  · -- closed under scalar multiplication
    intro rows N k u w hu hw
    obtain ⟨cs, hcs⟩ := hu
    refine ⟨RB.smulC rows.length k cs, fun q hq => ?_⟩
    rw [hw q hq, hcs q hq, RB.linC_smulC]

end Work.SG
