import Submission.ZagierHoffmanProof.StepL21

set_option autoImplicit false
set_option maxHeartbeats 100000000
open Polynomial RatFunc
open scoped BigOperators

/-!
# Step L22: the pre-prefix leading tuple at the Prop-2.12 configuration

`bstarLeadingTuple r s k j …` is the (2.13)-leading tuple after the B*_{s_j} step:
`s_j` prepended to the `(k−j−1)`-`q`-prepend of Lemma 2.9's merged head
`(s_k, …, s_r)` (built from `w1 := s_k − q` and the `sTail`).  `bstarLeadingTuple_head`
records that its first entry is `s_j`.  The full value lemma (every position equals
the corresponding tail slice of `s`, using the middle-entries-are-`q` hypothesis
`hmid` and `w1Of_add_pnat`) is the next piece; it is a value-level case analysis
through `value_qsTuple`/`value_consVec`/`sTail` with the depth arithmetic
`(r−k+1)+(k−j−1)+1 = r−j+1`.
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The pre-prefix leading tuple of the (2.13) output at the Prop-2.12 configuration:
`s_j` prepended to the `(k−j−1)`-`q`-prepend of the Lemma-2.9 merged head
`(s_k, …, s_r)` (where `w1 := s_k − q`). -/
noncomputable def bstarLeadingTuple (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) :
    Fin ((r - k + 1) + (k - j - 1) + 1) → ℕ+ :=
  consVec (s ⟨j - 1, by omega⟩)
    (qsTuple F (k - j - 1) (r - k + 1)
      (consVec ⟨(qExp F : ℕ) + (w1Of F r s k hk1 hkr hbig : ℕ),
        Nat.add_pos_left (PNat.pos (qExp F)) (w1Of F r s k hk1 hkr hbig : ℕ)⟩
        (sTail r s k hkr)))

/-- The head of the pre-prefix leading tuple is `s_j`. -/
lemma bstarLeadingTuple_head (r : ℕ) (s : Fin r → ℕ+) (k j : ℕ)
    (hk1 : 1 ≤ k) (hkr : k ≤ r) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (hbig : (Nat.card F : ℕ) < (s ⟨k - 1, by omega⟩ : ℕ)) :
    (bstarLeadingTuple F r s k j hk1 hkr hj1 hjk hbig)
      ⟨0, (by omega : 0 < (r - k + 1) + (k - j - 1) + 1)⟩ = s ⟨j - 1, by omega⟩ := by
  change (consVec (s ⟨j - 1, by omega⟩)
      (qsTuple F (k - j - 1) (r - k + 1)
        (consVec ⟨(qExp F : ℕ) + (w1Of F r s k hk1 hkr hbig : ℕ),
          Nat.add_pos_left (PNat.pos (qExp F)) (w1Of F r s k hk1 hkr hbig : ℕ)⟩
          (sTail r s k hkr)))) ⟨0, (by omega : 0 < (r - k + 1) + (k - j - 1) + 1)⟩ =
    s ⟨j - 1, by omega⟩
  exact consVec_zero (s ⟨j - 1, by omega⟩) (qsTuple F (k - j - 1) (r - k + 1)
    (consVec ⟨(qExp F : ℕ) + (w1Of F r s k hk1 hkr hbig : ℕ),
      Nat.add_pos_left (PNat.pos (qExp F)) (w1Of F r s k hk1 hkr hbig : ℕ)⟩
      (sTail r s k hkr)))

end ZagierHoffmanPositiveChar
