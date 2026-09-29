import Mathlib
import Submission.Work.SynFFT.mrgLvDefs

/-!
# `zipCat` never increases the encoded size of a group

`Work.SynFFT.grpValZipCatSize`: for rows `A B` (lists of rows, i.e. lists of lists of values),

  `vsz (grpVal (zipCat A B)) ≤ vsz (grpVal A) + vsz (grpVal B)`.

This is the size bookkeeping behind the merge words of the transpose (`zipCatWord`/`axisMerge`):
merging two adjacent groups elementwise costs no more than the two groups put side by side.

The proof is the direct induction on `A`.  Writing `grpVal g = ofList (g.map ofList)` and
`vsz (ofList xs) = Σ_{x∈xs} vsz x + xs.length + 1` (`vsz_ofList`, from `mrgLvDefs`), the key
elementary input is

  `vsz (ofList (a ++ b)) ≤ vsz (ofList a) + vsz (ofList b)`,

i.e. concatenating two row encodings shares exactly one terminal `nil`.  The `cons`/`cons` step of
`zipCat` then closes by `omega`, the slack `+1` of the inequality absorbing the `+1` of the
recursive structure.  (The two degenerate cases where one of the lists is empty hold trivially
because `grpVal [] = Val.nil` has size `1 ≥ 0`.)
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-- Unfolding of `grpVal` at a `cons`. -/
theorem gzcs_grpVal_cons (r : List Val) (rs : List (List Val)) :
    grpVal (r :: rs) = Val.cons (ofList r) (grpVal rs) := rfl

/-- The size of a `cons` value. -/
theorem gzcs_vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, Nat.add_assoc]

/-- Concatenating two rows costs at most the sum of their sizes: the two encodings share one
terminal `nil`. -/
theorem gzcs_vsz_ofList_append_le (a b : List Val) :
    vsz (ofList (a ++ b)) ≤ vsz (ofList a) + vsz (ofList b) := by
  rw [vsz_ofList, vsz_ofList, vsz_ofList, List.map_append, List.sum_append, List.length_append]
  omega

/-- `zipCat` never increases the encoded size: the `cons`-chain `zipCat A B` is no larger than `A`
and `B` put side by side. -/
theorem grpValZipCatSize (A B : List (List HvdH.Val)) :
    HvdH.vsz (Work.SynFFT.grpVal (Work.SynFFT.zipCat A B)) ≤
      HvdH.vsz (Work.SynFFT.grpVal A) + HvdH.vsz (Work.SynFFT.grpVal B) := by
  induction A generalizing B with
  | nil =>
      rw [zipCat_nil_left]
      have h : 1 ≤ vsz (grpVal ([] : List (List Val))) := by simp [grpVal, vsz, Val.enc]
      omega
  | cons a A' ih =>
      cases B with
      | nil =>
          rw [zipCat_nil_right]
          have h : 1 ≤ vsz (grpVal ([] : List (List Val))) := by simp [grpVal, vsz, Val.enc]
          omega
      | cons b B' =>
          -- the one nontrivial case: `zipCat (a :: A') (b :: B') = (a ++ b) :: zipCat A' B'`
          have hz : zipCat (a :: A') (b :: B') = (a ++ b) :: zipCat A' B' := rfl
          rw [hz]
          have eZ : vsz (grpVal ((a ++ b) :: zipCat A' B'))
              = vsz (ofList (a ++ b)) + vsz (grpVal (zipCat A' B')) + 1 := by
            rw [gzcs_grpVal_cons, gzcs_vsz_cons]
          have eA : vsz (grpVal (a :: A')) = vsz (ofList a) + vsz (grpVal A') + 1 := by
            rw [gzcs_grpVal_cons, gzcs_vsz_cons]
          have eB : vsz (grpVal (b :: B')) = vsz (ofList b) + vsz (grpVal B') + 1 := by
            rw [gzcs_grpVal_cons, gzcs_vsz_cons]
          rw [eZ, eA, eB]
          have h1 := ih B'
          have h2 := gzcs_vsz_ofList_append_le a b
          omega

end Work.SynFFT
