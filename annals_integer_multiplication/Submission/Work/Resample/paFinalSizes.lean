import Mathlib
import Submission.Work.Resample.paDefs
import Submission.Work.Resample.pbClr
import Submission.Work.ConvR.sizes

/-!
# Size arithmetic for the epilogue budget `PAFinalBr`

`Work.Resample.PAFinalBr` is the bracket of the epilogue of the `Ã` program: it dominates both
the size of the array parked on stack 1 and the total encoding size of the six values that the
drain (`Work.Resample.paKillD`) moves off the auxiliary stacks 2–6.

This file proves that bracket sufficient.  Since `ss` and `ts` have length `D`, the two `drop D`
lists are empty (`vsz = 1`) and `ts.take D = ts`, so the six drained values reduce to
`α`, `p` and `∏ ts`; the first two are bounded by `isz p` (`α ^ 2 < p` gives `α ≤ p`), and
`isz (∏ ts)` is bounded by `vsz (intList ts)` (`isz` of a product is at most the sum of the
`isz`'s, up to the seed constant `3`, while `intList` pays `isz` per element plus `1` each).
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-! ## Elementary size bounds -/

/-- `isz` of the product of a list of naturals is bounded by the encoding size of the list
(`intList`).  Both sides are at least the `isz`-sum, but `intList` pays `1` extra per element,
which absorbs the seed `1` of the product. -/
theorem pa_isz_prod_le_vsz (l : List ℕ) :
    HvdH.isz (((l.prod : ℕ) : ℤ)) ≤ HvdH.vsz (HvdH.intList l) + 2 := by
  induction l with
  | nil =>
    simp [HvdH.isz, HvdH.vsz, HvdH.Val.enc, HvdH.intList, HvdH.ofList, Nat.size_one]
  | cons t ts ih =>
    rw [List.prod_cons, Work.ConvR.vsz_intList_cons]
    have h := Work.ConvR.isz_mul_nat_le t ts.prod
    omega

/-- The encoding size of the empty `intList`. -/
theorem pa_vsz_intList_nil : HvdH.vsz (HvdH.intList ([] : List ℕ)) = 1 := by
  simp [HvdH.intList, HvdH.ofList, HvdH.vsz, HvdH.Val.enc]

/-- `isz` is monotone on natural casts. -/
theorem pa_isz_le_isz_of_le {a b : ℕ} (h : a ≤ b) :
    HvdH.isz ((a : ℤ)) ≤ HvdH.isz ((b : ℤ)) := by
  rw [HvdH.isz, HvdH.isz, Int.natAbs_natCast, Int.natAbs_natCast]
  exact Nat.add_le_add_right (Nat.size_le_size h) 2

/-! ## The budget -/

theorem paFinalSizes (p α : ℕ) (ss ts : List ℕ) (hαp : α ^ 2 < p) (hss : ss.length = HvdH.D)
    (hts : ts.length = HvdH.D) :
    ts.prod * (2 * p + 8) + ts.prod + 2 ≤ Work.Resample.PAFinalBr p ss ts ∧
    HvdH.vsz (HvdH.intList (ss.drop HvdH.D)) + HvdH.vsz (HvdH.intList (ts.drop HvdH.D)) +
      HvdH.vsz (HvdH.Val.int (α : ℤ)) + HvdH.vsz (HvdH.Val.int (p : ℤ)) +
      HvdH.vsz (HvdH.Val.int (((ts.take HvdH.D).prod : ℕ) : ℤ)) + 6 ≤
        8 * Work.Resample.PAFinalBr p ss ts := by
  have hssD : ss.drop HvdH.D = [] := List.drop_eq_nil_of_le (le_of_eq hss)
  have htsD : ts.drop HvdH.D = [] := List.drop_eq_nil_of_le (le_of_eq hts)
  have htake : ts.take HvdH.D = ts := List.take_of_length_le (le_of_eq hts)
  -- `α ^ 2 < p` gives `α ≤ p`, hence `isz α ≤ isz p` (`p` is positive because `α ^ 2 ≥ 0`).
  have hαp' : α ≤ p := by
    rcases Nat.eq_zero_or_pos α with h | h
    · subst h; omega
    · have h2 := Nat.le_self_pow (n := 2) (by decide) α
      omega
  refine ⟨?_, ?_⟩
  · -- the array size is absorbed by the first summand of the bracket
    simp only [Work.Resample.PAFinalBr]
    omega
  · -- the six drained values
    rw [hssD, htsD, htake, pa_vsz_intList_nil]
    rw [Work.ConvR.vsz_int, Work.ConvR.vsz_int, Work.ConvR.vsz_int]
    have hs1 : HvdH.isz (α : ℤ) ≤ HvdH.isz (p : ℤ) := pa_isz_le_isz_of_le hαp'
    have hs2 : HvdH.isz (((ts.prod : ℕ) : ℤ)) ≤ HvdH.vsz (HvdH.intList ts) + 2 :=
      pa_isz_prod_le_vsz ts
    have hv : 1 ≤ HvdH.vsz (HvdH.intList ts) := Work.ConvR.vsz_one_le _
    have hkey : HvdH.isz (α : ℤ) + HvdH.isz (p : ℤ) + HvdH.isz (((ts.prod : ℕ) : ℤ)) + 8
        ≤ 512 * (HvdH.vsz (HvdH.intList ss) + HvdH.vsz (HvdH.intList ts) + HvdH.isz (p : ℤ) + 1) := by
      omega
    have hfin : 512 * (HvdH.vsz (HvdH.intList ss) + HvdH.vsz (HvdH.intList ts) + HvdH.isz (p : ℤ) + 1)
        ≤ 8 * Work.Resample.PAFinalBr p ss ts := by
      simp only [Work.Resample.PAFinalBr, Work.ConvR.vsz_int]
      omega
    omega

end Work.Resample
