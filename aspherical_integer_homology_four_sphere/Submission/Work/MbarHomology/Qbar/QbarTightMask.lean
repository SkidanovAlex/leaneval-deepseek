import Mathlib
import Submission.Work.MbarHomology.Qbar.QbarTightCheap
import Submission.Work.MbarHomology.Qbar.QbarCxEnum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

/-!
# Bitmask form of the face order of `Q̄`

`qLeC e i` (`qTightC e ⊆ qTightC i`) is a `Finset` inclusion; deciding it in the kernel walks
`Multiset` quotients.  Here the tight set of a face is also read as a 48-bit mask
(`qMaskOf`), and inclusion becomes one `Nat.land` comparison (`qLeB`), which the kernel
evaluates with GMP.  `qLeB_iff` ties the two; `dimListLe_eq_mask` rewrites the enumeration
`dimListLe` into the mask form, so the per-cell `decide`s of `Qbar/CxData` stay cheap in the
kernel (and in external checkers).
-/

namespace Work.MbarHomology

/-- The mask bit of one packed digit (`0` for the absent marker `63`). -/
def qMaskDigit (p i : ℕ) : ℕ :=
  bif ((p >>> (6 * i)) &&& 63) == 63 then 0 else 2 ^ (((p >>> (6 * i)) &&& 63) % 48)

/-- The 48-bit mask of a packed quadruple of digits. -/
def qMaskOf (p : ℕ) : ℕ :=
  (qMaskDigit p 0 ||| qMaskDigit p 1) ||| (qMaskDigit p 2 ||| qMaskDigit p 3)

/-- The mask of the tight set of the face `x`. -/
def qMask (x : Fin 865) : ℕ := qMaskOf (qTightPack x)

/-- **The face order as a mask comparison.** -/
def qLeB (e i : Fin 865) : Bool := (qMask e &&& qMask i) == qMask e

theorem mem_qTightDigit_iff (p i : ℕ) (j : Fin 48) :
    j ∈ qTightDigit p i ↔ (qMaskDigit p i).testBit j.val = true := by
  unfold qTightDigit qMaskDigit
  cases h : (((p >>> (6 * i)) &&& 63) == 63)
  · simp only [Bool.cond_false, Finset.mem_singleton, Nat.testBit_two_pow, decide_eq_true_eq]
    constructor
    · intro hj; rw [hj]
    · intro hj; exact Fin.ext hj.symm
  · simp

theorem testBit_qMaskDigit_lt (p i n : ℕ) (h : (qMaskDigit p i).testBit n = true) : n < 48 := by
  unfold qMaskDigit at h
  cases hc : (((p >>> (6 * i)) &&& 63) == 63)
  · rw [hc] at h
    simp only [Bool.cond_false, Nat.testBit_two_pow, decide_eq_true_eq] at h
    rw [← h]; exact Nat.mod_lt _ (by norm_num)
  · rw [hc] at h; simp at h

theorem mem_qTightC_iff (x : Fin 865) (j : Fin 48) :
    j ∈ qTightC x ↔ (qMask x).testBit j.val = true := by
  unfold qTightC qTightDigits qMask qMaskOf
  simp only [Finset.mem_union, mem_qTightDigit_iff, Nat.testBit_lor, Bool.or_eq_true]

theorem testBit_qMask_lt (x : Fin 865) (n : ℕ) (h : (qMask x).testBit n = true) : n < 48 := by
  unfold qMask qMaskOf at h
  simp only [Nat.testBit_lor, Bool.or_eq_true] at h
  rcases h with (h | h) | (h | h) <;> exact testBit_qMaskDigit_lt _ _ _ h

theorem qLeB_iff (e i : Fin 865) : qLeB e i = true ↔ qLeC e i := by
  unfold qLeB qLeC
  rw [beq_iff_eq]
  constructor
  · intro h j hj
    rw [mem_qTightC_iff] at hj ⊢
    have := congrArg (fun m => m.testBit j.val) h
    simp only [Nat.testBit_land, hj, Bool.true_and] at this
    exact this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro n
    rw [Nat.testBit_land]
    cases hn : (qMask e).testBit n
    · rfl
    · have hlt := testBit_qMask_lt e n hn
      have hmem : (⟨n, hlt⟩ : Fin 48) ∈ qTightC e := (mem_qTightC_iff e _).mpr hn
      have := (mem_qTightC_iff i _).mp (h hmem)
      simp only [Bool.true_and]
      exact this

/-- `dimListLe`, with the face order evaluated on masks. -/
theorem dimListLe_eq_mask (e : Fin 865) (k : ℕ) :
    dimListLe e k = (dimList k).filter (fun i => qLeB e i) := by
  unfold dimListLe
  congr 1
  funext i
  by_cases h : qLeC e i
  · rw [decide_eq_true h, (qLeB_iff e i).mpr h]
  · rw [decide_eq_false h]
    cases hb : qLeB e i
    · rfl
    · exact absurd ((qLeB_iff e i).mp hb) h

end Work.MbarHomology
