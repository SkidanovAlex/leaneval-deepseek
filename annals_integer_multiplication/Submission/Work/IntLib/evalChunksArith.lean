import Mathlib
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.chunkDefs
import Submission.Work.IntLib.range_blk_enc
import Submission.Work.IntLib.stripFalses_map_bit
import Submission.Work.IntLib.chunksAPI
import Submission.Work.IntLib.evChainDefs

/-!
# Arithmetic and encoding facts for `HvdH.evalChunks` / `HvdH.intList`

This file collects the elementary `List`/`Val` facts about `HvdH.evalChunks`,
`HvdH.intList` and `Val.enc` that the `evalPoly`/`chunk` correctness proofs use.

The `evalChunks` recursion/append laws and the split law for the encoding of a
`cons`-chain are proved in the sibling files `chunksAPI.lean` and `evChainDefs.lean`;
what is added here is the *prefix* form

`evalChunks (hs.take (j+1)) b = evalChunks (hs.take j) b + 2^(b*j) * hs[j]`

together with the corresponding `Val.enc` splitting of `intList (hs.drop j)`,
and the `ofBits` concatenation law used by the `evalPoly` invariant.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-! ## Helpers -/

theorem ecArith_nil (b : ℕ) : HvdH.evalChunks ([] : List ℕ) b = 0 := by
  simp [HvdH.evalChunks]

/-- Splitting off the last digit of a prefix of `hs`. -/
theorem ecArith_take_succ (hs : List ℕ) (b j : ℕ) (hj : j < hs.length) :
    HvdH.evalChunks (hs.take (j + 1)) b
      = HvdH.evalChunks (hs.take j) b + 2 ^ (b * j) * hs.getD j 0 := by
  rw [List.take_succ_eq_append_getElem hj, evalChunks_append, evalChunks_singleton,
    List.length_take, Nat.min_eq_left (le_of_lt hj), List.getD_eq_getElem hs 0 hj]

theorem ecArith_getD_drop (l : List ℕ) (j : ℕ) : (l.drop j).getD 0 0 = l.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getD_eq_getElem?_getD]
  simp

theorem ecArith_enc_drop (hs : List ℕ) (j : ℕ) (hj : j < hs.length) :
    HvdH.Val.enc (HvdH.intList (hs.drop j)) =
      HvdH.Glyph.cons :: HvdH.Val.enc (.int (hs.getD j 0 : ℤ)) ++
        HvdH.Val.enc (HvdH.intList (hs.drop (j + 1))) := by
  have hd : hs.drop j = hs.getD j 0 :: hs.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hj, List.getD_eq_getElem hs 0 hj]
  rw [hd]
  exact enc_intList_cons (hs.getD j 0) (hs.drop (j + 1))

theorem ecArith_headD_drop (hs : List ℕ) (j : ℕ) (hj : j < hs.length) :
    (HvdH.Val.enc (HvdH.intList (hs.drop j))).headD HvdH.Glyph.eos = HvdH.Glyph.cons := by
  rw [ecArith_enc_drop hs j hj]
  rfl

theorem ecArith_headD_drop_length (hs : List ℕ) :
    (HvdH.Val.enc (HvdH.intList (hs.drop hs.length))).headD HvdH.Glyph.eos = HvdH.Glyph.nil := by
  rw [List.drop_length, enc_intList_nil]
  rfl

theorem ecArith_ofBits_concat {LO W : List Bool} {V : ℕ}
    (h : Work.IntLib.ofBits LO + 2 ^ LO.length * Work.IntLib.ofBits W = V) :
    Work.IntLib.ofBits (LO ++ W) = V := by
  rw [Work.IntLib.ofBits_append]
  exact h

/-! ## The lemma -/

theorem evalChunksArith :
    (∀ b : ℕ, HvdH.evalChunks ([] : List ℕ) b = 0) ∧
    (∀ (h : ℕ) (hs : List ℕ) (b : ℕ),
      HvdH.evalChunks (h :: hs) b = h + 2 ^ b * HvdH.evalChunks hs b) ∧
    (∀ (hs : List ℕ) (b j : ℕ), j < hs.length →
      HvdH.evalChunks (hs.take (j + 1)) b = HvdH.evalChunks (hs.take j) b + 2 ^ (b * j) * hs.getD j 0) ∧
    (∀ (hs : List ℕ) (j : ℕ), (hs.drop j).getD 0 0 = hs.getD j 0) ∧
    (∀ (hs : List ℕ), hs.take hs.length = hs) ∧
    (∀ (hs : List ℕ) (j : ℕ), j < hs.length →
      HvdH.Val.enc (HvdH.intList (hs.drop j)) =
        HvdH.Glyph.cons :: HvdH.Val.enc (.int (hs.getD j 0 : ℤ)) ++
          HvdH.Val.enc (HvdH.intList (hs.drop (j + 1)))) ∧
    (∀ (hs : List ℕ) (j : ℕ), j < hs.length →
      (HvdH.Val.enc (HvdH.intList (hs.drop j))).headD HvdH.Glyph.eos = HvdH.Glyph.cons) ∧
    (∀ (hs : List ℕ),
      (HvdH.Val.enc (HvdH.intList (hs.drop hs.length))).headD HvdH.Glyph.eos = HvdH.Glyph.nil) ∧
    (∀ (V : ℕ) (LO W : List Bool), Work.IntLib.ofBits LO + 2 ^ LO.length * Work.IntLib.ofBits W = V →
      Work.IntLib.ofBits (LO ++ W) = V) := by
  refine ⟨ecArith_nil, evalChunks_cons, ecArith_take_succ, ecArith_getD_drop, ?_, ecArith_enc_drop,
    ecArith_headD_drop, ecArith_headD_drop_length, ?_⟩
  · intro hs
    exact List.take_length
  · intro V LO W h
    exact ecArith_ofBits_concat h

end Work.IntLib
