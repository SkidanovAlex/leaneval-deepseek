/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Nielsen transvection witness for the torus relator `x ^ p * y ^ q`

This file fixes the explicit reduced word underlying the witness used in
`Work.OROneRel.transvectionNielsenData`.  For a negative integer `m`, the transvection
`x ↦ x * y ^ m` (fixing `y`) sends the relator `x ^ p * y ^ q` of `F {0,1}` to

  `(x * y ^ m) ^ p * y ^ q`,

and when `0 ≤ m + q` this concatenated word reduces to

  `(x * y ^ m) ^ (p - 1) * x * y ^ (m + q)`,

which is the explicit reduced list `tvWord p q m` below.  The list `tvBlk m` is the reduced word
of the single factor `x * y ^ m`.

Everything here is definitional bookkeeping; the list is designed so that the lemmas
`tvWord_toWord`, `tvWord_isCyclicallyReduced` and `tvWord_wvListAux_length` (stated and proved in
sibling files) give the word-level facts needed for the main theorem.
-/
import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.wgtMMDefs

namespace Work.OROneRel

/-- The reduced word `(0, true) :: (1, false) ^ |m|` of the factor `of 0 * of 1 ^ m` for `m < 0`. -/
def tvBlk (m : ℤ) : List (Fin 2 × Bool) := (0, true) :: List.replicate m.natAbs (1, false)

/-- The reduced word `(of 0 * of 1 ^ m) ^ (p - 1) * of 0 * of 1 ^ (m + q)` of the transvection
image `(of 0 * of 1 ^ m) ^ p * of 1 ^ q`, valid when `1 ≤ p`, `m < 0` and `0 ≤ m + q`. -/
def tvWord (p q : ℕ) (m : ℤ) : List (Fin 2 × Bool) :=
  (List.replicate (p - 1) (tvBlk m)).flatten
    ++ (0, true) :: List.replicate (m + (q : ℤ)).toNat (1, true)

@[simp] theorem tvBlk_length (m : ℤ) : (tvBlk m).length = m.natAbs + 1 := by
  simp [tvBlk]

/-- The length of the reduced word `tvWord p q m`. -/
theorem tvWord_length (p q : ℕ) (m : ℤ) :
    (tvWord p q m).length = (p - 1) * (m.natAbs + 1) + 1 + (m + (q : ℤ)).toNat := by
  simp only [tvWord, List.length_append, List.length_cons, List.length_replicate,
    List.length_flatten, List.map_replicate, List.sum_replicate, nsmul_eq_mul, tvBlk_length,
    Nat.cast_id]
  ring

end Work.OROneRel
