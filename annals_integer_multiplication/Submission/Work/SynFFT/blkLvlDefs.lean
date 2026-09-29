import Mathlib
import Submission.Work.SynFFT.kit2

/-!
# `Work.SynFFT.blkLvlDefs`: small helpers for the block level pass (`HasBlkLvl`)

The block level pass bundles, for each butterfly pair, its two outputs into a single `cons`
value (so that a `zipWith` can consume two halves and produce one list).  These two helpers
read the two components back.
-/

set_option autoImplicit false

namespace Work.SynFFT

open HvdH

/-- First component of a `cons` value (the value itself if it is not a `cons`). -/
def vfst : Val → Val
  | .cons a _ => a
  | _ => .nil

/-- Second component of a `cons` value (the value itself if it is not a `cons`). -/
def vsnd : Val → Val
  | .cons _ b => b
  | _ => .nil

@[simp] lemma vfst_cons (a b : Val) : vfst (.cons a b) = a := rfl
@[simp] lemma vsnd_cons (a b : Val) : vsnd (.cons a b) = b := rfl

end Work.SynFFT
