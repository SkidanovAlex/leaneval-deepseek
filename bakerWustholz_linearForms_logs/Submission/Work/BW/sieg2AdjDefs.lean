import Mathlib
import Submission.Work.BW.sieg2KernelDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The place underlying a coordinate of the mixed embedding

The index type of the standard orthonormal basis of the mixed space of a number field `F` is
`NumberField.mixedEmbedding.index F = {w : InfinitePlace F // IsReal w} ⊕ ({w // IsComplex w} × Fin 2)`:
a real place contributes one real coordinate, while a complex place contributes two real
coordinates (real and imaginary part).  `stdPlace` is the map back to the infinite place.

This file is imported by `Submission.Work.BW.sieg2_det_adjoint_le` and by the lemmas delegated
for it.
-/

open NumberField

namespace Work.BW

noncomputable section

/-- The infinite place underlying a coordinate index of the mixed embedding. -/
def stdPlace {F : Type*} [Field F] [NumberField F]
    (s : NumberField.mixedEmbedding.index F) : NumberField.InfinitePlace F :=
  match s with
  | Sum.inl w => w.1
  | Sum.inr z => z.1.1

@[simp]
theorem stdPlace_inl {F : Type*} [Field F] [NumberField F]
    (w : {w : NumberField.InfinitePlace F // w.IsReal}) :
    stdPlace (Sum.inl w) = w.1 := rfl

@[simp]
theorem stdPlace_inr {F : Type*} [Field F] [NumberField F]
    (w : {w : NumberField.InfinitePlace F // w.IsComplex}) (k : Fin 2) :
    stdPlace (Sum.inr (w, k)) = w.1 := rfl

end

end Work.BW
