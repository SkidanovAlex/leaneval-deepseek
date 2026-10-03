import Mathlib
import Submission.Work.ORHughesFree.Tree

namespace Work.ORHughesFree.Tree

/-- `PermRel`-related lists of children have the same length.

The `Iso` part of the mutual induction is irrelevant for this statement, so its motive is `True`;
the only constructor of `PermRel` that mentions it (`cons`) adds one element to each side, and all
the other constructors are visibly length-preserving (or follow from the induction hypotheses). -/
private theorem permRel_nil_right_aux_length {l l' : List MTree} (h : PermRel l l') :
    l.length = l'.length :=
  PermRel.rec (motive_1 := fun _ _ _ => True)
    (motive_2 := fun l l' _ => l.length = l'.length)
    (fun _ _ => trivial)
    rfl
    (fun _ _ _ ih2 => by simp [List.length_cons, ih2])
    (fun x y l => by simp [List.length_cons])
    (fun _ => rfl)
    (fun _ ih => ih.symm)
    (fun _ _ ih1 ih2 => ih1.trans ih2)
    h

/-- A list `PermRel`-equivalent to the empty list is empty: `PermRel` never changes the length of
a list, and the only list of length zero is `[]`. -/
theorem permRel_nil_right {l : List MTree} (h : PermRel l []) : l = [] :=
  List.eq_nil_of_length_eq_zero (permRel_nil_right_aux_length h)

end Work.ORHughesFree.Tree
