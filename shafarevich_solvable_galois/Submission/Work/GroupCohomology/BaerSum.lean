/-
Copyright (c) 2025. All rights reserved.

# The Baer sum of extensions and addition in `H²`

`baerSum X Y` is the operation on extensions of `Q` by `A` (with prescribed action) that
corresponds to addition in `H²(Q, A)` under the classification of
`Submission/Work/GroupCohomology/Classification.lean`.

Concretely, an extension is represented by a `2`-cocycle (`exists_cocycle_equiv`), and the Baer
sum is defined by adding the representing cocycles.  The characteristic property is
`baerSum_ofCocycle`: the Baer sum of the extensions attached to `c` and `c'` is the extension
attached to `c + c'`.

(Up to isomorphism this operation is the classical Baer sum: the quotient of the fibre product
`E ×_Q E'` by `{(a, -a) : a ∈ A}`.  That model is not formalized here; what is formalized is the
ensuing operation on isomorphism classes, which is the form in which the classification theorem is
used.)
-/
import Submission.Work.GroupCohomology.Classification
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.GroupCohomology

variable {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]

/-- A representing `2`-cocycle for an extension of `Q` by `A` (chosen using
`exists_cocycle_equiv`). -/
noncomputable def cocycleOf (X : Extension Q A) : Z2 Q A :=
  Classical.choose (exists_cocycle_equiv X)

theorem cocycleOf_equiv (X : Extension Q A) :
    Nonempty (X.Equiv (Extension.ofCocycle Q A (cocycleOf X))) :=
  Classical.choose_spec (exists_cocycle_equiv X)

/-- The class in `H²(Q, A)` of an extension of `Q` by `A`. -/
noncomputable def classOf (X : Extension Q A) : H2 Q A :=
  H2π Q A (cocycleOf X)

theorem classOf_ofCocycle (c : Z2 Q A) :
    classOf (Extension.ofCocycle Q A c) = H2π Q A c :=
  (eq_ofCocycle_of_equiv c (cocycleOf (Extension.ofCocycle Q A c))
    (cocycleOf_equiv (Extension.ofCocycle Q A c))).symm

theorem H2pi_cocycleOf_ofCocycle (c : Z2 Q A) :
    H2π Q A (cocycleOf (Extension.ofCocycle Q A c)) = H2π Q A c :=
  classOf_ofCocycle c

/-- **The Baer sum** of two extensions of `Q` by `A`: the extension whose class is the sum of the
two classes in `H²(Q, A)`. -/
noncomputable def baerSum (X Y : Extension Q A) : Extension Q A :=
  Extension.ofCocycle Q A (cocycleOf X + cocycleOf Y)

theorem classOf_baerSum (X Y : Extension Q A) :
    classOf (baerSum X Y) = classOf X + classOf Y := by
  show classOf (Extension.ofCocycle Q A (cocycleOf X + cocycleOf Y)) = classOf X + classOf Y
  rw [classOf_ofCocycle, map_add]
  rfl

/-- **The Baer sum corresponds to addition of `2`-cocycles.**  The Baer sum of the extensions
attached to `c` and `c'` is isomorphic to the extension attached to `c + c'`. -/
theorem baerSum_ofCocycle (c c' : Z2 Q A) :
    Nonempty (Extension.Equiv (Extension.ofCocycle Q A (c + c'))
      (baerSum (Extension.ofCocycle Q A c) (Extension.ofCocycle Q A c'))) := by
  refine ofCocycle_equiv_of_eq_class (c + c')
    (cocycleOf (Extension.ofCocycle Q A c) + cocycleOf (Extension.ofCocycle Q A c')) ?_
  show H2π Q A (c + c') =
    H2π Q A (cocycleOf (Extension.ofCocycle Q A c) + cocycleOf (Extension.ofCocycle Q A c'))
  rw [map_add, map_add, H2pi_cocycleOf_ofCocycle, H2pi_cocycleOf_ofCocycle]

end Work.GroupCohomology
