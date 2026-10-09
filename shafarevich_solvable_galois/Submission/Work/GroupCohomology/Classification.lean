/-
Copyright (c) 2025. All rights reserved.

# Classification of group extensions by `H²`

Let `Q` be a group and `A` an additive commutative group with a `DistribMulAction Q A`.  The
constructions in `Submission/Work/GroupCohomology/Extension.lean` attach to a `2`-cocycle `c` an
extension `E_c` of `Q` by `A` with the prescribed action.  Here we assemble the classification:

* `ofCocycle_equiv_iff` : `E_c ≅ E_{c'}` (as extensions of `Q` by `A`) iff `c` and `c'` have the
  same class in `H²(Q, A)`;
* `exists_cocycle_equiv` (in the module of the same name) : every extension of `Q` by `A` with the
  prescribed action is isomorphic to `E_c` for some `2`-cocycle `c`;
* `ofCocycle_splits_iff` : `E_c` splits iff the class of `c` is `0`;
* `exists_splitting_of_subsingleton_H2` : if `H²(Q, A) = 0`, every extension of `Q` by `A` splits.
-/
import Submission.Work.GroupCohomology.Extension
import Submission.Work.GroupCohomology.eq_ofCocycle_of_equiv
import Submission.Work.GroupCohomology.ofCocycle_equiv_of_eq_class
import Submission.Work.GroupCohomology.exists_cocycle_equiv
import Submission.Work.GroupCohomology.ofCocycle_splits_of_class_zero
import Submission.Work.GroupCohomology.class_zero_of_splits_ofCocycle
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.GroupCohomology

section Classification

variable {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]

/-- **Classification of group extensions by `H²`.**  Two extensions of `Q` by `A` built from
`2`-cocycles `c`, `c'` (with the prescribed action) are isomorphic if and only if `c` and `c'`
define the same class in `H²(Q, A)`. -/
theorem ofCocycle_equiv_iff (c c' : Z2 Q A) :
    Nonempty (Extension.Equiv (Extension.ofCocycle Q A c) (Extension.ofCocycle Q A c')) ↔
      H2π Q A c = H2π Q A c' :=
  ⟨eq_ofCocycle_of_equiv c c', ofCocycle_equiv_of_eq_class c c'⟩

/-- **Splitting criterion.**  The extension `E_c` attached to a `2`-cocycle `c` splits if and only
if the class of `c` in `H²(Q, A)` vanishes. -/
theorem ofCocycle_splits_iff (c : Z2 Q A) :
    Nonempty (Extension.Splitting (Extension.ofCocycle Q A c)) ↔ H2π Q A c = 0 :=
  ⟨class_zero_of_splits_ofCocycle c, ofCocycle_splits_of_class_zero c⟩

/-- Splitting is invariant under isomorphism of extensions. -/
theorem nonempty_splitting_of_equiv {X Y : Extension Q A} (e : Extension.Equiv X Y)
    (h : Nonempty (Extension.Splitting Y)) : Nonempty (Extension.Splitting X) := by
  letI := X.groupE
  letI := Y.groupE
  obtain ⟨s⟩ := h
  refine ⟨{ toFun := fun q => e.toMulEquiv.symm (s q)
            map_one' := by
              show e.toMulEquiv.symm (s 1) = 1
              rw [map_one, map_one]
            map_mul' := by
              intro x y
              show e.toMulEquiv.symm (s (x * y)) =
                e.toMulEquiv.symm (s x) * e.toMulEquiv.symm (s y)
              rw [map_mul, map_mul]
            rightInverse_rightHom := by
              intro q
              show X.ext.rightHom (e.toMulEquiv.symm (s q)) = q
              have h1 := congrFun e.rightHom_comm (e.toMulEquiv.symm (s q))
              simp only [Function.comp_apply] at h1
              rw [MulEquiv.apply_symm_apply] at h1
              rw [← h1]
              exact s.rightInverse_rightHom q }⟩

/-- If `H²(Q, A) = 0`, then every extension of `Q` by `A` (with the prescribed action) splits. -/
theorem exists_splitting_of_subsingleton_H2 [Subsingleton (H2 Q A)] (X : Extension Q A) :
    Nonempty (Extension.Splitting X) := by
  obtain ⟨c, ⟨e⟩⟩ := exists_cocycle_equiv X
  exact nonempty_splitting_of_equiv e
    (ofCocycle_splits_of_class_zero c (Subsingleton.elim _ _))

end Classification

end Work.GroupCohomology
