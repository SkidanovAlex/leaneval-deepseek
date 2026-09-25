/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The wild inertia subgroup is closed

`V_κ = NK.LocalTame.wildInertiaSubgroup p` is *defined* as the join of the normal pro-`p`
subgroups of `G_κ = Gal(K'/κ)`.  It is pro-`p` by
`NK.LocalTame.wildInertiaSubgroup_isProP`, hence the maximal normal pro-`p` subgroup, and it is
the maximal *closed* normal pro-`p` subgroup once it is known to be closed.  This file proves that
closedness — for **every** field `κ` and separable closure `K'`, with no local-field hypothesis.

The argument is in two steps, neither of which uses the false rule "finite index ⟹ open" (which
fails in general profinite groups: `∏_ℕ ℤ/2` has index-`2` normal subgroups containing no open
subgroup, coming from non-continuous functionals):

1. `NK.TameStructureDeep.Support.isProP_of_openNormal_index`: if every **open normal** subgroup
   of a profinite group has `p`-power index, then the group is pro-`p` in the finite-quotient sense
   (`ℓ`-divisibility for `ℓ ≠ p`, via
   `NK.TameStructureDeep.Support.eq_one_of_hom_zmod_of_openNormal_index` and
   `NK.TameStructureDeep.Support.commutative_topologicalClosure_zpowers`);
2. `NK.TameStructureDeep.Support.isClosed_of_forall_normal_isProP_le`: the maximal normal pro-`p`
   subgroup of a profinite group is closed.  Indeed its closure `C` satisfies the hypothesis of
   step 1: for an open normal `U ≤ C` the subset `V_κ·U` is an open (hence closed) subgroup of `C`
   containing the dense `V_κ`, so `V_κ·U = C` and
   `[C : U] = [V_κ : V_κ ∩ U]`, a `p`-power because `V_κ ∩ U` is normal of finite index in the
   pro-`p` group `V_κ`.  Hence `C` is pro-`p` and normal, so `C ≤ V_κ` by maximality of `V_κ`,
   whence `C = V_κ`.
-/
import Submission.NK.TameStructureDeep.Defs
import Submission.NK.TameStructureDeep.Support.isClosed_of_forall_normal_isProP_le

open scoped Classical

namespace NK.TameStructureDeep.Support

noncomputable section

/-- **The wild inertia subgroup is closed.**  For any field `κ` and separable closure `K'`, the
join `V_κ` of the normal pro-`p` subgroups of `Gal(K'/κ)` is a closed subgroup of the profinite
group `Gal(K'/κ)`.

This is the statement that the wild inertia is a Galois group (Hilbert: the wild inertia of a
finite Galois extension of local fields is a `p`-group).  It is *proved* here, not assumed: see
the module docstring for the two-step argument. -/
theorem wildInertiaSubgroup_isClosed {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] (p : ℕ) (hp : p.Prime) :
    IsClosed (NK.LocalTame.wildInertiaSubgroup (κ := κ) (K' := K') p : Set (Gal(K'/κ))) :=
  isClosed_of_forall_normal_isProP_le (G := Gal(K'/κ)) hp
    (NK.LocalTame.wildInertiaSubgroup_isProP (κ := κ) (K' := K') p)
    (fun _ hN hNp => NK.LocalTame.le_wildInertiaSubgroup hN hNp)

end

end NK.TameStructureDeep.Support
