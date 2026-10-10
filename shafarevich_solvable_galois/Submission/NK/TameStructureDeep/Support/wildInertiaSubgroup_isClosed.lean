import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Connected.Separation
import Submission.NK.TameStructureDeep.Support.isClosed_of_forall_normal_isProP_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

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
