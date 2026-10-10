import Mathlib.Order.CompletePartialOrder
import Mathlib.FieldTheory.Galois.Notation
import Submission.NK.LocalTame.Galois
import Submission.NK.LocalTame.ProP.isProP_iSup_of_normal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalTame

noncomputable section

open NK.LocalTame.ProP

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-- **The wild inertia subgroup of `Gal(K'/κ)` is a pro-`p` group.** -/
theorem wildInertiaSubgroup_isProP (p : ℕ) :
    IsProP p ↥(wildInertiaSubgroup (κ := κ) (K' := K') p) := by
  rw [wildInertiaSubgroup]
  exact isProP_iSup_of_normal (fun N : {N : Subgroup (Gal(K'/κ)) // N.Normal ∧ IsProP p ↥N} =>
    N.1) (fun N => N.2.1) (fun N => N.2.2)

/-- **The wild inertia subgroup is the unique maximal closed normal pro-`p` subgroup** of
`Gal(K'/κ)`: it is normal, pro-`p`, and contains every normal pro-`p` subgroup
(NSW (7.5.7) Corollary). -/
theorem wildInertiaSubgroup_isWildInertia (p : ℕ) :
    IsWildInertia p (Gal(K'/κ)) (wildInertiaSubgroup (κ := κ) (K' := K') p) :=
  isWildInertia_wildInertiaSubgroup p (wildInertiaSubgroup_isProP p)

end

end NK.LocalTame
