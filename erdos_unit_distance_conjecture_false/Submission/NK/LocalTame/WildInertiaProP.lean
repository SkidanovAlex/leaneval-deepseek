/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The wild inertia subgroup is pro-`p`

`wildInertiaSubgroup p` is by definition the join of all normal pro-`p` subgroups of
`Gal(K'/κ)`.  This file records that the join is again pro-`p`
(`NK.LocalTame.ProP.isProP_iSup_of_normal`), so that `wildInertiaSubgroup p` really is the
*maximal* closed normal pro-`p` subgroup (`NK.LocalTame.isWildInertia_wildInertiaSubgroup`)
— with no arithmetic input required.  What remains as an arithmetic input about the wild inertia
is only that it is contained in the inertia subgroup (`NK.LocalTame.TameStructureInput`).
-/
import Submission.NK.LocalTame.Basic
import Submission.NK.LocalTame.Galois
import Submission.NK.LocalTame.ProP.isProP_iSup_of_normal

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
