/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The wild inertia subgroup and the tame quotient of `G_κ`

For `κ` a field, `K'` an algebra over it and `p : ℕ`, this file defines

* `wildInertiaSubgroup p`, the **wild inertia** `V_κ = V_p`: the join of all normal pro-`p`
  subgroups of `Gal(K'/κ)` — for a `p`-adic field `κ` this is the maximal closed normal pro-`p`
  subgroup, equivalently the fixing subgroup of the maximal tame extension of `κ`
  (NSW, *Cohomology of Number Fields*, (7.5.7) Corollary);
* `tameQuotient p = G_κ/V_κ`, the **tame quotient** `G_κ^{tr}`;
* `tameInertiaSubgroup p = V_κ`-`I_κ`, i.e. the inertia subgroup of `NK.LocalAnabelian` viewed
  as a subgroup of the tame quotient: `I_κ/V_κ`.

The only unconditional results here are the ones that need no local field theory: the wild
inertia is normal, it contains every normal pro-`p` subgroup, and it is the unique maximal
closed normal pro-`p` subgroup *provided* it is itself pro-`p` (which is a theorem about joins of
pro-`p` groups, `NK.LocalTame.isProP_iSup_of_normal`).  The arithmetic content — that
`wildInertiaSubgroup p` really is the wild inertia of a `p`-adic field, and everything about
`I_κ/V_κ` — is isolated in the input structures of `NK.LocalTame.TameStructure`.
-/
import Submission.NK.LocalAnabelian.All
import Submission.NK.LocalTame.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open IntermediateField
open NK.LocalAnabelian

namespace NK.LocalTame

universe u

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-- **The wild inertia subgroup** `V_κ` of `Gal(K'/κ)`: the join of all closed normal pro-`p`
subgroups of `Gal(K'/κ)`.

For `κ` a `p`-adic field and `K'` a separable closure this is the wild inertia subgroup: the
maximal closed normal pro-`p` subgroup of `G_κ`, equivalently the fixing subgroup of the maximal
tame extension of `κ` (NSW (7.5.7) Corollary, (7.5.11)). -/
noncomputable def wildInertiaSubgroup (p : ℕ) : Subgroup (Gal(K'/κ)) :=
  ⨆ (N : {N : Subgroup (Gal(K'/κ)) // N.Normal ∧ IsProP p ↥N}), N.1

/-- Every closed normal pro-`p` subgroup is contained in the wild inertia: the wild inertia is
the *largest* such subgroup. -/
theorem le_wildInertiaSubgroup {p : ℕ} {N : Subgroup (Gal(K'/κ))} (hN : N.Normal)
    (h : IsProP p ↥N) : N ≤ wildInertiaSubgroup (κ := κ) (K' := K') p :=
  le_iSup (fun M : {M : Subgroup (Gal(K'/κ)) // M.Normal ∧ IsProP p ↥M} => M.1) ⟨N, hN, h⟩

/-- **The wild inertia subgroup is normal.** -/
theorem wildInertiaSubgroup_normal (p : ℕ) :
    (wildInertiaSubgroup (κ := κ) (K' := K') p).Normal := by
  rw [Subgroup.normal_iff_map_conj_eq]
  intro g
  rw [wildInertiaSubgroup, Subgroup.map_iSup]
  exact iSup_congr fun N => by
    haveI : (N.1).Normal := N.2.1
    exact Subgroup.Normal.map_conj_eq (H := N.1) g

instance wildInertiaSubgroup_normal_inst (p : ℕ) :
    (wildInertiaSubgroup (κ := κ) (K' := K') p).Normal :=
  wildInertiaSubgroup_normal p

/-- **The wild inertia is the unique maximal closed normal pro-`p` subgroup**, once it is known to
be pro-`p`.  The pro-`p`-ness of the join of normal pro-`p` subgroups is
`NK.LocalTame.isProP_iSup_of_normal`. -/
theorem isWildInertia_wildInertiaSubgroup (p : ℕ)
    (hp : IsProP p ↥(wildInertiaSubgroup (κ := κ) (K' := K') p)) :
    IsWildInertia p (Gal(K'/κ)) (wildInertiaSubgroup (κ := κ) (K' := K') p) :=
  ⟨wildInertiaSubgroup_normal p, hp, fun _ hN hNp => le_wildInertiaSubgroup hN hNp⟩

/-- **The tame quotient** `G_κ^{tr} = G_κ/V_κ` of `Gal(K'/κ)`: the quotient by the wild
inertia subgroup. -/
abbrev tameQuotient (p : ℕ) : Type _ :=
  Gal(K'/κ) ⧸ wildInertiaSubgroup (κ := κ) (K' := K') p

/-- **The tame inertia** `I_κ/V_κ` inside the tame quotient: the image of the inertia subgroup
`I_κ = Gal(K'/κ^ur)` in `G_κ^{tr}`. -/
abbrev tameInertiaSubgroup (p : ℕ) : Subgroup (tameQuotient (κ := κ) (K' := K') p) :=
  (inertiaSubgroup (κ := κ) (K' := K') p).map
    (QuotientGroup.mk' (wildInertiaSubgroup (κ := κ) (K' := K') p))

/-- The tame inertia is the image of the inertia subgroup in the quotient, cf.
`NK.LocalTame.quotientImage`. -/
theorem tameInertiaSubgroup_eq_quotientImage (p : ℕ) :
    tameInertiaSubgroup (κ := κ) (K' := K') p =
      quotientImage (wildInertiaSubgroup (κ := κ) (K' := K') p)
        (inertiaSubgroup (κ := κ) (K' := K') p) := rfl

/-- **The abelianised tame quotient** `G_κ^{tr,ab}`: the abelianisation of `G_κ/V_κ`.  Its
torsion subgroup is where the order of the residue field of `κ` is visible (Shimizu,
arXiv:2009.10431, Lemma 2.1; local class field theory). -/
abbrev tameAbelianization (p : ℕ) : Type _ :=
  Abelianization (tameQuotient (κ := κ) (K' := K') p)

/-- The torsion subgroup of the abelianised tame quotient. -/
abbrev tameTorsion (p : ℕ) : Subgroup (tameAbelianization (κ := κ) (K' := K') p) :=
  CommGroup.torsion (tameAbelianization (κ := κ) (K' := K') p)

end

end NK.LocalTame
