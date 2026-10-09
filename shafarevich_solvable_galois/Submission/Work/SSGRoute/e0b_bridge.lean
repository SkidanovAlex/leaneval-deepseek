import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.e0b_core_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `Ext`/group-cohomology bridge (`E0b`), bare form

`PTDefs.extH A n = Abelian.Ext (unitRep G) A n = Extⁿ_G(ℤ, A)` is Mathlib's derived-category
`Ext`, while `groupCohomology A n` is the cohomology of the inhomogeneous cochain complex.
Mathlib's `groupCohomologyIso` computes `groupCohomology A n` as the `n`-th homology of
`Hom(P_•, A)` for any projective resolution `P` of the trivial module `ℤ`, and
`Work.SSGRoute.E0bCore.extHAddEquivHomology` (the universe-relaxed copy of
`Work.SSGRoute.projRes_homologyAddEquiv_extMk`) computes that same homology as `Extⁿ_G(ℤ, A)`.
Composing the two gives the bridge

`E n G A : groupCohomology A n ≃+ extH A n`,

with the representative formula `E (class of a cocycle f) = extMk f` recorded in `Psi_spec`.
This file only contains the *bare* isomorphism; its naturality in the coefficients and its
compatibility with connecting maps are the two further nodes (`E_naturality`, `E_delta`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace Work.SSGRoute.Bridge

open SSGRoute.PTExt CategoryTheory

noncomputable section

/-- The bar resolution of the trivial module `Coeff = ℤ` at the group `G`. -/
abbrev barRes (G : Type) [Group G] : ProjectiveResolution (unitRep G : Rep.{0} Coeff G) :=
  Rep.barResolution Coeff G

/-- **First half of the bridge**: `Hⁿ(G, A)` is the `n`-th homology of `Hom(P_•, A)` for the bar
resolution `P` of `ℤ` (Mathlib's `groupCohomologyIso`). -/
noncomputable def theta (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) :
    groupCohomology A n ≃+
      ((barRes G).complex.linearYonedaObj Coeff A).homology n :=
  (groupCohomologyIso A n (barRes G)).toLinearEquiv.toAddEquiv

/-- **Second half of the bridge**: the `n`-th homology of `Hom(P_•, A)` is `Extⁿ_G(ℤ, A)`. -/
noncomputable def Psi (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) :
    ((barRes G).complex.linearYonedaObj Coeff A).homology n ≃+ extH A n :=
  Classical.choose (E0bCore.extHAddEquivHomology (C := Rep.{0} Coeff G) (k := Coeff)
    (X := unitRep G) (Y := A) (barRes G) n)

/-- **The `Ext`/group-cohomology bridge** `Hⁿ(G,A) ≃+ Extⁿ_G(ℤ,A)`. -/
noncomputable def E (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) :
    groupCohomology A n ≃+ extH A n :=
  (theta n G A).trans (Psi n G A)

/-- `E` is the composite of `theta` and `Psi` by definition. -/
lemma E_eq (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G) :
    E n G A = (theta n G A).trans (Psi n G A) := rfl

/-- **The representative formula of the bridge**: on the class of a cocycle `f : P.X n ⟶ A`
(namely `extMk f`), the second half `Psi` is `ProjectiveResolution.extMk`. -/
lemma Psi_spec (n : ℕ) (G : Type) [Group G] (A : Rep.{0} Coeff G)
    (f : (barRes G).complex.X n ⟶ A) (hf : (barRes G).complex.d (n + 1) n ≫ f = 0) :
    Psi n G A (((barRes G).complex.linearYonedaObj Coeff A).homologyπ n
      (((barRes G).complex.linearYonedaObj Coeff A).cyclesMk f (n + 1) (by simp) (by
        change (barRes G).complex.d (n + 1) n ≫ f = 0
        exact hf))) =
    (barRes G).extMk f (n + 1) rfl hf :=
  Classical.choose_spec (E0bCore.extHAddEquivHomology (C := Rep.{0} Coeff G) (k := Coeff)
    (X := unitRep G) (Y := A) (barRes G) n) f hf

/-- **`H¹(G, C) = 0` transfers to `Ext¹_G(ℤ, C) = 0`.** -/
theorem subsingleton_extH_of_subsingleton_groupCohomology (n : ℕ) (G : Type) [Group G]
    (A : Rep.{0} Coeff G) (h : Subsingleton (groupCohomology A n)) :
    Subsingleton (extH A n) :=
  ⟨fun x y => by
    have hx : (E n G A).symm x = (E n G A).symm y := Subsingleton.elim _ _
    simpa using congrArg (E n G A) hx⟩

/-- `Subsingleton` transfer in the other direction. -/
theorem subsingleton_groupCohomology_of_subsingleton_extH (n : ℕ) (G : Type) [Group G]
    (A : Rep.{0} Coeff G) (h : Subsingleton (extH A n)) :
    Subsingleton (groupCohomology A n) :=
  ⟨fun x y => (E n G A).injective (Subsingleton.elim _ _)⟩

end

end Work.SSGRoute.Bridge
