import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.eCohZeroInvSign
import Submission.Work.SSGRoute.ext_one_iso_divisible_cohomology
import Submission.Work.SSGRoute.ArchDictionary.extOneDictNaturalH1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The degree-`0` comparison of `eCoh` with the `unitRep`-`Hom` dictionary, up to sign

Two degree-`0` dictionaries live on the same group `Ext⁰_{unitRep}(ℤ, Hom_ℤ(X,N))`:

* Mathlib's `groupCohomology` bridge `eCoh 0 G A : H⁰(G,A) ≃+ Ext⁰(ℤ,A)` (`A = homRep X N`);
* the canonical dictionary `unitHomExtEquiv X N : Ext⁰_{unitRep}(ℤ, Hom_ℤ(X,N)) ≃+ Ext⁰_G(X,N)`
  (`Submission/Work/SSGRoute/ext_one_iso_divisible_cohomology.lean`), whose inverse is the
  `NatH1.cEq` of the divisible-coefficient dictionary
  (`Submission/Work/SSGRoute/ArchDictionary/extOneDictNaturalH1.lean`).

`Work.SSGRoute.ArchDictionary.eCohZeroInvSign` computes the first one on the invariant
`eZeroToInv G A f` of a coefficient map `f : unitRep G ⟶ A` (it is `± mk₀ f`).  This file
identifies the two: at the invariant of the *canonical* coefficient map
`φ = (unitHomEquiv X N)⁻¹ (addEquiv₀ a)` — the one whose value on `1` is exactly the additive
equivalence `Ext⁰(X,N) ≅ (X ⟶ N)` — the `eCoh 0`-class is `± (unitHomExtEquiv X N).symm a`.

This is the identity that a proof of `Work.SSGRoute.ArchDictionary.eOf_connMap_cocycle` (the lead's
D3, `ARCHP2_PLAN.md` §B/§3) has to insert between `eCoh_delta` at `n = 0` and the computation of
`CokerNat.connMapCov`: `eCoh_delta` produces
`eCoh 1 (δ z) = ± (eCoh 0 z).comp extClass`, while the statement of D3 names the right-hand side
through `NatH1.cEq`, i.e. through `unitHomExtEquiv`.  Neither direction of this comparison existed on
disk (grep for `eCoh 0` next to `unitHomExtEquiv`/`cEq` was empty before this file).

Both signs are unavoidable: they are fixed by the `Classical.choose`s inside `eCoh` and `H0Iso`, and
the only consumers are at `p = 2`, where a global sign is irrelevant.
-/

open CategoryTheory SSGRoute.PTExt

namespace Work.SSGRoute.ArchNat

/-- **The degree-`0` comparison, generic form.**  For the canonical coefficient map
`φ = (unitHomEquiv X N)⁻¹ (addEquiv₀ a) : unitRep G ⟶ homRep X N`, the `eCoh 0`-class of the
invariant `eZeroToInv G (homRep X N) φ` is `±` the dictionary class `(unitHomExtEquiv X N).symm a`. -/
theorem eCoh_zero_invOfExt0_eq_pm {G : Type} [Group G] (X N : Rep.{0} Coeff G)
    (a : CategoryTheory.Abelian.Ext X N 0) :
    eCoh 0 G (Work.SSGRoute.homRep X N)
        ((groupCohomology.H0Iso (Work.SSGRoute.homRep X N)).inv
          (Work.SSGRoute.eZeroToInv G (Work.SSGRoute.homRep X N)
            ((Work.SSGRoute.unitHomEquiv X N).symm (CategoryTheory.Abelian.Ext.addEquiv₀ a))))
      = (Work.SSGRoute.unitHomExtEquiv X N).symm a ∨
      eCoh 0 G (Work.SSGRoute.homRep X N)
        ((groupCohomology.H0Iso (Work.SSGRoute.homRep X N)).inv
          (Work.SSGRoute.eZeroToInv G (Work.SSGRoute.homRep X N)
            ((Work.SSGRoute.unitHomEquiv X N).symm (CategoryTheory.Abelian.Ext.addEquiv₀ a))))
      = -(Work.SSGRoute.unitHomExtEquiv X N).symm a := by
  -- `unitHomExtEquiv_symm_mk₀` computes the dictionary on classes of the form `mk₀ w`.
  have hkey : (Work.SSGRoute.unitHomExtEquiv X N).symm a
      = CategoryTheory.Abelian.Ext.mk₀ ((Work.SSGRoute.unitHomEquiv X N).symm
          (CategoryTheory.Abelian.Ext.addEquiv₀ a)) := by
    rw [← Work.SSGRoute.unitHomExtEquiv_symm_mk₀ X N
      (CategoryTheory.Abelian.Ext.addEquiv₀ a)]
    congr 1
    exact Work.SSGRoute.ext_eq_mk₀_addEquiv₀ a
  have h := Work.SSGRoute.ArchDictionary.eCohZeroInvSign (Work.SSGRoute.homRep X N)
    ((Work.SSGRoute.unitHomEquiv X N).symm (CategoryTheory.Abelian.Ext.addEquiv₀ a))
  rcases h with h | h
  · left
    rw [h, hkey]
  · right
    rw [h, hkey]

/-- **The degree-`0` comparison in the `NatH1` normalisation** (the form in which
`eOf_connMap_cocycle` needs it): the `eCoh 0`-class of the canonical invariant of
`Ext⁰(ℤ, Hom_ℤ((pres M).X₁, N))` is `± NatH1.cEq N M a`. -/
theorem eCoh_zero_invOfExt0_eq_pm_cEq {G : Type} [Group G] (N M : Rep.{0} Coeff G)
    (a : CategoryTheory.Abelian.Ext (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁ N 0) :
    eCoh 0 G (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₃
        ((groupCohomology.H0Iso (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₃).inv
          (Work.SSGRoute.eZeroToInv G (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₃
            ((Work.SSGRoute.unitHomEquiv
                (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁ N).symm
              (CategoryTheory.Abelian.Ext.addEquiv₀ a))))
      = Work.SSGRoute.ArchDictionary.NatH1.cEq N M a ∨
      eCoh 0 G (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₃
        ((groupCohomology.H0Iso (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₃).inv
          (Work.SSGRoute.eZeroToInv G (Work.SSGRoute.ArchDictionary.NatH1.dpres N M).X₃
            ((Work.SSGRoute.unitHomEquiv
                (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁ N).symm
              (CategoryTheory.Abelian.Ext.addEquiv₀ a))))
      = -(Work.SSGRoute.ArchDictionary.NatH1.cEq N M a) := by
  simpa only [Work.SSGRoute.ArchDictionary.NatH1.cEq] using
    eCoh_zero_invOfExt0_eq_pm (Work.SSGRoute.ArchDictionary.NatH1.pres M).X₁ N a

end Work.SSGRoute.ArchNat
