import Mathlib
import ChallengeDeps
import Submission.Work.DSMap.Map
import Submission.Work.DSMap.Fix
import Submission.Work.DSG1.Basic
import Submission.Work.DSG1.enoughInjectives_sheafOfModules
import Submission.Work.DSG1.comparison

/-!
# DSG1 (area G1): the area theorem

This file assembles the area `G1` of the direct-summand proof map
(`sources/dsmap/direct_summand_proof_map.md`, review §2):

> a splitting for `g ≫ f : X' → X → Spec A` gives one for `f : X → Spec A`.

The ingredients are

* `Work.DSG1.phi_comp` (`Basic.lean`): the `A`-algebra structure of `Γ(X',⊤)` induced by
  `g ≫ f` is the structure induced by `f` followed by the restriction `gammaMap g`,
* `Work.DSG1.comparison` (delegated, `comparison.lean`): the comparison map
  `φ : RΓ(X,𝒪_X) ⟶ RΓ(X',𝒪_{X'})` with `rgUnit A X f ≫ φ = rgUnit A X' (g ≫ f)`,
* `Work.DSG1.transfer` (`Basic.lean`): any such `φ` transfers splittings.

The statement proved here is the frozen `DSMap.Fix.area_G1_pullbackU.{a,b,c}`
(`Submission/Work/DSMap/Fix.lean`, read-only): the universe of the derived category of `X'` is
fixed to `a + 1`.  This is the lead's repair of the original `DSMap.area_G1_pullback`, whose free
universe `d` made the hypothesis `DSplit.{a,b,d}` unusable: using it requires a
`HasDerivedCategory.{d} (SheafOfModules X')` instance, and Mathlib supplies derived-category
instances only at the standard universe `max u v` (see `DESIGN.md` §3 and `Univ.lean`).  At
`d = a + 1`:

* `HasDerivedCategory.{a+1} (SheafOfModules X'.ringCatSheaf)` is `HasDerivedCategory.standard _`,
* `EnoughInjectives (SheafOfModules.{a} X'.ringCatSheaf)` is the Grothendieck-abelian instance
  (`Work.DSG1.enoughInjectives_sheafOfModules`),
* the instance of `ModuleCat A` is the one supplied by the goal `DSplit.{a,b,c} A X f`.

The properness hypotheses of the frozen statement are not used: the comparison map exists for any
`g` (see `comparison.lean`).

Historical note: the earlier versions of this file contained
`Work.DSG1.area_G1_pullback_proved` and a `DSMap.area_G1_pullback_proved` alias, stated with the
two `X'`-side instances as extra hypotheses.  Those are superseded by
`DSMap.Fix.area_G1_pullbackU_proved` (the retired `DSMap.area_G1_pullback` is no longer the
deliverable) and were replaced, not merely renamed.  The conditional form
`Work.DSG1.area_G1_pullback_of_comparison` is kept: it is the useful statement for any caller who
has the comparison map for its own choice of instances.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits

universe a b c

namespace Work.DSG1

/-- `DSplit` transfer along a comparison morphism: the formal content of area `G1`, with the
comparison map supplied for every choice of the instances of `X` (the instances of `X'` being
fixed). -/
theorem area_G1_pullback_of_comparison (A : Type a) [CommRing A] {X X' : Scheme.{a}}
    (f : X ⟶ Spec (.of A)) (g : X' ⟶ X)
    [HasDerivedCategory.{a + 1} (SheafOfModules X'.ringCatSheaf)]
    [EnoughInjectives (SheafOfModules X'.ringCatSheaf)]
    (h : ∀ (_ : HasDerivedCategory.{b} (ModuleCat.{a} A))
      (_ : HasDerivedCategory.{c} (SheafOfModules X.ringCatSheaf))
      (_ : EnoughInjectives (SheafOfModules X.ringCatSheaf)),
      ∃ φ : DSMap.RG A X f ⟶ DSMap.RG A X' (g ≫ f),
        DSMap.rgUnit A X f ≫ φ = DSMap.rgUnit A X' (g ≫ f)) :
    DSMap.DSplit.{a, b, a + 1} A X' (g ≫ f) → DSMap.DSplit.{a, b, c} A X f :=
  dsplit_of_comparison (A := A) f g h

end Work.DSG1

namespace DSMap.Fix

/-- **Area G1.**  A splitting of the challenge unit of `X'` along `g ≫ f` retracts the challenge
unit of `X`. -/
theorem area_G1_pullbackU_proved (A : Type a) [CommRing A] {X X' : Scheme.{a}}
    (f : X ⟶ Spec (.of A)) (g : X' ⟶ X) [IsProper f] [IsProper (g ≫ f)] :
    DSplit.{a, b, a + 1} A X' (g ≫ f) → DSplit.{a, b, c} A X f := by
  intro h' hdc hdx hix
  letI := hdc
  letI := hdx
  letI := hix
  haveI hdx' : HasDerivedCategory.{a + 1} (SheafOfModules X'.ringCatSheaf) :=
    HasDerivedCategory.standard _
  haveI hix' : EnoughInjectives (SheafOfModules X'.ringCatSheaf) :=
    Work.DSG1.enoughInjectives_sheafOfModules X'
  obtain ⟨φ, hφ⟩ := Work.DSG1.comparison (A := A) f g
  exact Work.DSG1.transfer f g φ hφ (h' hdc hdx' hix')

end DSMap.Fix
