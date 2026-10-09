import Mathlib
import Submission.Work.SSGRoute.ZDataMup.NKArtinUmbrella
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A cycle-free copy of the one elementary bridge lemma of `ArtinSymAux`

`Work.SSGRoute.ZDataMup.ArtinSymAux` is a `localFactor_productFormula_abelian`-free file in
content, but its *header* imports `localFactor_productFormula_abelian`, which imports
`Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified`.  Every module that imports
`ArtinSymAux` therefore depends on the (until now unproved) target, and cannot be imported in the
proof of that very target.

The only lemma of `ArtinSymAux` that the ideal-modulus lane (`…/ArtinReciprocity/IdealModulus/`)
uses is the elementary bridge below.  This file re-provides it with a clean import list, so that
the ideal-modulus lane can be re-assembled without the spurious edge.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- `Ideal.ramificationIdxIn p (𝓞 L) = 1` is `NK.HeckeL.IsUnramifiedIn p`. -/
theorem isUnramifiedIn_of_ramificationIdxIn_eq_one_clean (p : HeightOneSpectrum (𝓞 K))
    (h : Ideal.ramificationIdxIn p.asIdeal (𝓞 L) = 1) :
    NK.HeckeL.IsUnramifiedIn (K := K) (L := L) p := by
  letI hMSA : MulSemiringAction (Gal(L/K)) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGG : IsGaloisGroup (Gal(L/K)) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (Gal(L/K)) (𝓞 K) (𝓞 L) K L
  intro q hq
  haveI : q.asIdeal.IsPrime := q.isPrime
  haveI : q.asIdeal.LiesOver p.asIdeal := hq
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := 𝓞 K) (B := 𝓞 L) p.asIdeal q.asIdeal
    (Gal(L/K))]
  exact h

end Work.SSGRoute.ZDataMup
