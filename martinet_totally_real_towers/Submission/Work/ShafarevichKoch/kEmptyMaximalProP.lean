import Mathlib
import Submission.Work.ShafarevichKoch.SupportedTower
import Submission.Work.ShafarevichKoch.kSupported_universal
import Submission.Work.ShafarevichKoch.kSupported_isPGroup_and_unramified
import Submission.Work.ClassFieldTower.Defs

/-!
# `Work.ShafarevichKoch.kEmptyMaximalProP` -- `F_∅` as the explicit tower `k_∅`

The seed's `Work.ClassFieldTower.exists_maximalUnramifiedProP` produces *some* object
`M : MaximalUnramifiedProP F 2`, whose carrier `M.K` is an opaque type.  This module constructs a
**concrete** such object, namely the explicit supremum `k_∅ = kSupported F 2 ∅ ⊆ AlgebraicClosure F`
of all finite Galois pro-`2` extensions of `F` with trivial relative different
(`SupportedTower.lean`), with all its instances on the nose.

The point is definitional transparency: with `M := kEmptyMaximalProP F`, one has
`M.K = ↥(kSupported F 2 ∅)` and `galoisGroup M = ↥(kSupported F 2 ∅) ≃ₐ[F] ↥(kSupported F 2 ∅)`
*by `rfl`*, and the two `Algebra` instances coincide, so the Krull topology
(`Mathlib.FieldTheory.KrullTopology`) found for `galoisGroup M` is the same one as for
`Gal(k_∅/F)`.  Hence the objects of `SupportedComparison.lean` (the restriction
`Gal(k_S/F) →* Gal(k_∅/F)`, `H_S = Gal(k_S/k_∅)` and `G_S ⧸ H_S ≃* G_∅`) are statements about the
chapter's *own* `G_∅`; in particular `KcProTwoPresentationInput` and `KcKochCohomologyBound` may be
attacked at the concrete object rather than at an abstract `M`.

The three fields of the structure are:

* `universal` -- `kSupported_universal` (every finite Galois pro-`2` `F`-extension with trivial
  relative different embeds into `k_∅`);
* `proP` and `unramified` -- the two conjuncts of `kSupported_isPGroup_and_unramified`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField

noncomputable section

namespace Work.ShafarevichKoch

/-- **A concrete maximal unramified pro-`2` extension of `F`**: the explicit supremal tower
`k_∅ = kSupported F 2 ∅` inside `AlgebraicClosure F`. -/
def kEmptyMaximalProP (F : Type) [Field F] [NumberField F] :
    Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2 where
  K := ↥(kSupported F 2 (∅ : Finset ℕ))
  fieldK := inferInstance
  algebraK := inferInstance
  galoisK := isGalois_kSupported (F := F) (p := 2) (S := (∅ : Finset ℕ))
  universal := fun M _ _ _ _ hpg hdiff => kSupported_universal F M hpg hdiff
  proP := fun L hfd hgal => by
    haveI : FiniteDimensional F L := hfd
    haveI : IsGalois F L := hgal
    haveI : NumberField ↥L := NumberField.of_module_finite F ↥L
    exact (kSupported_isPGroup_and_unramified F L hfd hgal).1
  unramified := fun L _ hfd hgal => (kSupported_isPGroup_and_unramified F L hfd hgal).2

/-- The carrier of `kEmptyMaximalProP F` is the explicit tower `k_∅`, by `rfl`. -/
theorem kEmptyMaximalProP_K (F : Type) [Field F] [NumberField F] :
    (kEmptyMaximalProP F).K = ↥(kSupported F 2 (∅ : Finset ℕ)) := rfl

end Work.ShafarevichKoch
