import Mathlib
import Submission.Work.Sph3Disc.pairDelta_mixedCup_general

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `cocycleOfK` is `ℤ`-linear inside `homologyπ`

`Work.Cohomology.cocycleOfK` takes the cocycle proof as an argument, so one cannot simply `rw`
`r •` through `homologyπ ∘ cocycleOfK`; this module provides that step.  It is the piece needed at
the end of `Work.Whitney.cutoff_class_formula` (see `rankOne_cup_model_NOTES.md` sections 12 and
14), where the slide produces `starAB … = (-1)^m • ⟨d (cup …), _⟩` and the `(-1)^m` has to be
carried through `homologyπ ∘ cocycleOfK`.

Proof: `iCycles` is injective (`iCycles_injective_K`) and `iCycles (cocycleOfK K α h) = α`
(`iCycles_cocycleOfK`), so the two `cocycleOfK`s agree after applying `r •`; then `homologyπ` is
additive (a `ModuleCat ℤ` morphism) and `map_zsmul` finishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.Cohomology

open CategoryTheory CategoryTheory.Limits

/-- **`cocycleOfK` is `ℤ`-linear inside `homologyπ`**: scaling the cochain scales the class, even
though the cocycle proof argument changes. -/
theorem homologyPi_cocycleOfK_smul (K : CochainComplex (ModuleCat ℤ) ℕ) {n : ℕ}
    (c : ↑(K.X n)) (hc : (ModuleCat.Hom.hom (K.d n (n + 1))) c = 0) (r : ℤ)
    (h : (ModuleCat.Hom.hom (K.d n (n + 1))) (r • c) = 0) :
    (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n))
        (cocycleOfK K (r • c) h)
      = r • (ModuleCat.Hom.hom (HomologicalComplex.homologyπ K n))
          (cocycleOfK K c hc) := by
  have hcyc : cocycleOfK K (r • c) h = r • cocycleOfK K c hc := by
    apply iCycles_injective_K K n
    rw [map_zsmul, iCycles_cocycleOfK, iCycles_cocycleOfK]
  rw [hcyc, map_zsmul]

end Work.Cohomology
