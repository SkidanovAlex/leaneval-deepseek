import Mathlib
import Submission.Work.Kunneth.cp2cp2Span
import Submission.Work.Projective.CP2CP2Ring

/-!
# `ℂP² × ℂP²` as a `Work.Projective.CP2CP2Model`

`Work.Projective.CP2CP2Model X` is the Künneth-ring interface of `ℂP² × ℂP²`: the two classes
`a = π₁^*h`, `b = π₂^*h` in `H²`, the fundamental class `c`, the Pontryagin classes of the tangent
bundle, `span{a², ab, b²} = ⊤`, and the nine intersection numbers of that spanning set.  Its
docstring records that it is *not* inhabited for a concrete `SSet` in this workspace — supplying
that is the job of the KUNNETH subproject.

This module inhabits it, for the simplicial set `Work.Kunneth.cpZ = ℂP² ⊗ ℂP²`: all the fields are
the results of `Submission/Work/Kunneth/cp2cp2Pairing.lean` and
`Submission/Work/Kunneth/cp2cp2Span.lean`.

## Main results

* `Work.Kunneth.cp2cp2Model : Work.Projective.CP2CP2Model cpZ`

The model for the *space* `ℂP² × ℂP²` — the one the consumers `Work.Gen.cp2cp2NumbersOf` /
`Work.Gen.Generators8Of` use — is `Work.Kunneth.cp2cp2ModelCpp` (`cp2cp2ModelCpp.lean`), and the
extra input those consumers ask for alongside the model, the generation of `H₈` by the fundamental
class, is `Work.Kunneth.cppC_generates` (`cp2cp2H8Span.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

open Work.Cohomology

attribute [-instance] AddCommGroup.toIntModule

/-- **`ℂP² × ℂP²` as a Künneth-ring model**: `a = π₁^*h`, `b = π₂^*h`, the fundamental class
`c = [ℂP²] × [ℂP²]`, `p₁ = 3(a² + b²)`, `p₂ = 9·a²b²`, `span{a², ab, b²} = ⊤` and the nine
intersection numbers `⟨a²⌣a²⟩ = ⟨a²⌣ab⟩ = 0`, `⟨a²⌣b²⟩ = 1`, `⟨ab⌣ab⟩ = 1`, and the rest `0`. -/
noncomputable def cp2cp2Model : Work.Projective.CP2CP2Model cpZ where
  a := cpa
  b := cpb
  c := cpFund
  p₁ := (3 : ℤ) • (Work.Projective.kSq cpZ cpa + Work.Projective.kSq cpZ cpb)
  p₂ := (9 : ℤ) • Work.Projective.kTop cpZ
    (Work.Projective.kSq cpZ cpa) (Work.Projective.kSq cpZ cpb)
  p₁_eq := rfl
  p₂_eq := rfl
  span_middle := cp2cp2_span_middle
  int_a2a2 := cpa2_cpa2_pairing
  int_a2b2 := cpa2_cpb2_pairing
  int_b2a2 := cpb2_cpa2_pairing
  int_b2b2 := cpb2_cpb2_pairing
  int_abab := cpab_cpab_pairing
  int_a2ab := cpa2_cpab_pairing
  int_aba2 := cpab_cpa2_pairing
  int_b2ab := cpb2_cpab_pairing
  int_abb2 := cpab_cpb2_pairing

end

end Work.Kunneth
