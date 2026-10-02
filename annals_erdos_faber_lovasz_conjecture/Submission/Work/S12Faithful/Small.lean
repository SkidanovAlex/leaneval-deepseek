import Submission.Work.S12Faithful.Data
import Submission.Work.S12Faithful.exists_S12A2Data

/-!
# From the smallness bundle to the numeric data

A one-line wrapper: `Work.S12Faithful.exists_S12A2Data` takes the constant-level smallness
relations individually, `Work.S12Faithful.S12A2Small` bundles them, and
`Work.S12Faithful.exists_S12A2Small` produces the bundle.  This module makes the two compose.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.S12Faithful

open ErdosFaberLovaszConjecture

/-- **`S12A2Data` from the smallness bundle.** -/
theorem exists_S12A2Data_of_small (hK : KahnStatement) {β γ ρ ε ζ η ηr : ℝ} {r₁ r₀ : ℕ}
    (hs : S12A2Small β γ ρ ε ζ η ηr r₁ r₀) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ, ∀ n ≥ N, S12A2Data n r₁ r₀ β γ ρ ξ ε ζ η ηr :=
  exists_S12A2Data hK hs.hβ0 hs.hγ0 hs.hρ0 hs.hε0 hs.hζ0 hs.hη0 hs.hηr0
    hs.hr₁2 hs.hr₀2 hs.hr₁r₀ hs.hρ4 hs.hρ100 hs.hγ1 hs.hβγ hs.hβsq hs.hβ4 hs.hγρs
    hs.hγ2ε hs.hε1000 hs.hε4000 hs.h8γε hs.hγρabs hs.hβr1 hs.hr₁β₀ hs.hr₀big hs.hL5in
    hs.hsmall hs.hη22 hs.h15γρε hs.h15γε hs.h20ερ hs.h30 hs.h8r₀ hs.h20ε hs.h15ερ
    hs.hηrbig hs.hsqrtε hs.hnumα0 hs.hnum1 hs.hnum2 hs.hcardc

end Work.S12Faithful
