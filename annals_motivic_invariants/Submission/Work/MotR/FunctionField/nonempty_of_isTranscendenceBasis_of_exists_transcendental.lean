import Mathlib
import Submission.Work.FFResidual.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotR.FunctionField

theorem nonempty_of_isTranscendenceBasis_of_exists_transcendental {𝔽 K : Type} [Field 𝔽] [Field K]
    [Algebra 𝔽 K] (h : ∃ t : K, Transcendental 𝔽 t) {s : Finset K}
    (hs : IsTranscendenceBasis 𝔽 (Subtype.val : s → K)) : s.Nonempty := by
  have ht : Algebra.Transcendental 𝔽 K := ⟨h⟩
  exact Finset.nonempty_coe_sort.mp (hs.nonempty_iff_transcendental.mpr ht)

end Work.MotR.FunctionField
