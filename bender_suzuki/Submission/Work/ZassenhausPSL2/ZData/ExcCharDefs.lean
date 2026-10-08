import Submission.Blueprint.Interfaces
import Submission.Work.Coherence.Defs
import Submission.Work.CharCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Vocabulary for the exceptional-character (T.I.F.N.) theorem

Re-exports the modules providing the vocabulary of `Work.ZassenhausPSL2.exc_char_coherent`:
`Submission.Blueprint.excludingKernel` (the set `𝒮 = {χ ∈ Irr H | Q₁ ⊄ ker χ}`),
`Submission.Blueprint.indLinear` (`Ind_H^G` as a `ℤ`-linear map on class functions),
`Submission.Blueprint.conj` (conjugation of subgroups) and `Work.Coherence.Coherent`.
-/
