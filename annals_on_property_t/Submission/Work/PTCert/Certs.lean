import Submission.Work.RouteB.Final
import Submission.Work.PTCert.conjActFacts
import Submission.Work.PTCert.orbitDecomp
import Submission.Work.PTCert.fourierTransport
import Submission.Work.PTCert.kleinLevel
import Submission.Work.PTCert.codeFacts
import Submission.Work.PTCert.redWCanonical
import Submission.Work.PTCert.modelKeyFaithful
import Submission.Work.PTCert.actCSound
import Submission.Work.PTCert.whtSound
import Submission.Work.PTCert.ldlChainSound
import Submission.Work.PTCert.bitsBridge
import Submission.Work.PTCert.actSetup
import Submission.Work.PTCert.nStructure
import Submission.Work.PTCert.rowFacts
import Submission.Work.PTCert.symFacts
import Submission.Work.PTCert.nLevel
import Submission.Work.PTCert.kleinFacts
import Submission.Work.PTCert.entryFormula
import Submission.Work.PTCert.ldlFacts
import Submission.Work.PTCert.rowTabSound
import Submission.Work.PTCert.orbitKeys
import Submission.Work.PTCert.labelIdentity
import Submission.Work.PTCert.psdAssembly
import Submission.Work.PTCert.finalStep
import Submission.Work.PTCert.targetSumC1
import Submission.Work.PTCert.targetSumC2
import Submission.Work.PTCert.eSem
import Submission.Work.PTCert.tabSem
import Submission.Work.PTCert.nSem
import Submission.Work.PTCert.rowSem
import Submission.Work.PTCert.groupSem
import Submission.Work.PTCert.orbLabSem
import Submission.Work.PTCert.classSem
import Submission.Work.PTCert.kleinSem
import Submission.Work.PTCert.cert1Final
import Submission.Work.PTCert.cert2Final

/-!
# The two certificates of `theorem_1`

`Submission.RouteB.Edge.theorem_1_of_certificates` reduces the challenge statement to the two
sum-of-squares certificates in `ℝ[Aut(F_5)]` below; they are proved by the kernel-checked
certificate pipeline of `Submission/Work/PTCert/` (see `NOTES_LEAD_glue.md`): the data modules
`Data/*`, the kernel checks `Checks/*` (`decide +kernel`), and the glue lemmas composed here.
-/

namespace Submission.PTCert

open Submission.RouteB.Edge

section
open Work.PTCert

private theorem hCF : CodeFacts := codeFacts
private theorem hE : G.ESem := eSem (modelKeyFaithful redWCanonical)
private theorem hT : G.TabSem := tabSem hCF
private theorem hA : G.ActSetup := actSetup hCF conjActFacts actCSound bitsBridge hE hT
private theorem hNst : G.NStructure := nStructure hA bitsBridge hE nSem hT
private theorem hRF : G.RowFacts := rowFacts hCF hA hNst hE nSem hT rowSem groupSem
private theorem hK : ∀ k ≤ 5, G.KleinSem k := kleinSem
private theorem hPA : G.PsdAssembly :=
  psdAssembly (nLevel hA hNst hRF fourierTransport bitsBridge hCF)
    (kleinFacts hCF hA hNst hRF kleinLevel hK hE nSem bitsBridge)
    (entryFormula hCF hA hNst hRF hK hE nSem hT rowSem bitsBridge)
    (ldlFacts ldlChainSound) (symFacts hCF hA hNst hRF hE nSem hT rowSem groupSem) hRF hK
private theorem hRT : G.RowTabSound := rowTabSound whtSound orbLabSem
private theorem hC : G.ClassSem := classSem hCF
private theorem hFS : G.FinalStep :=
  finalStep (orbitKeys orbitDecomp hCF hA hNst hRF hE nSem hT rowSem groupSem hC) (labelIdentity hC) hC

end

/-- `∃ Λ > 0, Δ₅² − Λ·Δ₅ ∈ Σ²` in `ℝ[Aut(F_5)]` (certified `Λ = 1`). -/
theorem saut5DeltaCert : SAut5DeltaCert :=
  Work.PTCert.cert1Final hPA hRT hFS hC hK Work.PTCert.targetSumC1

/-- `∃ μ > 0, Adj₅ + 2·Op₅ − μ·Δ₅ ∈ Σ²` in `ℝ[Aut(F_5)]` (certified `μ = 1/20`). -/
theorem saut5Adj2OpCert : SAut5Adj2OpCert :=
  Work.PTCert.cert2Final hPA hRT hFS hC hK Work.PTCert.targetSumC2

end Submission.PTCert
