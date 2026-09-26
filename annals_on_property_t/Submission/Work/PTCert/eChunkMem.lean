import Mathlib
import Submission.Work.PTCert.eAux

namespace Work.PTCert

/-- Every element of `eAll` is a normal code of letters `< 81`, of value `< 10368`.
Recipe: `Work.PTCert.eAll_chunks_eAux : eAll = eC0 ++ … ++ eC7` (already proved in
`Submission.Work.PTCert.eAux`), `Work.PTCert.mem_eAll_iff` for the membership case split, then
`Work.PTCert.eChunkOK_spec` applied to `Submission.PTCert.C.echunk_ok0`, …, `C.echunk_ok7`
(each has type `eChunkOK cmT eM nT repT eCj = true`). -/
theorem eChunkMem : ∀ z ∈ Submission.PTCert.D.eAll,
    z < 10368 ∧ z % 128 < 81 ∧ z / 128 < 81 ∧
      Submission.PTCert.normC Submission.PTCert.D.cmT (z / 128) (z % 128) = z := by
  intro z hz
  rw [mem_eAll_iff] at hz
  rcases hz with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact eChunkOK_spec _ _ _ _ _ Submission.PTCert.C.echunk_ok0 z h0
  · exact eChunkOK_spec _ _ _ _ _ Submission.PTCert.C.echunk_ok1 z h1
  · exact eChunkOK_spec _ _ _ _ _ Submission.PTCert.C.echunk_ok2 z h2
  · exact eChunkOK_spec _ _ _ _ _ Submission.PTCert.C.echunk_ok3 z h3
  · exact eChunkOK_spec _ _ _ _ _ Submission.PTCert.C.echunk_ok4 z h4
  · exact eChunkOK_spec _ _ _ _ _ Submission.PTCert.C.echunk_ok5 z h5
  · exact eChunkOK_spec _ _ _ _ _ Submission.PTCert.C.echunk_ok6 z h6
  · exact eChunkOK_spec _ _ _ _ _ Submission.PTCert.C.echunk_ok7 z h7

end Work.PTCert
