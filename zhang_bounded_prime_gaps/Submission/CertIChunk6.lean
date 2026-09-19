import Submission.CertChunks

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `6`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_6 : chunkI 6 = (5641182676572066665101498499366241771051298529504591039445963786586935691023318490568473397137172469114755053992361472088856217457817975411944829734765566627050878100397097977044665441067423616491419898668306344184808733146265306143890965769277934910742462464000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
