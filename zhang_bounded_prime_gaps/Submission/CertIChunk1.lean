import Submission.CertChunks
import Submission.CertIChunk0

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators

/-! The value of the `1`-th chunk of the table-based `I`-evaluation, by one `decide`. -/

namespace Commons.NumberTheory.MaynardSieve

theorem chunkVal_1 : chunkI 1 = (17186033213738821825221451634271187222796232467694611456573481323017877488656089517291981098688550827461923557879206271347537840825691896437993674076646715763501269993057140588253275844016295616520498459979205141349262686902565959406161665740973715054573649920000 : ℤ) := by
  decide

end Commons.NumberTheory.MaynardSieve
