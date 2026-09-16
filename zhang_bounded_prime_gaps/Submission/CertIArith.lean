import Submission.CertIChunk0
import Submission.CertIChunk1
import Submission.CertIChunk2
import Submission.CertIChunk3
import Submission.CertIChunk4
import Submission.CertIChunk5
import Submission.CertIChunk6
import Submission.CertIChunk7
import Submission.CertIChunk8
import Submission.CertIChunk9
import Submission.CertIChunk10
import Submission.CertIChunk11
import Submission.CertIChunk12
import Submission.CertIChunk13
import Submission.CertIChunk14
import Submission.CertIChunk15
import Submission.CertIChunk16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The `I`-arithmetic identity of the certificate

The 17 chunk values `Submission.CertIChunk0 … CertIChunk16` are summed and compared with the
stored pair `certLam * certqI` of `Submission/CertData.lean`.  This gives the `I`-half of the
certificate:

  `IFuncOrth 50 certFun = certK² · (certqI / certDI)`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- `certIvalT` is the sum of its 17 chunks. -/
theorem certIvalT_val : certIvalT = ((((((((((((((((chunkI 0 + chunkI 1) + chunkI 2) + chunkI 3) + chunkI 4) + chunkI 5) + chunkI 6) + chunkI 7) + chunkI 8) + chunkI 9) + chunkI 10) + chunkI 11) + chunkI 12) + chunkI 13) + chunkI 14) + chunkI 15) + chunkI 16) := by
  rw [certIvalT_chunk]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Finset.sum_range_zero, zero_add]

/-- **The `I`-arithmetic identity, evaluated.** -/
theorem certDI_mul_certIvalT : certDI * certIvalT = certLam * certqI := by
  rw [certIvalT_val, chunkVal_0, chunkVal_1, chunkVal_2, chunkVal_3, chunkVal_4, chunkVal_5, chunkVal_6, chunkVal_7, chunkVal_8, chunkVal_9, chunkVal_10, chunkVal_11, chunkVal_12, chunkVal_13, chunkVal_14, chunkVal_15, chunkVal_16]
  decide

/-- **The `I`-arithmetic identity in the form used by the certificate.** -/
theorem certDI_mul_certISum : certDI * certISum = certLam * certqI := by
  rw [certISum_eq_certIvalT]
  exact certDI_mul_certIvalT

/-- **The value of the `I`-form of the certificate.** -/
theorem IFuncOrth_certFun_eq :
    IFuncOrth 50 certFun = (certK : ℝ) * (certK : ℝ) * ((certqI : ℝ) / (certDI : ℝ)) :=
  IFuncOrth_certFun_value certDI_mul_certISum

end Commons.NumberTheory.MaynardSieve
