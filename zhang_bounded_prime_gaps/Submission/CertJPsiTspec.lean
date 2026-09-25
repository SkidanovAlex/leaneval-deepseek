import Submission.CertJPsiTRow0
import Submission.CertJPsiTRow1
import Submission.CertJPsiTRow2
import Submission.CertJPsiTRow3
import Submission.CertJPsiTRow4
import Submission.CertJPsiTRow5
import Submission.CertJPsiTRow6
import Submission.CertJPsiTRow7
import Submission.CertJPsiTRow8
import Submission.CertJPsiTRow9
import Submission.CertJPsiTRow10
import Submission.CertJPsiTRow11
import Submission.CertJPsiTRow12
import Submission.CertJPsiTabT
import Submission.CertJLookup
import Submission.CertJPsiND

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000000

open scoped BigOperators
open Finset

/-!
# The transposed `J`-kernel table: correctness

`psiTabTN` (row `L` = the values `psiTab[51·N+L]`) is checked *directly* against the kernel sum
`certJPsiND N L = ∑_{jj ≤ N} certJPsiTermN N L jj` — this avoids importing the flat table
`psiTab` (two 1.2 MB literals in one module exceed the memory budget).  The `L`-checks are the
13 chunk theorems of `Submission.CertJPsiTRow0 … 12`.
-/

namespace Commons.NumberTheory.MaynardSieve

theorem psiTabTN_length : psiTabTN.length = 51 := by decide

/-- Row `L` of the transposed table. -/
theorem psiTabTN_row (L : ℕ) (hL : L < 51) :
    nthDl psiTabTN L [] =
      (List.range 54).map (fun N => ∑ jj ∈ Finset.range (N + 1), certJPsiTermN N L jj) := by
  interval_cases L
  exact psiTabTN_row_0 0 (by norm_num)
  exact psiTabTN_row_0 1 (by norm_num)
  exact psiTabTN_row_0 2 (by norm_num)
  exact psiTabTN_row_0 3 (by norm_num)
  exact psiTabTN_row_1 0 (by norm_num)
  exact psiTabTN_row_1 1 (by norm_num)
  exact psiTabTN_row_1 2 (by norm_num)
  exact psiTabTN_row_1 3 (by norm_num)
  exact psiTabTN_row_2 0 (by norm_num)
  exact psiTabTN_row_2 1 (by norm_num)
  exact psiTabTN_row_2 2 (by norm_num)
  exact psiTabTN_row_2 3 (by norm_num)
  exact psiTabTN_row_3 0 (by norm_num)
  exact psiTabTN_row_3 1 (by norm_num)
  exact psiTabTN_row_3 2 (by norm_num)
  exact psiTabTN_row_3 3 (by norm_num)
  exact psiTabTN_row_4 0 (by norm_num)
  exact psiTabTN_row_4 1 (by norm_num)
  exact psiTabTN_row_4 2 (by norm_num)
  exact psiTabTN_row_4 3 (by norm_num)
  exact psiTabTN_row_5 0 (by norm_num)
  exact psiTabTN_row_5 1 (by norm_num)
  exact psiTabTN_row_5 2 (by norm_num)
  exact psiTabTN_row_5 3 (by norm_num)
  exact psiTabTN_row_6 0 (by norm_num)
  exact psiTabTN_row_6 1 (by norm_num)
  exact psiTabTN_row_6 2 (by norm_num)
  exact psiTabTN_row_6 3 (by norm_num)
  exact psiTabTN_row_7 0 (by norm_num)
  exact psiTabTN_row_7 1 (by norm_num)
  exact psiTabTN_row_7 2 (by norm_num)
  exact psiTabTN_row_7 3 (by norm_num)
  exact psiTabTN_row_8 0 (by norm_num)
  exact psiTabTN_row_8 1 (by norm_num)
  exact psiTabTN_row_8 2 (by norm_num)
  exact psiTabTN_row_8 3 (by norm_num)
  exact psiTabTN_row_9 0 (by norm_num)
  exact psiTabTN_row_9 1 (by norm_num)
  exact psiTabTN_row_9 2 (by norm_num)
  exact psiTabTN_row_9 3 (by norm_num)
  exact psiTabTN_row_10 0 (by norm_num)
  exact psiTabTN_row_10 1 (by norm_num)
  exact psiTabTN_row_10 2 (by norm_num)
  exact psiTabTN_row_10 3 (by norm_num)
  exact psiTabTN_row_11 0 (by norm_num)
  exact psiTabTN_row_11 1 (by norm_num)
  exact psiTabTN_row_11 2 (by norm_num)
  exact psiTabTN_row_11 3 (by norm_num)
  exact psiTabTN_row_12 0 (by norm_num)
  exact psiTabTN_row_12 1 (by norm_num)
  exact psiTabTN_row_12 2 (by norm_num)

/-- **The `Ψ`-kernel as a lookup in the transposed table.** -/
theorem certJPsiND_eq_nthDl (N L : ℕ) (hN : N ≤ 53) (hL : L ≤ 50) :
    certJPsiND N L = nthD (nthDl psiTabTN L []) N 0 := by
  rw [psiTabTN_row L (by omega), nthD_map_range _ N 54 (by omega)]
  rfl

end Commons.NumberTheory.MaynardSieve
