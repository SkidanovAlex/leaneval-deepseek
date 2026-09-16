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
  exact psiTabTN_row_1 4 (by norm_num)
  exact psiTabTN_row_1 5 (by norm_num)
  exact psiTabTN_row_1 6 (by norm_num)
  exact psiTabTN_row_1 7 (by norm_num)
  exact psiTabTN_row_2 8 (by norm_num)
  exact psiTabTN_row_2 9 (by norm_num)
  exact psiTabTN_row_2 10 (by norm_num)
  exact psiTabTN_row_2 11 (by norm_num)
  exact psiTabTN_row_3 12 (by norm_num)
  exact psiTabTN_row_3 13 (by norm_num)
  exact psiTabTN_row_3 14 (by norm_num)
  exact psiTabTN_row_3 15 (by norm_num)
  exact psiTabTN_row_4 16 (by norm_num)
  exact psiTabTN_row_4 17 (by norm_num)
  exact psiTabTN_row_4 18 (by norm_num)
  exact psiTabTN_row_4 19 (by norm_num)
  exact psiTabTN_row_5 20 (by norm_num)
  exact psiTabTN_row_5 21 (by norm_num)
  exact psiTabTN_row_5 22 (by norm_num)
  exact psiTabTN_row_5 23 (by norm_num)
  exact psiTabTN_row_6 24 (by norm_num)
  exact psiTabTN_row_6 25 (by norm_num)
  exact psiTabTN_row_6 26 (by norm_num)
  exact psiTabTN_row_6 27 (by norm_num)
  exact psiTabTN_row_7 28 (by norm_num)
  exact psiTabTN_row_7 29 (by norm_num)
  exact psiTabTN_row_7 30 (by norm_num)
  exact psiTabTN_row_7 31 (by norm_num)
  exact psiTabTN_row_8 32 (by norm_num)
  exact psiTabTN_row_8 33 (by norm_num)
  exact psiTabTN_row_8 34 (by norm_num)
  exact psiTabTN_row_8 35 (by norm_num)
  exact psiTabTN_row_9 36 (by norm_num)
  exact psiTabTN_row_9 37 (by norm_num)
  exact psiTabTN_row_9 38 (by norm_num)
  exact psiTabTN_row_9 39 (by norm_num)
  exact psiTabTN_row_10 40 (by norm_num)
  exact psiTabTN_row_10 41 (by norm_num)
  exact psiTabTN_row_10 42 (by norm_num)
  exact psiTabTN_row_10 43 (by norm_num)
  exact psiTabTN_row_11 44 (by norm_num)
  exact psiTabTN_row_11 45 (by norm_num)
  exact psiTabTN_row_11 46 (by norm_num)
  exact psiTabTN_row_11 47 (by norm_num)
  exact psiTabTN_row_12 48 (by norm_num)
  exact psiTabTN_row_12 49 (by norm_num)
  exact psiTabTN_row_12 50 (by norm_num)

/-- **The `Ψ`-kernel as a lookup in the transposed table.** -/
theorem certJPsiND_eq_nthDl (N L : ℕ) (hN : N ≤ 53) (hL : L ≤ 50) :
    certJPsiND N L = nthD (nthDl psiTabTN L []) N 0 := by
  rw [psiTabTN_row L (by omega), nthD_map_range _ N 54 (by omega)]
  rfl

end Commons.NumberTheory.MaynardSieve
