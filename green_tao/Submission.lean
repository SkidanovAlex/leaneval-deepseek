import ChallengeDeps
import Submission.Helpers
import Submission.Work.GYFinal2

open LeanEval.NumberTheory

namespace Submission

theorem green_tao : ContainsArbitraryAPs {p : ℕ | Nat.Prime p} :=
  GYMaj.green_tao_of_majorant (εw := 1 / 8) (by norm_num) (by norm_num) GYMaj.majorant_hP

end Submission
