import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.Work.FIPiChain.Unconditional

namespace Submission

theorem friedlander_iwaniec : {p : ℕ | p.Prime ∧ ∃ a b, p = a ^ 2 + b ^ 4}.Infinite :=
  Work.FIPiChain.friedlander_iwaniec_unconditional

end Submission
