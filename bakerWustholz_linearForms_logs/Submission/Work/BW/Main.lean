import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.bw_independent
import Submission.Work.BW.logindep_reduction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Baker–Wüstholz for every length `n`, by strong induction on `n`: the ℚ-independent case is
`bw_independent` (BW §§7–21), the dependent case is `logindep_reduction` (BW §6). -/
theorem bw_holds {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) :
    ∀ (n : ℕ) (α : Fin n → K), (∀ i, α i ≠ 0) → BWHolds φ α := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro α hα
    by_cases h : LinearIndependent ℚ (fun i => Complex.log (φ (α i)))
    · exact bw_independent φ α hα h (fun m hm β hβ => IH m hm β hβ)
    · exact logindep_reduction φ α hα h (fun m hm β hβ => IH m hm β hβ)

end Work.BW
