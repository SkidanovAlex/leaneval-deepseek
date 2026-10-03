/-
# `Submission.Work.FIChain.Ad_atilc_split_real` — (1.7) for the `λ⁺`-half at real arguments

`Ad ã(ζ)(X) = g̃(ζ)·Ã(⌊X⌋₊) + r̃(ζ, ⌊X⌋₊)` for every real `X` (`ã = atilc = atil FIa`,
`g̃ = FIgtil`, `Ã = AcountAtilC`, `r̃ = rtildeFull FIr FIg FIgtil FIa`).

`Ad`'s second argument is floored (`Ad a d X = Σ_{n ≤ ⌊X⌋₊, d|n} a n`), so this is the companion's
(1.7) — `ASP.approx_atil` applied to `ASP.FI_approx` — evaluated at the integer `⌊X⌋₊`. -/
import Mathlib
import Submission.Work.FIChain.Defs
import Submission.ASP.S10
import Submission.ASP.S9g

set_option autoImplicit false

namespace Work.FIChain

open Finset
open scoped BigOperators

noncomputable section



/-- **(1.7) for the `λ⁺`-half, at real arguments**: `Ad ã(ζ)(X) = g̃(ζ)·Ã(⌊X⌋₊) + r̃(ζ, ⌊X⌋₊)`
for every real `X`.  (`Ad`'s second argument is floored, so this is `ASP.approx_atil` at the integer
`⌊X⌋₊`, with the base `(1.7)` `ASP.FI_approx`.) -/
theorem Ad_atilc_split_real (d : ℕ) (X : ℝ) :
    Submission.ASP.Ad atilc d X
      = Submission.ASP.FIgtil d * AcountAtilC ⌊X⌋₊
        + Submission.ASP.rtildeFull Submission.ASP.FIr Submission.ASP.FIg
            Submission.ASP.FIgtil Submission.ASP.FIa d ⌊X⌋₊ := by
  have h := Submission.ASP.approx_atil Submission.ASP.FIa Submission.ASP.FIg Submission.ASP.FIr
    Submission.ASP.FIgtil X (Submission.ASP.FI_approx X) d ⌊X⌋₊
  rw [show Submission.ASP.Ad atilc d X = Submission.ASP.Ad atilc d ((⌊X⌋₊ : ℕ) : ℝ) from by
    simp only [Submission.ASP.Ad, Nat.floor_natCast]]
  exact h


end

end Work.FIChain
