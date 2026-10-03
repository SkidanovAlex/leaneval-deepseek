/-
# `Submission.Work.FIPiChain.P5` --- the challenge from the areas' output alone

This is node **P5** of the lead design (`Submission/Work/FIFinal/PIREMOVAL_LEAD.md`, §3): the wiring
of the chapter.  The areas produce `Work.FITop4.Prop41StatementPiBig`
(`Work.FIFinal.prop41 (h4 : Area4_6c)`); nodes P1 and P2 turn it into the two *integrated* windows
at a common free scale `B = max (max B₁ B₂) 2`; node P4 (`Work.FIPiChain.primeSum_bound_of_windowsInt`)
runs the FI endgame there.  The result is the paper's Theorem 1 for `ã`, fed into the final mile
`Work.FIFinal.challenge_of_primeSumBound`.

The deliverable is `Work.FIPiChain.challenge_of_area4`:

  `Work.FITop4.Area4_6c → {p : ℕ | p.Prime ∧ ∃ a b : ℕ, p = a ^ 2 + b ^ 4}.Infinite`,

i.e. the challenge from **area 4 alone** (areas 1, 2, 3, 6, τ, 7 are consumed from disk inside
`Work.FIFinal.prop41`), with the unprovable `PiRemoval` **deleted** from the chain.
-/
import Mathlib
import Submission.Work.FIPiChain.P1Aw.BprimeWindowInt_ge
import Submission.Work.FIPiChain.P2Rho.RhoWindowInt2_ge
import Submission.Work.FIPiChain.P4
import Submission.Work.FIFinal.Bridge

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIPiChain

open Finset Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The endgame from the areas' `Π`-restricted Proposition 4.1 alone.**  This is the conclusion of
`Work.FIChain.primeSum_bound_of_prop41'` (the paper's Theorem 1 for `ã`) obtained by running the
endgame at the free scale `B = max (max B₁ B₂) 2`, where `B₁`, `B₂` are the thresholds of the two
`Π`-free integrated windows produced by the areas via nodes P1 and P2. -/
theorem primeSum_bound_of_PiBig (h : Work.FITop4.Prop41StatementPiBig) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      |(∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, Real.log (p : ℝ) * Submission.ASP.FIa p)
          - (4 / Real.pi) * Submission.ASP.Acount Submission.ASP.FIa (N : ℝ)|
        ≤ C * Work.FIChain.AcountAtilC N
            * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) := by
  obtain ⟨B₁, _hB₁pos, hP1⟩ := P1Aw.BprimeWindowInt_ge h
  obtain ⟨B₂, _hB₂pos, hP2⟩ := P2Rho.RhoWindowInt2_ge h
  exact primeSum_bound_of_windowsInt (max (max B₁ B₂) 2) (le_max_right _ _)
    (hP1 _ (le_trans (le_max_left B₁ B₂) (le_max_left _ _)))
    (hP2 _ (le_trans (le_max_right B₁ B₂) (le_max_left _ _)))

/-- **The challenge from the areas' `Π`-restricted Proposition 4.1.** -/
theorem challenge_of_PiBig' (h : Work.FITop4.Prop41StatementPiBig) :
    Work.FIFinal.ChallengeTheorem :=
  Work.FIFinal.challenge_of_primeSumBound
    (Work.FIFinal.primeSumBound_of_fichain (primeSum_bound_of_PiBig h))

/-- **The deliverable of the chapter**: the challenge from area 4 alone.  `Work.FIFinal.prop41`
consumes areas 1, 2, 3, 6, τ, 7 from disk (and takes area 4 as its hypothesis), producing the
`Π`-restricted Proposition 4.1; `challenge_of_PiBig'` runs the endgame on the areas' *integrated*
output, so the (unprovable, and unnecessary) `Π`-removal `Work.FIFinal.PiRemoval` no longer appears
anywhere. -/
theorem challenge_of_area4 (h4 : Work.FITop4.Area4_6c) :
    {p : ℕ | p.Prime ∧ ∃ a b : ℕ, p = a ^ 2 + b ^ 4}.Infinite :=
  challenge_of_PiBig' (Work.FIFinal.prop41 h4)

end

end Work.FIPiChain
