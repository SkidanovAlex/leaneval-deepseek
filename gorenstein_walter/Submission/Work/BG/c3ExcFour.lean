import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.glaubValue
import Submission.Work.BG.lemma18LinearIndependent
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.l34Exc_sfixed_four

/-!
# Area BG: `Work.BG.c3ExcFour`

The exceptional configuration of BG 1981, Lemma 3.4 with `|Λξ| = 4` (the `|S| = 8` branch).

The statement is the one requested by area `BG`/`S10`; it is *character for character* the
statement of `Work.BG.l34Exc_sfixed_four` (`Submission/Work/BG/l34Exc_sfixed_four.lean`),
which was proved in the shared repository: with `𝒮(χ) = bset C f χ`, if `𝒮(χ) ∋ ν` is not
`s`-fixed with `|Λν| = 4` and `s`-stable orbit, and `𝒮(χ) ∋ ξ ∉ {ν, ν^s}` is `s`-fixed with
`|Λξ| = 4`, then the two `s`-fixed members of `Λν` supplied by Lemma 2.1 lie in `𝒮(f μ)` for a
non-`s`-fixed `μ ∈ Λξ` (coherence clause (iv) plus `(f ξ, f ν') = 0`), contradicting BG Lemma 3.3
in the form `Work.BG.l34TwoSfixedMaximal`.  We therefore close the goal by that library lemma;
nothing else is needed.
-/

namespace Work.BG

theorem c3ExcFour {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ → OddOrder.RepresentationTheory.ClassFunction G ℂ,
      Work.GW2.C16.IsCoherent C f →
    ∀ χ : OddOrder.RepresentationTheory.ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν →
      Work.BG.sconj C ξ = ξ → (Work.BG.lamOrbit C ξ).ncard = 4 → False := by
  intro hCompat hSec3
  exact l34Exc_sfixed_four D C hCompat hSec3

end Work.BG
