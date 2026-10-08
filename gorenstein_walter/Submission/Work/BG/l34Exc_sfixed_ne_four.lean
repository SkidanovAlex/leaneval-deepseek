import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.thm32
import Submission.Work.BG.lemma24
import Submission.Work.BG.centralIntegral
import Submission.Work.BG.glaubValue
import Submission.Work.BG.lemma18LinearIndependent
import Submission.Work.BG.rem31Orth
import Submission.Work.BG.rem31StabCard
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.CharBridge
import Submission.Work.BG.bset_orbit_struct
import Submission.Work.BG.s02_lemma21
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.lemma33Aux
import Submission.Work.BG.lemma33ShapeA
import Submission.Work.BG.lemma33Plumb
import Submission.Work.BG.congContra
import Submission.Work.BG.l34ne_glauberman_contra
import Submission.Work.BG.l34ne_chi_even
import Submission.Work.BG.l34ne_deg_mod_four
import Submission.Work.BG.l34ne_restrict_shape

import Submission.Work.BG.l34ne_aux

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem l34Exc_sfixed_ne_four {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ f : ClassFunction ↥C.P.H0 ℂ → ClassFunction G ℂ, Work.GW2.C16.IsCoherent C f →
    ∀ χ : ClassFunction G ℂ, Work.BG.IsPmIrr χ →
    ∀ ν ∈ Work.GW2.C16.bset C f χ, Work.BG.sconj C ν ≠ ν →
      (Work.BG.sconj C ν ∉ Work.BG.lamOrbit C ν ∨ (Work.BG.lamOrbit C ν).ncard = D.n) →
      (Work.BG.lamOrbit C ν).ncard = 4 →
      Work.BG.sconj C '' Work.BG.lamOrbit C ν = Work.BG.lamOrbit C ν →
      ∀ ξ ∈ Work.GW2.C16.bset C f χ, ξ ≠ ν → ξ ≠ Work.BG.sconj C ν →
      Work.BG.sconj C ξ = ξ → (Work.BG.lamOrbit C ξ).ncard ≠ 4 → False :=
  Work.BG.l34ne_main D C

end Work.BG
