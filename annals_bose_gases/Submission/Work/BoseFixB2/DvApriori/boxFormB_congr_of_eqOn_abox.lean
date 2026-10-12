import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB2.Polar.wordB_box_local
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB2.DvApriori.boxFormB_congr_of_eqOn_abox`

The box-restricted form `Work.BoseKinLoc.boxFormB N v g ℓ μ d s εT b` is defined from box
integrals over the centred configuration box `Submission.BoseGases.abox N ℓ`; hence it only
sees the restriction of the state to that box.  This is the packaging of
`Work.BoseFixB2.Polar.boxFormB_congr_of_pos` (proved there from the box-locality
`Sector.fsT_box_invariant` of the slot kinetic word) with the hypothesis `0 < ℓ` written
first and the states named `Φ`, `Ψ`.
-/

namespace Work.BoseFixB2.DvApriori

theorem boxFormB_congr_of_eqOn_abox {m : ℕ} {v g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {ℓ μ d s εT b : ℝ} (hℓ : 0 < ℓ) {Φ Ψ : Submission.BoseGases.X m → ℝ}
    (h : ∀ x ∈ Submission.BoseGases.abox m ℓ, Φ x = Ψ x) :
    Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b Φ
      = Work.BoseKinLoc.boxFormB m v g ℓ μ d s εT b Ψ :=
  Work.BoseFixB2.Polar.boxFormB_congr_of_pos hℓ h

end Work.BoseFixB2.DvApriori
