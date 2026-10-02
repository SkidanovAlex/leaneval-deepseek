import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.parLam_eq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- `parSigma` is always one of the two square roots of unity. -/
theorem parSigma_eq_neg_one_or_one (S : SplitData d) (c : ℂ) :
    parSigma S c = -1 ∨ parSigma S c = 1 := by
  unfold parSigma
  split <;> [left; right] <;> norm_num

/-- **The wall identity in multiplication form.**  On a small ball around `c₀`, the branch
corrected direction `parLam = σ · dir G` of `G` satisfies `parLam · σ · ‖G‖ = G`; equivalently
`parLam² · ‖G‖ = σ · G`.  This is the form in which the wall is used when assembling the
parameter normal form: off the collision locus it is the rearrangement of
`parLam = σ · G / ‖G‖`, and on the collision locus `G = 0` both sides vanish. -/
theorem parLam_sigma_norm_Gc {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ',
      Work.PARIMPL.ParSplit.parLam S c * (Work.PARIMPL.ParSplit.parSigma S c : ℂ)
        * (‖Work.PARIMPL.ParSplit.Gc S c‖ : ℂ) = Work.PARIMPL.ParSplit.Gc S c := by
  obtain ⟨ρ', hρ', hρ'ρ, h⟩ := parLam_eq S
  refine ⟨ρ', hρ', hρ'ρ, fun c hc => ?_⟩
  rcases eq_or_ne (Gc S c) 0 with hG | hG
  · rw [hG]; simp
  · have hlam := h c hc hG
    have hn : (‖Gc S c‖ : ℂ) ≠ 0 := by
      exact_mod_cast (norm_ne_zero_iff.mpr hG)
    rw [hlam]
    rcases parSigma_eq_neg_one_or_one S c with h1 | h1
    · rw [h1]
      norm_num
      rw [div_mul_cancel₀]
      · ring
      · exact hn
    · rw [h1]
      norm_num
      exact div_mul_cancel₀ _ hn

end Work.PARIMPL.ParSplit
