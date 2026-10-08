import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.StageB.ThetaMain

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

theorem theta_trivial {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n) {ω : G}
    (hω : Work.PSU3.OmegaHyp fr ω) :
    ∃ i : ℕ,
      (∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
        (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ (2 ^ (i + 1))) ∧
      ω ^ 2 = fr.zc (((fr.κ fr.ζ : Work.PSU3.E n) + (fr.κ fr.ζ : Work.PSU3.E n)⁻¹) ^ (2 ^ i)) := by
  obtain ⟨i, hi, hω2⟩ := theta_trivial_frame fr hS hω
  refine ⟨i, ?_, ?_⟩
  · intro a ha
    have h := hi a ha
    rw [h, Units.val_pow_eq_pow_val]
  · exact hω2

end Work.PSU3.StageB
