import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.hcan_pow_m_eq_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.StepB

theorem hcan_mem_W_of_good_generating {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hgen : orderOf (fr.ζ : G) = Nat.card ↥(Work.ThmF.W H t))
    (hpow : ∀ x ∈ Submission.Blueprint.twoPoint H t,
      x ^ Nat.card ↥(Work.ThmF.W H t) = 1 → x ∈ Work.ThmF.W H t)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr) (ω * Work.PSU3.StageB.zcQF fr α)) :
    (Work.PSU3.StageB.hcan hS.split ω : G) ∈ Work.ThmF.W H t := by
  -- §2 (18): the `h`-component twisted by `ζ⁻¹` has order dividing `orderOf fr.ζ`.
  have hpowζ : (((Work.PSU3.StageB.hcan hS.split ω : G) * (fr.ζ : G)⁻¹) ^ orderOf (fr.ζ : G)) = 1 := by
    have h := Work.PSU3.StageB.Omega.hcan_pow_m_eq_one hS fr hω hωf
    rw [← Subgroup.orderOf_coe fr.ζ] at h
    exact h
  -- the twisted element lies in `D = twoPoint H t`
  have hxmem : (Work.PSU3.StageB.hcan hS.split ω : G) * (fr.ζ : G)⁻¹
      ∈ Submission.Blueprint.twoPoint H t :=
    (Submission.Blueprint.twoPoint H t).mul_mem (Work.PSU3.StageB.hcan hS.split ω).2
      ((Submission.Blueprint.twoPoint H t).inv_mem (fr.KW_le fr.ζ.2))
  -- hypothesis `hpow`, at exponent `|W| = orderOf fr.ζ`
  have hxW : (Work.PSU3.StageB.hcan hS.split ω : G) * (fr.ζ : G)⁻¹ ∈ Work.ThmF.W H t :=
    hpow _ hxmem (by rw [← hgen]; exact hpowζ)
  -- `ζ ∈ W`, so undo the twist
  have hζW : (fr.ζ : G) ∈ Work.ThmF.W H t := fr.ζ_mem_W
  have hdecomp : (Work.PSU3.StageB.hcan hS.split ω : G) =
      ((Work.PSU3.StageB.hcan hS.split ω : G) * (fr.ζ : G)⁻¹) * (fr.ζ : G) := by group
  rw [hdecomp]
  exact (Work.ThmF.W H t).mul_mem hxW hζW

end Work.PSU3.StageB.StepB
