import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.ChV12.structureIdentity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

theorem distinguished_exists {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) :
    ∃ s ∈ Q, orderOf s = 2 ∧ ∃ r ∈ Q, t * s * t = r⁻¹ * t * r := by
  -- Peterfalvi II Ch. V §2 Lemma 1 b), delivered as `structureIdentity`:
  -- there is `s ∈ Inv Q` and `ρ ∈ Q` with `t * s * t⁻¹ = ρ * t * ρ⁻¹`.
  obtain ⟨p, hp, _⟩ :=
    Work.ThmF.ChV12.structureIdentity (Work.ThmF.IsSplitRankOne.toData hS.split)
  obtain ⟨hsQ, hs2, hρQ, hsr⟩ := hp
  -- `t` is an involution, so `t⁻¹ = t`.
  have htt : t⁻¹ = t := by
    have h2 : t ^ 2 = 1 := by
      have h := pow_orderOf_eq_one t
      rwa [hS.split.invol] at h
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h2)
  rw [htt] at hsr
  -- Peterfalvi's form: `t s t = r⁻¹ t r` with `r := ρ⁻¹`.
  exact ⟨p.1, hsQ, hs2, p.2⁻¹, Q.inv_mem hρQ, by rw [inv_inv]; exact hsr⟩

end Work.PSU3.StageA
