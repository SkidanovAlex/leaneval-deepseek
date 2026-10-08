import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.ChV12.L5Base

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

/-- In the `PSU3` situation `H` is strongly embedded, so an involution `v ∈ H` has its
centraliser inside `H`.  Indeed, let `u ∉ H` be an involution commuting with `v`.  Then
`v = u v u⁻¹ = (MulAut.conj u) v`, so `v` lies both in `H` and in its conjugate `H ^ u`;
strong embeddedness makes `Nat.card (H ⊓ H ^ u)` odd for `u ∉ H`, yet it is divisible by
`orderOf v = 2` — a contradiction. -/
theorem false_of_commuting_involutions {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t u v : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hu : orderOf u = 2) (hv : orderOf v = 2)
    (huH : u ∉ H) (hvH : v ∈ H) (hcomm : u * v = v * u) : False := by
  obtain ⟨_, _, hodd⟩ := hS.split.stronglyEmbedded
  have hoddUV : Odd (Nat.card (H ⊓ H.map (MulAut.conj u).toMonoidHom : Subgroup G)) := hodd u huH
  have hvmap : v ∈ H.map (MulAut.conj u).toMonoidHom := by
    refine ⟨v, hvH, ?_⟩
    change MulAut.conj u v = v
    rw [MulAut.conj_apply, hcomm]
    simp
  have hvK : v ∈ (H ⊓ H.map (MulAut.conj u).toMonoidHom : Subgroup G) := ⟨hvH, hvmap⟩
  have hdvd : 2 ∣ Nat.card (H ⊓ H.map (MulAut.conj u).toMonoidHom : Subgroup G) := by
    have h := Subgroup.orderOf_dvd_natCard (H ⊓ H.map (MulAut.conj u).toMonoidHom : Subgroup G) hvK
    rwa [hv] at h
  exact (Nat.not_even_iff_odd.mpr hoddUV) (even_iff_two_dvd.mpr hdvd)

end Work.PSU3.StageA
