import Mathlib
import Submission.Work.Reductions.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Reductions

/-- If `t ∈ H` is an involution and `H` is strongly embedded, then the centralizer of `t`
is contained in `H`: an element `x ∉ H` commuting with `t` would put the involution `t` into
`H ⊓ H^x`, a group of odd order. -/
theorem stronglyEmbedded_centralizer_le {G : Type} [Group G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : t ∈ H)
    (h2 : orderOf t = 2) : Subgroup.centralizer ({t} : Set G) ≤ H := by
  obtain ⟨hne, heven, hodd⟩ := hH
  intro x hx
  by_contra hxH
  have hcomm : t * x = x * t := (Subgroup.mem_centralizer_iff.mp hx) t (Set.mem_singleton t)
  set K : Subgroup G := H ⊓ H.map (MulAut.conj x).toMonoidHom with hK
  have htK : t ∈ K := by
    rw [hK, Subgroup.mem_inf]
    refine ⟨ht, ?_⟩
    rw [Subgroup.mem_map]
    refine ⟨t, ht, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hcomm]
    group
  have horder : orderOf (⟨t, htK⟩ : K) = 2 := by
    rw [Subgroup.orderOf_mk, h2]
  have hdvd : 2 ∣ Nat.card K := by
    have h := Subgroup.card_subgroup_dvd_card (Subgroup.zpowers (⟨t, htK⟩ : K))
    rwa [Nat.card_zpowers, horder] at h
  have hoddK : Odd (Nat.card K) := by
    rw [hK]; exact hodd x hxH
  exact (Nat.not_even_iff_odd.mpr hoddK) (even_iff_two_dvd.mpr hdvd)

end Work.Reductions
