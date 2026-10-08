import Mathlib
import Submission.Work.RED.Basic

namespace Work.RED

/-- If `K` is normal in `N` and `H` is characteristic in `K` (with `H ≤ K ≤ N`), then `H`
is normal in `N`: conjugation by an element of `N` induces an automorphism of `K` (since `K`
is normal in `N`), and `H`, being characteristic in `K`, is fixed by all such automorphisms.

This is the field `char_normal` of `Work.RED.GW2.MinimalNormalFactsProp`; the minimality of `N`
is not needed for this particular statement. -/
theorem MNF_char_normal (G : Type*) [Group G] [Finite G] (N K H : Subgroup G)
    (hN : Work.RED.GW2.IsMinimalNormal N) (hHK : H ≤ K) (hKN : K ≤ N)
    (hK : (K.subgroupOf N).Normal) (hH : (H.subgroupOf K).Characteristic) :
    (H.subgroupOf N).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (hHK.trans hKN)]
  intro h k hh hk
  have hhK : h ∈ K := hHK hh
  -- The automorphism of `↥K` induced by conjugation with `k ∈ N`, transported along
  -- `↥(K.subgroupOf N) ≃* ↥K`.
  have hchar := (Subgroup.characteristic_iff_map_le.mp hH)
      ((Subgroup.subgroupOfEquivOfLe hKN).symm.trans
        (((MulAut.conjNormal (⟨k, hk⟩ : ↥N)) : MulAut ↥(K.subgroupOf N)).trans
          (Subgroup.subgroupOfEquivOfLe hKN)))
  have hx : (⟨h, hhK⟩ : ↥K) ∈ H.subgroupOf K := hh
  have hy := hchar ⟨(⟨h, hhK⟩ : ↥K), hx, rfl⟩
  have hcoe : (((Subgroup.subgroupOfEquivOfLe hKN).symm.trans
        (((MulAut.conjNormal (⟨k, hk⟩ : ↥N)) : MulAut ↥(K.subgroupOf N)).trans
          (Subgroup.subgroupOfEquivOfLe hKN))) (⟨h, hhK⟩ : ↥K) : G) = k * h * k⁻¹ := by
    simp only [MulEquiv.trans_apply, Subgroup.subgroupOfEquivOfLe_apply_coe,
      MulAut.conjNormal_apply]
    rfl
  simp only [Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom] at hy
  rw [hcoe] at hy
  exact hy

end Work.RED
