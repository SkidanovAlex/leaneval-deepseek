import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.DoubleCoset.exists_map_conj_eq_inf_map_conj_of_doubleCoset_cover
import Submission.Work.Models.Port.Commons.GroupTheory.IsPGroup.inf_eq_bot_of_not_dvd_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.DoubleCoset

theorem inf_map_conj_eq_bot_of_doubleCoset_cover {G : Type*} [Group G] [Finite G]
    (T B : Subgroup G) (w : G)
    (hcover : ∀ g : G, g ∈ B ∨ ∃ b₁ b₂ : ↥B, g = (b₁ : G) * w * (b₂ : G))
    (hinf : B ⊓ B.map (MulAut.conj w).toMonoidHom = T)
    {U : Subgroup G} (hUB : U ≤ B) (hU : IsPGroup 2 U) (hTodd : Odd (Nat.card T))
    {g : G} (hg : g ∉ B) : U ⊓ B.map (MulAut.conj g).toMonoidHom = ⊥ := by
  -- The double coset cover gives that `B ⊓ B^g` is a conjugate of `T`, hence has odd order.
  obtain ⟨x, hx⟩ := exists_map_conj_eq_inf_map_conj_of_doubleCoset_cover T B w hcover hinf hg
  have hcard : Nat.card ↥(B ⊓ B.map (MulAut.conj g).toMonoidHom) = Nat.card T := by
    rw [hx]
    exact Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hnotdvd : ¬ 2 ∣ Nat.card ↥(B ⊓ B.map (MulAut.conj g).toMonoidHom) := by
    rw [hcard]
    obtain ⟨k, hk⟩ := hTodd
    rintro ⟨m, hm⟩
    omega
  -- A 2-subgroup intersected with a subgroup of odd order is trivial.
  have hbot : U ⊓ (B ⊓ B.map (MulAut.conj g).toMonoidHom) = ⊥ :=
    Commons.GroupTheory.IsPGroup.inf_eq_bot_of_not_dvd_card (p := 2) hU hnotdvd
  -- Since `U ≤ B`, `U ⊓ B^g = U ⊓ (B ⊓ B^g)`.
  calc U ⊓ B.map (MulAut.conj g).toMonoidHom
      = (U ⊓ B) ⊓ B.map (MulAut.conj g).toMonoidHom := by rw [inf_eq_left.mpr hUB]
    _ = U ⊓ (B ⊓ B.map (MulAut.conj g).toMonoidHom) := inf_assoc _ _ _
    _ = ⊥ := hbot

end Commons.GroupTheory.DoubleCoset
