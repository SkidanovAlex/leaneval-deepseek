import Mathlib
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.index_eq_one_add_relIndex_of_doubleCoset_cover
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.relIndex_mul_card_of_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.Subgroup

theorem index_eq_one_add_card_of_doubleCoset_cover_of_notMem {G : Type*} [Group G] [Finite G]
    (U T B : Subgroup G) (w : G)
    (hB : B = U ⊔ T) (hUT : U ⊓ T = ⊥) (hTn : T ≤ Subgroup.normalizer (U : Set G))
    (hcover : ∀ g : G, g ∈ B ∨ ∃ b₁ b₂ : ↥B, g = (b₁ : G) * w * (b₂ : G))
    (hw : w ∉ B)
    (hinf : Nat.card ↥(B ⊓ B.map (MulAut.conj w).toMonoidHom) = Nat.card ↥T) :
    B.index = 1 + Nat.card ↥U := by
  -- The stabilizer congruence subgroup of the double coset decomposition.
  set N : Subgroup G := B ⊓ B.map (MulAut.conj w).toMonoidHom with hN
  -- Step 1: the double coset cover gives `B.index = 1 + N.relIndex B`.
  have hidx : B.index = 1 + N.relIndex B := by
    rw [hN]
    exact index_eq_one_add_relIndex_of_doubleCoset_cover B w hcover hw
  -- Step 2: `|B| = |U| * |T|`, since `B = U ⊔ T`, `U ⊓ T = ⊥` and `T` normalizes `U`.
  have hcardB : Nat.card ↥B = Nat.card ↥U * Nat.card ↥T := by
    rw [hB]
    exact card_sup_of_inf_eq_bot_of_le_normalizer U T hTn hUT
  -- Step 3: `|N| = |T|` by hypothesis.
  have hcardN : Nat.card ↥N = Nat.card ↥T := by
    rw [hN]
    exact hinf
  -- Step 4: `N.relIndex B * |N| = |B|`.
  have hrel : N.relIndex B * Nat.card ↥N = Nat.card ↥B :=
    relIndex_mul_card_of_le (by rw [hN]; exact inf_le_left)
  -- `T` is nonempty and finite, so `|T| > 0`.
  have hTpos : 0 < Nat.card ↥T := Nat.card_pos
  -- Cancelling `|T|` gives `N.relIndex B = |U|`.
  have hrelU : N.relIndex B = Nat.card ↥U :=
    Nat.mul_right_cancel hTpos (by rw [← hcardN, hrel, hcardB, hcardN])
  rw [hidx, hrelU]

end Commons.GroupTheory.Subgroup
