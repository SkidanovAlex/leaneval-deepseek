import Submission.Work.Endgame.Defs
import Submission.Work.Endgame.oddCore_eq_bot_of_isSimpleGroup_of_even
import Submission.Work.Skeleton.card_subgroup_lt_card

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The 2-rank one case of the endgame

In a simple group of even order without a four-group, no subgroup is strongly embedded.  This is
the contradiction that closes the case `¬ HasFourGroup G` of the endgame.

The argument: `IsStronglyEmbedded M` gives an involution `t` and `Even (Nat.card G)`; Brauer–Suzuki
applied to `t` gives `O(G) ⊔ C_G(t) = ⊤`, and `O(G) = ⊥` in a simple group of even order, so `t`
is central; then `⟨t⟩` is normal, hence `⊥` or `⊤` by simplicity, and `t ≠ 1` forces
`Nat.card G = orderOf t = 2`, which contradicts `Even (Nat.card M)` for the proper subgroup `M`.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.Endgame

theorem not_isStronglyEmbedded_of_not_hasFourGroup (hBrSz : BrauerSuzukiProp) {G : Type}
    [Group G] [Finite G] [IsSimpleGroup G] (h4 : ¬ HasFourGroup G) (M : Subgroup G) :
    ¬ IsStronglyEmbedded M := by
  intro hM
  have hEvenG : Even (Nat.card G) := even_natCard_of_isStronglyEmbedded hM
  have hcore : oddCore G = ⊥ := oddCore_eq_bot_of_isSimpleGroup_of_even hEvenG
  -- Cauchy's theorem produces an involution
  rw [even_iff_two_dvd] at hEvenG
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 hEvenG
  -- Brauer–Suzuki: `t` is central
  have hC : Subgroup.centralizer ({t} : Set G) = ⊤ := by
    have h := hBrSz G h4 t ht
    rwa [hcore, bot_sup_eq] at h
  have hcent : ∀ y : G, y * t = t * y := fun y =>
    Subgroup.mem_centralizer_singleton_iff.mp (hC ▸ Subgroup.mem_top y)
  have hle : Subgroup.zpowers t ≤ Subgroup.center G :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_center_iff.mpr hcent)
  have hnormal : (Subgroup.zpowers t).Normal := Subgroup.normal_of_le_center hle
  have htne : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have htop : Subgroup.zpowers t = ⊤ := by
    rcases hnormal.eq_bot_or_eq_top with h | h
    · exact absurd (Subgroup.zpowers_eq_bot.mp h) htne
    · exact h
  have hcardG : Nat.card G = 2 := by
    rw [← Subgroup.card_top (G := G), ← htop, Nat.card_zpowers, ht]
  -- `M` has even order but is proper in a group of order `2`
  have hlt : Nat.card M < Nat.card G := Work.Skeleton.card_subgroup_lt_card M hM.1
  have hpos : 0 < Nat.card M :=
    Nat.card_pos_iff.mpr ⟨⟨1, M.one_mem⟩, inferInstance⟩
  have heven : Even (Nat.card M) := hM.2.1
  rw [hcardG] at hlt
  rw [even_iff_two_dvd] at heven
  omega

end Work.Endgame
