import Mathlib
import Submission.Work.Models.Port.BenderSetup
import Submission.Work.Models.Basic
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.index_eq_one_add_relIndex_of_doubleCoset_cover
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.relIndex_mul_card_of_le

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.Abstract

open LeanEval.GroupTheory.Defs

/-- For a Bender pair, the intersection of the Borel `B` with its `w`-conjugate is the torus
`T`.  Proof: `T ≤ B` and `T = T^w ≤ B^w`, so `T ≤ N := B ⊓ B^w`; the Bruhat decomposition
`G = B ∪ BwB` (with `w ∉ B`) gives `B.index = 1 + N.relIndex B`, whence `N.relIndex B = |U|`
from `B.index = |U| + 1`; combined with `|B| = N.relIndex B * |N|` and `|B| = |U| * |T|`
this forces `|N| = |T|`, and the inclusion `T ≤ N` upgrades to equality. -/
theorem inf_conj_w {G : Type*} [Group G] [Finite G] (P : Submission.BenderPair G) :
    P.B ⊓ Submission.Blueprint.conj P.w P.B = P.T := by
  set N : Subgroup G := P.B ⊓ Submission.Blueprint.conj P.w P.B with hN
  -- The double-coset cover `G = B ∪ BwB` gives `[G : B] = 1 + [B : N]`.
  have hidx : P.B.index = 1 + N.relIndex P.B := by
    rw [hN]
    exact Commons.GroupTheory.Subgroup.index_eq_one_add_relIndex_of_doubleCoset_cover
      P.B P.w P.bruhat P.hwB
  -- With `[G : B] = |U| + 1` this forces `[B : N] = |U|`.
  have hrelU : N.relIndex P.B = Nat.card ↥P.U := by
    have h := P.hindex
    rw [hidx] at h
    omega
  -- `|B| = |U| * |T|`.
  have hcardB : Nat.card ↥P.B = Nat.card ↥P.U * Nat.card ↥P.T := by
    rw [P.hB]
    exact Commons.GroupTheory.Subgroup.card_sup_of_inf_eq_bot_of_le_normalizer
      P.U P.T P.hTnU P.hUT
  have hNB : N ≤ P.B := by rw [hN]; exact inf_le_left
  -- `[B : N] * |N| = |B|`.
  have hrel : N.relIndex P.B * Nat.card ↥N = Nat.card ↥P.B :=
    Commons.GroupTheory.Subgroup.relIndex_mul_card_of_le hNB
  -- Therefore `|N| = |T|`.
  have hcardN : Nat.card ↥N = Nat.card ↥P.T := by
    have hpos : 0 < Nat.card ↥P.U := Nat.card_pos
    refine Nat.mul_left_cancel hpos ?_
    calc Nat.card ↥P.U * Nat.card ↥N = N.relIndex P.B * Nat.card ↥N := by rw [hrelU]
      _ = Nat.card ↥P.B := hrel
      _ = Nat.card ↥P.U * Nat.card ↥P.T := hcardB
  -- `T ≤ N`: `T ≤ B`, and `w ∈ N(T)` gives `T = T^w ≤ B^w`.
  have hTN : P.T ≤ N := by
    intro t ht
    rw [hN, Subgroup.mem_inf]
    refine ⟨P.T_le_B ht, ?_⟩
    rw [Work.Models.mem_conj_iff]
    have hmem : P.w⁻¹ * t * P.w ∈ P.T := by
      have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ P.hwT) t).mp ht
      simpa using h
    exact P.T_le_B hmem
  exact (Subgroup.eq_of_le_of_card_ge hTN (le_of_eq hcardN)).symm

end Work.Models.Abstract
