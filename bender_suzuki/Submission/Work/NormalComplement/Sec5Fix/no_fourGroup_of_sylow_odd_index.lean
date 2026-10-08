import Mathlib
import Submission.Work.NormalComplement.Sec5Fix.Prelim

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open Submission.Blueprint

namespace Work.NormalComplement.Sec5Fix

/-- A four-group of a finite group `F` survives in every Sylow `2`-subgroup of `F`.  Here
`S ≤ H ≤ F` with `S` a `2`-subgroup of odd index in `H` (so `S` is a Sylow `2`-subgroup of `H`)
and `H` of odd index in `F` (so `S` is a Sylow `2`-subgroup of `F`); a four-group of `F` then
lies in a conjugate of `S`, hence is a four-group of `↥S`.

In the contrapositive form used downstream: if `↥S` has no four-group and `S` is a Sylow
`2`-subgroup obtained this way, then `F` has no four-group. -/
theorem no_fourGroup_of_sylow_odd_index {F : Type} [Group F] [Finite F] (H S : Subgroup F)
    (hSH : S ≤ H) (hSp : IsPGroup 2 S) (hSidx : ¬ 2 ∣ (S.subgroupOf H).index)
    (hidxH : Odd H.index) (hS4 : ¬ Submission.Blueprint.HasFourGroup ↥S) :
    ¬ Submission.Blueprint.HasFourGroup F := by
  intro h4
  -- `S` is a Sylow `2`-subgroup of `F`: its index is the product of its odd index in `H`
  -- and the odd index of `H` in `F`.
  have hrel : S.relIndex H = (S.subgroupOf H).index := rfl
  have hSindex : ¬ 2 ∣ S.index := by
    intro h2
    rw [← Subgroup.relIndex_mul_index hSH, hrel] at h2
    rcases (Nat.prime_two.dvd_mul).mp h2 with h1 | h1
    · exact hSidx h1
    · exact (Nat.not_even_iff_odd.mpr hidxH) (even_iff_two_dvd.mpr h1)
  let Ssyl : Sylow 2 F := hSp.toSylow hSindex
  -- The two commuting involutions of the four-group generate a `2`-subgroup of `F`.
  obtain ⟨a, b, ha, hb, hab_ne, hab_comm⟩ := h4
  have hA : IsPGroup 2 (Subgroup.zpowers a) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, ha]; norm_num⟩
  have hB : IsPGroup 2 (Subgroup.zpowers b) := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, hb]; norm_num⟩
  have hnorm : Subgroup.zpowers a ≤
      Subgroup.normalizer ((Subgroup.zpowers b : Subgroup F) : Set F) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hh
    rw [← hm]
    exact (Commute.zpow_left hab_comm.symm m).eq
  have hAB := IsPGroup.to_sup_of_normal_right' hA hB hnorm
  -- Embed it into a Sylow `2`-subgroup `Q`.
  obtain ⟨Q, hQle⟩ := IsPGroup.exists_le_sylow hAB
  have haQ : a ∈ (Q : Subgroup F) := hQle (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
  have hbQ : b ∈ (Q : Subgroup F) := hQle (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
  have hQ4 : Submission.Blueprint.HasFourGroup ↥Q := by
    refine ⟨⟨a, haQ⟩, ⟨b, hbQ⟩, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk]; exact ha
    · rw [Subgroup.orderOf_mk]; exact hb
    · intro hh; exact hab_ne (Subtype.ext_iff.mp hh)
    · exact Subtype.ext (by simpa using hab_comm)
  -- Sylow's theorem: `S` and `Q` are conjugate, hence `↥S` also has a four-group.
  exact hS4 (hasFourGroup_of_mulEquiv (Sylow.equiv Ssyl Q) hQ4)

end Work.NormalComplement.Sec5Fix
