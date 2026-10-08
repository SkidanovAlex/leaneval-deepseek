/-
# Subnormal subgroups of a quasisimple group are central or the whole group

This file proves the dichotomy that underlies Bender's components theory: if `H ≤ Q` is
`Q`-subnormal and `Q` is quasisimple (Bender's convention: `⁅Q,Q⁆ = Q` and `Q/Z(Q)` simple),
then `H` is contained in the centralizer of `Q` in the ambient group, or `H = Q`.

## Mathematics

Everything happens in `↥Q`.  Let `D := H.subgroupOf Q`, subnormal in `↥Q`, and `Z := Z(↥Q)`.
Since `D` is subnormal, its image `D̄` in the simple group `↥Q/Z` is subnormal
(`Subgroup.IsSubnormal.quotient`), hence `⊥` or `⊤`.

* `D̄ = ⊥` means `D ≤ Z`, so `H` centralizes `Q`.
* `D̄ = ⊤` means `D ⊔ Z = ⊤`.  The centre normalizes `D` and `D` normalizes itself, so
  `D ◁ ↥Q`; and `↥Q/D ≅ Z/(D ∩ Z)` is commutative, so `⁅↥Q,↥Q⁆ ≤ D` by
  `Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top`.  As `Q` is perfect this
  gives `D = ⊤`, i.e. `H = Q`.

## Contents

* `subnormal_le_center_or_eq_top` : the abstract dichotomy in a group `S` with `S/Z(S)`
  simple and `S` perfect;
* `subnormal_le_centralizer_or_eq_of_isQuasisimple` : the requested ambient-group form.
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.commutator_eq_bot_of_isQuasisimple_of_isQuasisimple

set_option linter.style.haveILetI false

namespace Work.BMAX.Components

/-- **The dichotomy, abstract form.**  Let `D` be a subnormal subgroup of a group `S` whose
centre has simple quotient and which is perfect.  Then `D ≤ Z(S)` or `D = S`. -/
theorem subnormal_le_center_or_eq_top {S : Type*} [Group S] (D : Subgroup S)
    (hD : D.IsSubnormal) (hperf : commutator S = ⊤)
    (hsimp : IsSimpleGroup (S ⧸ Subgroup.center S)) :
    D ≤ Subgroup.center S ∨ D = ⊤ := by
  -- the image of `D` in `S/Z(S)` is subnormal in a simple group
  have hquot : (D.map (QuotientGroup.mk' (Subgroup.center S))).IsSubnormal :=
    hD.quotient (K := Subgroup.center S)
  rcases hquot.eq_bot_or_top_of_isSimpleGroup hsimp with hbot | htop
  · -- `D ≤ Z(S)`
    left
    have hle : D ≤ (QuotientGroup.mk' (Subgroup.center S)).ker :=
      (Subgroup.map_eq_bot_iff D).mp hbot
    rwa [QuotientGroup.ker_mk' (Subgroup.center S)] at hle
  · -- `D Z(S) = S`, hence `D ◁ S` with commutative quotient, hence `D = S`
    right
    have hsup : D ⊔ Subgroup.center S = ⊤ := by
      have h := QuotientGroup.comap_map_mk' (Subgroup.center S) D
      rw [htop, Subgroup.comap_top] at h
      rw [sup_comm] at h
      exact h.symm
    have hDnor : D.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      calc (⊤ : Subgroup S) = D ⊔ Subgroup.center S := hsup.symm
        _ ≤ Subgroup.normalizer (D : Set S) :=
            sup_le Subgroup.le_normalizer (Subgroup.center_le_normalizer (D : Set S))
    haveI : D.Normal := hDnor
    have hcomm : commutator S ≤ D :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (N := D) hsup
        (inferInstance : IsMulCommutative ↥(Subgroup.center S))
    rw [hperf] at hcomm
    exact eq_top_iff.mpr hcomm

/-- **A subnormal subgroup of a quasisimple subgroup is central or the whole group.**
In the ambient group `G`: if `H ≤ Q`, `H` is subnormal in `Q` and `Q` is quasisimple, then
`H ≤ C_G(Q)` or `Q ≤ H`. -/
theorem subnormal_le_centralizer_or_eq_of_isQuasisimple {G : Type*} [Group G] {H Q : Subgroup G}
    (hHQ : H ≤ Q) (hH : (H.subgroupOf Q).IsSubnormal) (hQ : Work.GW2.IsQuasisimple Q) :
    H ≤ Subgroup.centralizer (Q : Set G) ∨ Q ≤ H := by
  obtain ⟨hperf, hsimp⟩ := hQ
  -- transport perfectness of `Q` to the group `↥Q`
  have hperf' : commutator ↥Q = ⊤ := by
    refine Subgroup.map_injective (f := Q.subtype) Subtype.val_injective ?_
    rw [Subgroup.map_subtype_commutator, hperf, Subgroup.map_top, Subgroup.range_subtype]
  rcases subnormal_le_center_or_eq_top (H.subgroupOf Q) hH hperf' hsimp with hle | htop
  · left
    exact Work.BMAX.QuasiComm.le_centralizer_of_le_of_subgroupOf_le_center hHQ hle
  · right
    intro q hq
    have hmem : (⟨q, hq⟩ : ↥Q) ∈ H.subgroupOf Q := by rw [htop]; trivial
    rw [Subgroup.mem_subgroupOf] at hmem
    exact hmem

end Work.BMAX.Components
