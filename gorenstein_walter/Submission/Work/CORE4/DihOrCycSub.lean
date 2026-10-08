import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.FUS.DihedralSylow.subgroup_cyclic_or_dihedral
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.FUS.Dihedral

namespace Work.CORE4

open Subgroup

/-- **Sylow 2-shape passes to subgroups.**  If every Sylow `2`-subgroup of `G` is cyclic or
dihedral (`Work.GW2.DihOrCycSylow G`), then the same holds for every subgroup `K ≤ G`.

A Sylow `2`-subgroup `P` of `↥K` maps to the `2`-subgroup `X = P.map K.subtype ≤ G`, which lies
in a Sylow `2`-subgroup `S` of `G`; `P ≅ X`.  If `S` is cyclic, so is `X ≤ S`.  If
`S ≅ DihedralGroup n`, then `|S| = 2n ≤ |G|` forces `n ≠ 0`; for `n = 1` `S` is again cyclic, and
for `n ≥ 2` `Work.FUS.DihedralSylow.subgroup_cyclic_or_dihedral` applies to `X`. -/
theorem DihOrCycSub {G : Type*} [Group G] [Finite G] (h : Work.GW2.DihOrCycSylow G)
    (K : Subgroup G) : Work.GW2.DihOrCycSylow ↥K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro P
  -- `P` viewed inside `G`
  set X : Subgroup G := (P : Subgroup ↥K).map K.subtype with hXdef
  have hX : IsPGroup 2 X := IsPGroup.map P.isPGroup' K.subtype
  obtain ⟨S, hXS⟩ := hX.exists_le_sylow
  -- `↥P ≃* ↥X`
  have ePX : ↥(P : Subgroup ↥K) ≃* ↥X :=
    Subgroup.equivMapOfInjective (P : Subgroup ↥K) K.subtype (Subgroup.subtype_injective K)
  -- a subgroup of a cyclic group is cyclic
  have cyc_of_le_sylow (hcyc : IsCyclic ↥S) : IsCyclic ↥(P : Subgroup ↥K) := by
    haveI : IsCyclic ↥S := hcyc
    haveI : IsCyclic ↥(X.subgroupOf S) := inferInstance
    exact (MulEquiv.isCyclic (ePX.trans (Subgroup.subgroupOfEquivOfLe hXS).symm)).mpr inferInstance
  rcases h S with hcyc | ⟨n, hn⟩
  · exact Or.inl (cyc_of_le_sylow hcyc)
  · obtain ⟨eS⟩ := hn
    by_cases hn2 : 2 ≤ n
    · rcases Work.FUS.DihedralSylow.subgroup_cyclic_or_dihedral S n hn2 ⟨eS⟩ X hX with
        hcyc | ⟨m, _hm2, hiso⟩
      · exact Or.inl ((MulEquiv.isCyclic ePX).mpr hcyc)
      · obtain ⟨e⟩ := hiso
        exact Or.inr ⟨m, ⟨ePX.trans e⟩⟩
    · -- `n ≤ 1`: then `S` is cyclic (the case `n = 0` is impossible for a finite group)
      have hcardS : Nat.card ↥(S : Subgroup G) = 2 * n := by
        rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
      have hpos : 0 < Nat.card ↥(S : Subgroup G) := by
        haveI : Nonempty ↥(S : Subgroup G) := ⟨⟨1, (S : Subgroup G).one_mem⟩⟩
        exact Nat.card_pos
      have hn1 : n = 1 := by omega
      haveI : IsCyclic (DihedralGroup n) := DihedralGroup.isCyclic_iff.mpr hn1
      exact Or.inl (cyc_of_le_sylow ((MulEquiv.isCyclic eS).mpr inferInstance))

end Work.CORE4
