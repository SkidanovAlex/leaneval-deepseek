import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.DihHelp.cyclicSqOne
import Submission.Work.DSTR.DihHelp.dihTransfer

/-!
# DS3: a D-group has 2-rank at most two (`Work.DSTR.twoRank`)

The statement proved here is `Work.GW2.TwoRankProp`: if `X` is a finite group whose Sylow
2-subgroups are cyclic or dihedral, then every elementary abelian 2-subgroup `E ≤ X`
(commutative, `x ^ 2 = 1` for all `x ∈ E`) has `Nat.card E ≤ 4`.

The argument is the elementary one, and it splits into three pieces.

* An elementary abelian 2-subgroup is a 2-group: `x ^ 2 = 1` gives `orderOf x ∣ 2`, so
  `IsPGroup 2 ↥E`; by Sylow's first theorem (`IsPGroup.exists_le_sylow`) `E` lies in some
  Sylow 2-subgroup `Q` of `X`.
* If `Q` is cyclic then `E` is cyclic (a subgroup of a cyclic group is cyclic), and a cyclic
  group all of whose elements square to `1` has order at most `2`: a generator `g` satisfies
  `g ^ 2 = 1`, so `orderOf g = Nat.card ↥E` is `≤ 2`.  This is the delegated lemma
  `Work.DSTR.DihHelp.cyclicSqOne`.
* If `Q` is dihedral, `Q ≃* DihedralGroup n`, then the composite
  `↥E ↪ ↥Q ≃* DihedralGroup n` is injective and its range `A ≤ DihedralGroup n` is an abelian
  subgroup with the same cardinality as `E`.  The rank input `DihedralAbelianRankProp` (`hDR`)
  says that `A` is cyclic or `Nat.card A ≤ 4`; in the cyclic case all elements of `A` still
  square to `1`, so again `Nat.card A ≤ 2`.  Hence `Nat.card E ≤ 4`.  This is the delegated
  lemma `Work.DSTR.DihHelp.dihTransfer`.
-/

namespace Work.DSTR

/-- **DS3** (`Work.GW2.TwoRankProp`): a group with cyclic or dihedral Sylow 2-subgroups has 2-rank at most 2, i.e. every elementary abelian 2-subgroup has order at most `4`. -/
theorem twoRank (hDR : Work.GW2.DihedralAbelianRankProp) : Work.GW2.TwoRankProp := by
  intro X _ _ hSyl E hcomm h2
  -- `E` is an elementary abelian 2-group.
  have h2E : ∀ g : ↥E, g ^ 2 = 1 := fun g => Subtype.ext (by simpa using h2 (g : X) g.2)
  have hPE : IsPGroup 2 ↥E := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro g
    exact ⟨1, by rw [pow_one, orderOf_dvd_iff_pow_eq_one]; exact h2E g⟩
  -- Hence `E` is contained in a Sylow 2-subgroup of `X`.
  obtain ⟨Q, hEQ⟩ := hPE.exists_le_sylow
  rcases hSyl Q with hcycQ | ⟨n, ⟨e⟩⟩
  · -- `Q` cyclic: then so is `E`, and a cyclic exponent-2 group has order at most `2`.
    have hcycE : IsCyclic ↥E := @Subgroup.isCyclic_of_le X _ E (Q : Subgroup X) hEQ hcycQ
    have hb := Work.DSTR.DihHelp.cyclicSqOne hcycE h2E
    omega
  · -- `Q` dihedral: transport `E` into `DihedralGroup n` and use the rank input.
    exact Work.DSTR.DihHelp.dihTransfer hDR e hEQ hcomm h2E

end Work.DSTR
