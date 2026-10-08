import Mathlib
import Submission.Work.AUTL2.Defs
import Submission.Work.AUTL2.Elementary

namespace Work.AUTL2.Helper

/-- If every Sylow 2-subgroup of a finite group `G` is cyclic or dihedral, then `G` has no
elementary abelian subgroup of order `8`: the 2-rank of `G` is at most `2`.

This is the `G`-level version of `Work.AUTL2.not_elementaryAbelian_card_eight_of_dihOrCyc`
(which deals with the Sylow 2-subgroup itself): an elementary abelian subgroup of order `8` is
a 2-subgroup, hence lies in a Sylow 2-subgroup, where the statement is already known. -/
theorem not_elementaryAbelian_card_eight_of_dihOrCycSylow {G : Type*} [Group G] [Finite G]
    (hdih : Work.GW2.DihOrCycSylow G) :
    ¬ ∃ E : Subgroup G, Nat.card E = 8 ∧ ∀ x ∈ E, x * x = 1 := by
  rintro ⟨E, hcard, hE⟩
  -- `E` is a 2-group (of order `8 = 2 ^ 3`), so it lies in a Sylow 2-subgroup `P`.
  have hpg : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  obtain ⟨P, hEP⟩ := hpg.exists_le_sylow
  have hP : IsCyclic ↥(P : Subgroup G) ∨
      ∃ n : ℕ, Nonempty (↥(P : Subgroup G) ≃* DihedralGroup n) := hdih P
  refine Work.AUTL2.not_elementaryAbelian_card_eight_of_dihOrCyc (P := ↥(P : Subgroup G))
    hP ⟨E.subgroupOf (P : Subgroup G), ?_, ?_⟩
  · -- cardinality: `E.subgroupOf P` is the same subgroup as `E`, inside `P`
    have h2 := Subgroup.card_map_of_injective
      (K := E.subgroupOf (P : Subgroup G)) (f := (P : Subgroup G).subtype)
      (Subgroup.subtype_injective (P : Subgroup G))
    rw [Subgroup.map_subgroupOf_eq_of_le hEP] at h2
    rw [← h2, hcard]
  · -- all elements of `E.subgroupOf P` are involutions
    intro x hx
    have hxE : (x : G) ∈ E := hx
    have h1 : (x : G) * (x : G) = 1 := hE (x : G) hxE
    exact Subtype.ext (by simpa [pow_two] using h1)

end Work.AUTL2.Helper
