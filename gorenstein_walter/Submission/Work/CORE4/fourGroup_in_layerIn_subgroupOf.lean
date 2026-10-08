import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.RED.DihedralFacts
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic

namespace Work.CORE4

open scoped MatrixGroups

open Subgroup

/-- A Klein four-group is carried to a Klein four-group by an injective homomorphism. -/
theorem isFourGroup_map_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {V : Subgroup G} (h : Work.GW2.IsFourGroup V) :
    Work.GW2.IsFourGroup (V.map f) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hf, h.1]
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hw
    rw [← map_pow, h.2 v hv, map_one]

/-- In `L₂(q)` with `q = p ^ e` odd and `q ≥ 5` there is a Klein four-group, and it can be
pulled back into `E = E(M) = layerIn C.D.M`.

`L₂(q)` has dihedral Sylow 2-subgroups (`l2syl`); a Sylow 2-subgroup is a non-cyclic 2-group,
hence of the form `DihedralGroup n` with `n` even (`even_dihedral_param_of_isPGroup_two_not_isCyclic`),
and an even dihedral group contains a Klein four-group (`DihedralFacts.fourGroup_exists_of_even`).
Pushing that four-group along the injective composite

`DihedralGroup n ≃* P ↪ L₂(q) ≃* E(M) ↪ M`

(where the last map is the inclusion `E(M) ≤ M`) gives the required `V ≤ E(M)`. -/
theorem fourGroup_in_layerIn_subgroupOf {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (C : Work.GW2.Case2Ctx6 B)
    (l2syl : Work.GW2.L2SylowDihedralProp)
    (p e : ℕ) [Fact p.Prime] (hshape : Work.GW2.NineShape C.D p e)
    (hiso : Nonempty (Work.GW2.layerIn C.D.M ≃* PSL(2, GaloisField p e))) :
    ∃ V : Subgroup ↥C.D.M,
      V ≤ (Work.GW2.layerIn C.D.M).subgroupOf C.D.M ∧ Work.GW2.IsFourGroup V := by
  obtain ⟨hodd, h5, -, -⟩ := hshape
  obtain ⟨φ⟩ := hiso
  -- a Sylow 2-subgroup of `L₂(q)`
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := PSL(2, GaloisField p e))
  -- it is dihedral, of order `2 * n` with `n ≥ 2`
  obtain ⟨n, hn2, ⟨ε⟩⟩ := l2syl p e hodd h5 S
  have hnc : ¬ IsCyclic ↥(S : Subgroup (PSL(2, GaloisField p e))) := by
    rw [MulEquiv.isCyclic ε, DihedralGroup.isCyclic_iff]
    omega
  -- hence `n` is nonzero and even
  obtain ⟨heven, hne⟩ :=
    Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic ε S.isPGroup' hnc
  haveI : NeZero n := hne
  -- an even dihedral group contains a Klein four-group
  obtain ⟨W, hW⟩ := Work.RED.DihedralFacts.fourGroup_exists_of_even n heven
  have hW' : Work.GW2.IsFourGroup W := hW
  -- the inclusion `E(M) ≤ M` (as a subgroup of `↥M`)
  have hle : Work.GW2.layerIn C.D.M ≤ C.D.M :=
    Subgroup.map_subtype_le (Work.GW2.layer ↥(C.D.M))
  -- the injective composite `DihedralGroup n → ↥E(M) → ↥M`
  let g : DihedralGroup n →* ↥(Work.GW2.layerIn C.D.M) :=
    φ.symm.toMonoidHom.comp
      (((S : Subgroup (PSL(2, GaloisField p e))).subtype).comp ε.symm.toMonoidHom)
  let ψ : DihedralGroup n →* ↥C.D.M := (Subgroup.inclusion hle).comp g
  have hψinj : Function.Injective ψ :=
    (Subgroup.inclusion_injective hle).comp
      (φ.symm.injective.comp
        (((S : Subgroup (PSL(2, GaloisField p e))).subtype_injective).comp ε.symm.injective))
  refine ⟨W.map ψ, ?_, ?_⟩
  · intro v hv
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨w, _hw, rfl⟩ := Subgroup.mem_map.mp hv
    simp only [ψ]
    exact (g w).2
  · exact isFourGroup_map_of_injective ψ hψinj hW'

end Work.CORE4
