/-
# A non-cyclic `2`-subgroup with dihedral ambient image contains a Klein four-subgroup

Let `P ≤ S ≤ G` be subgroups of a group `G` with `S ≃* DihedralGroup n` (transported by `ψ`),
and suppose that `P` is a `2`-group which is not cyclic.  Then `P` contains a subgroup `V` of
order `4` all of whose elements are involutions, i.e. a Klein four-subgroup.

The argument is the natural reduction to the dihedral case:

* the image `Q := (P.subgroupOf S).map ψ ≤ DihedralGroup n` is again a `2`-group
  (`IsPGroup.of_equiv` followed by `IsPGroup.map`), and it is not cyclic, because `ψ` restricts
  to an isomorphism `↥P ≃* ↥Q` (`Subgroup.subgroupOfEquivOfLe` composed with
  `Subgroup.equivMapOfInjective`, transported by `MulEquiv.isCyclic`);
* the dihedral input `v2_dihedral_two_subgroup_has_four` produces a Klein four-subgroup `W ≤ Q`;
* pulling `W` back along `ψ` (i.e. taking `(W.comap f).map S.subtype`) gives a subgroup of `G`
  that lies in `P`, has four elements, and consists of involutions.

This is the `v2` copy of
`Work.CORE4.L2PAux.exists_four_of_noncyclic_two_subgroup_of_dihedral`; it rests on the clash-free
dihedral statement `Work.CORE4.L2PAux.v2_dihedral_two_subgroup_has_four` and on no unproved
material.
-/
import Mathlib
import Submission.Work.CORE4.L2PAux.v2_dihedral_two_subgroup_has_four

namespace Work.CORE4.L2PAux

theorem v2_exists_four_of_noncyclic_two_subgroup_of_dihedral {G : Type*} [Group G]
    (P S : Subgroup G) (hPS : P ≤ S) {n : ℕ} (ψ : S ≃* DihedralGroup n)
    (hP : IsPGroup 2 P) (hnc : ¬ IsCyclic P) :
    ∃ V : Subgroup G, V ≤ P ∧ Nat.card V = 4 ∧ ∀ v ∈ V, v ^ 2 = 1 := by
  classical
  let f : ↥S →* DihedralGroup n := ψ.toMonoidHom
  let Q : Subgroup (DihedralGroup n) := (P.subgroupOf S).map f
  have hf_inj : Function.Injective f := ψ.injective
  -- `Q` is again a `2`-group ...
  have hQpg : IsPGroup 2 Q := (hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPS).symm).map f
  -- ... and is not cyclic, since `↥P ≃* ↥Q`.
  have hQnc : ¬ IsCyclic Q := by
    intro hQcyc
    refine hnc ?_
    exact (MulEquiv.isCyclic
      ((Subgroup.subgroupOfEquivOfLe hPS).symm.trans
        (Subgroup.equivMapOfInjective (P.subgroupOf S) f hf_inj))).mpr hQcyc
  obtain ⟨W, hWQ, hWcard, hWsq⟩ := v2_dihedral_two_subgroup_has_four Q hQpg hQnc
  refine ⟨(W.comap f).map S.subtype, ?_, ?_, ?_⟩
  · -- the pull-back lies in `P`
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [Subgroup.mem_comap] at hy
    have hyP : (y : G) ∈ P := by
      have hyQ : f y ∈ Q := hWQ hy
      rw [Subgroup.mem_map] at hyQ
      obtain ⟨p, hp, hpf⟩ := hyQ
      have hpy : p = y := hf_inj hpf
      have hpP : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hp
      rwa [hpy] at hpP
    rwa [← hyx]
  · -- the pull-back has four elements
    rw [Subgroup.card_map_of_injective S.subtype_injective]
    have hrange : W ≤ f.range := le_trans hWQ (Subgroup.map_le_range f (P.subgroupOf S))
    have hWmap : W = (W.comap f).map f := (Subgroup.map_comap_eq_self hrange).symm
    have h1 : Nat.card ↥((W.comap f).map f) = Nat.card ↥(W.comap f) :=
      Subgroup.card_map_of_injective hf_inj
    rw [← hWmap] at h1
    rw [← h1, hWcard]
  · -- every element of the pull-back is an involution
    intro v hv
    rw [Subgroup.mem_map] at hv
    obtain ⟨y, hy, hyv⟩ := hv
    rw [Subgroup.mem_comap] at hy
    have hy2 : y ^ 2 = 1 := hf_inj (by rw [map_pow, hWsq (f y) hy, map_one])
    rw [← hyv]
    rw [← map_pow S.subtype y 2, hy2, map_one]

end Work.CORE4.L2PAux
