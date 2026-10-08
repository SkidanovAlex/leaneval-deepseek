import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.NineQuasisimpleSylowNotCyclic
import Submission.Work.RED.DihedralFacts
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic

namespace Work.CORE4

open Subgroup

set_option linter.style.haveILetI false

/- Declare inside `namespace Work.CORE4`; keep the imports listed in depends_on.
   WARNING: do NOT import Submission.Work.ASM.Defs or any other module that declares its own
   copy of `namespace Work.GW2` (e.g. Submission.Work.CORE2A.*, Submission.Work.CORE2B.*):
   CORE4's `Submission.Work.CORE4.Defs` is the owner of `Work.GW2` here and the copies clash. -/

/-- A Klein four-group is carried to a Klein four-group by an injective homomorphism. -/
private theorem isFourGroup_map_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {V : Subgroup G} (h : Work.GW2.IsFourGroup V) :
    Work.GW2.IsFourGroup (V.map f) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hf, h.1]
  · rintro w ⟨v, hv, rfl⟩
    rw [← map_pow, h.2 v hv, map_one]

/-- **`E(K) ≠ 1` means `K` contains a Klein four-group.**  A nontrivial layer of a finite group
`K` whose Sylow `2`-subgroups are cyclic or dihedral contains a subgroup of type `(2,2)`.

Indeed `layer K ≠ ⊥` exhibits a normal quasisimple `E ≤ K`; a Sylow `2`-subgroup `P` of `↥E` is
not cyclic (`NineQuasisimpleSylowNotCyclic`) but is cyclic or dihedral (`DihOrCycSub`), hence is
isomorphic to `DihedralGroup n` with `n` even
(`even_dihedral_param_of_isPGroup_two_not_isCyclic`); an even dihedral group contains a Klein
four-group (`DihedralFacts.fourGroup_exists_of_even`), which pulls back into `E ≤ layer K`. -/
theorem exists_fourGroup_le_layer {K : Type} [Group K] [Finite K]
    (hsy : Work.GW2.DihOrCycSylow K) (hne : Work.GW2.layer K ≠ ⊥) :
    ∃ V : Subgroup K, V ≤ Work.GW2.layer K ∧ Work.GW2.IsFourGroup V := by
  -- `layer K ≠ ⊥` exhibits a normal quasisimple subgroup `E ≤ K`
  obtain ⟨E, hEnorm, hEq⟩ : ∃ E : Subgroup K, E.Normal ∧ Work.GW2.IsQuasisimple E := by
    by_contra hcon
    apply hne
    rw [Work.GW2.layer]
    exact le_antisymm (sSup_le fun F hF => absurd ⟨F, hF.1, hF.2⟩ hcon) bot_le
  have hEle : E ≤ Work.GW2.layer K := le_sSup ⟨hEnorm, hEq⟩
  -- a Sylow `2`-subgroup of `↥E`
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := ↥E)
  -- it is not cyclic, since `E` is quasisimple
  have hnc : ¬ IsCyclic ↥(P : Subgroup ↥E) := NineQuasisimpleSylowNotCyclic hEq P
  -- but it is cyclic or dihedral, being a subgroup of a D-group
  rcases DihOrCycSub hsy E P with hcyc | ⟨n, ⟨e⟩⟩
  · exact absurd hcyc hnc
  -- a non-cyclic dihedral `2`-group is `DihedralGroup n` with `n` even
  obtain ⟨heven, hnez⟩ :=
    Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic e P.isPGroup' hnc
  haveI : NeZero n := hnez
  obtain ⟨W, hW⟩ := Work.RED.DihedralFacts.fourGroup_exists_of_even n heven
  -- push the four-group of `DihedralGroup n` into `K` along `DihedralGroup n ≃* ↥P ↪ ↥E ↪ K`
  let ψ : DihedralGroup n →* K :=
    E.subtype.comp ((P : Subgroup ↥E).subtype.comp e.symm.toMonoidHom)
  have hψ : Function.Injective ψ :=
    E.subtype_injective.comp ((Subgroup.subtype_injective _).comp e.symm.injective)
  refine ⟨W.map ψ, ?_, ?_⟩
  · rintro v ⟨w, -, rfl⟩
    exact hEle (SetLike.coe_mem (e.symm w : ↥E))
  · exact isFourGroup_map_of_injective ψ hψ hW

end Work.CORE4
