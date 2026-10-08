import Mathlib
import Submission.Work.RED.Basic
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic
import Submission.Work.RED.isSolvable_of_forall_sylow_two_isCyclic

/-!
# RED: a non-solvable group with dihedral-or-cyclic Sylow 2-subgroups and trivial `O(G)`
contains a Klein four-group

`Work.RED.exists_fourGroup_of_dihOrCyc_nonsolvable`: if the Sylow 2-subgroups of the finite
group `N` are cyclic or dihedral, `O(N) = 1`, and `N` is not solvable, then `N` contains a
Klein four-group.

Proof.  If every Sylow 2-subgroup is cyclic then `N` is solvable
(`Work.RED.isSolvable_of_forall_sylow_two_isCyclic`), contradicting `hsol`.  Otherwise some
Sylow 2-subgroup `P` is non-cyclic, hence (by `DihOrCycSylow`) isomorphic to `DihedralGroup n`
for some `n`; `P` being a non-cyclic 2-group forces `n` to be a nonzero even number
(`Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic`), and `DihedralGroup n` for even
`n` contains a Klein four-group (`DihedralFactsProp.fourGroup_exists_of_even`), which we pull
back to `N` along `P ≃* DihedralGroup n` and `P ↪ N`.
-/

namespace Work.RED

open Subgroup

/-- A Klein four-group is preserved by pushing a subgroup forward along an injective
homomorphism. -/
theorem isFourGroup_map_of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {V : Subgroup G} (h : Work.RED.GW2.IsFourGroup V) :
    Work.RED.GW2.IsFourGroup (V.map f) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hf, h.1]
  · intro x hx
    obtain ⟨v, hv, rfl⟩ := hx
    rw [← map_pow, h.2 v hv, map_one]

theorem exists_fourGroup_of_dihOrCyc_nonsolvable
    (hdi : Work.RED.GW2.DihedralFactsProp)
    (hcsq : ∀ (G : Type*) [Group G] [Finite G] (P : Sylow 2 G),
      IsCyclic ↥(P : Subgroup G) → IsPGroup 2 (G ⧸ Work.RED.GW2.oddCore G))
    {N : Type*} [Group N] [Finite N] (h : Work.RED.GW2.DihOrCycSylow N)
    (hO : Work.RED.GW2.oddCore N = ⊥) (hsol : ¬ Group.IsSolvable N) :
    ∃ V : Subgroup N, Work.RED.GW2.IsFourGroup V := by
  by_cases hcyc : ∀ P : Sylow 2 N, IsCyclic ↥(P : Subgroup N)
  · exact absurd (isSolvable_of_forall_sylow_two_isCyclic hO hcyc) hsol
  · rw [Classical.not_forall] at hcyc
    obtain ⟨P, hPnc⟩ := hcyc
    rcases h P with hPcyc | ⟨n, ⟨e⟩⟩
    · exact absurd hPcyc hPnc
    · obtain ⟨heven, hne⟩ :=
        even_dihedral_param_of_isPGroup_two_not_isCyclic e P.isPGroup' hPnc
      haveI : NeZero n := hne
      obtain ⟨V, hV⟩ := hdi.fourGroup_exists_of_even n heven
      refine ⟨V.map (((P : Subgroup N).subtype).comp e.symm.toMonoidHom), ?_⟩
      refine isFourGroup_map_of_injective _ (fun x y hxy => ?_) hV
      exact e.symm.injective (Subtype.coe_injective (by simpa using hxy))

end Work.RED
