import Mathlib
import Submission.Work.DSTR.quasisimpleSylow
import Submission.Work.CORE2A.dihOrCycSylow_subgroup
import Submission.Work.ASM.FT
import Submission.Work.RED.DihedralFacts
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic

/-!
# CORE2A: a quasisimple subgroup of a D-group contains a Klein four-group

Let `K` be a finite group whose Sylow 2-subgroups are cyclic or dihedral (a *D-group*), and
let `E ◁ K` be a **quasisimple** subgroup (perfect, with simple central quotient).

Quasisimple groups are perfect, hence not solvable, and a group with a cyclic Sylow
2-subgroup is solvable once one knows Feit--Thompson; this is
`Work.GW2.QuasisimpleSylowProp`, proved in `Submission.Work.DSTR.quasisimpleSylow` from the
ported odd-order theorem.  So **no** Sylow 2-subgroup of `E` is cyclic.  But `DihOrCycSylow K`
is inherited by the subgroup `E` (`Work.CORE2A.dihOrCycSylow_subgroup`), so every Sylow
2-subgroup of `E` is *dihedral*: `P ≅ DihedralGroup n`.

Since `P` is a non-cyclic 2-group, the parameter `n` is non-zero and even
(`Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic`), and an even dihedral group
contains a Klein four-subgroup (`Work.RED.DihedralFacts.fourGroup_exists_of_even`).  Pushing
that four-group forward along the composite

`DihedralGroup n ≃* P ↪ E ↪ K`

(an injective homomorphism) yields a Klein four-subgroup of `K` contained in `E`.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2A

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

theorem fourGroup_in_quasisimple {K : Type} [Group K] [Finite K] (E : Subgroup K)
    (hE : E.Normal) (hQ : Work.GW2.IsQuasisimple E) (hsy : Work.GW2.DihOrCycSylow K) :
    ∃ V : Subgroup K, V ≤ E ∧ Work.GW2.IsFourGroup V := by
  -- Feit--Thompson in the vocabulary of the development, to feed `QuasisimpleSylowProp`.
  have hFT : Work.GW2.FeitThompsonProp := Work.GW2.feitThompsonProp
  -- `DihOrCycSylow` passes to the subgroup `E`.
  have hsyE : Work.GW2.DihOrCycSylow ↥E := dihOrCycSylow_subgroup hsy E
  -- No Sylow 2-subgroup of a quasisimple group is cyclic.
  have hnotcyc : ∀ P : Sylow 2 ↥E, ¬ IsCyclic ↥(P : Subgroup ↥E) :=
    fun P => Work.DSTR.quasisimpleSylow K hFT E hQ P
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := ↥E)
  rcases hsyE P with hcyc | ⟨n, ⟨e⟩⟩
  · exact absurd hcyc (hnotcyc P)
  · -- `P ≅ DihedralGroup n` with `n` a nonzero even number.
    obtain ⟨heven, hne⟩ :=
      Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic e P.isPGroup' (hnotcyc P)
    haveI : NeZero n := hne
    obtain ⟨V₀, hV₀⟩ := Work.RED.DihedralFacts.fourGroup_exists_of_even n heven
    have hV₀' : Work.GW2.IsFourGroup V₀ := hV₀
    -- The injective composite `DihedralGroup n ≃* P ↪ E ↪ K`.
    let φ : DihedralGroup n →* K :=
      E.subtype.comp ((P : Subgroup ↥E).subtype.comp e.symm.toMonoidHom)
    have hφinj : Function.Injective φ :=
      E.subtype_injective.comp
        ((P : Subgroup ↥E).subtype_injective.comp e.symm.injective)
    refine ⟨Subgroup.map φ V₀, ?_, ?_⟩
    · -- The four-group lands inside `E`.
      change Subgroup.map (E.subtype.comp ((P : Subgroup ↥E).subtype.comp e.symm.toMonoidHom))
        V₀ ≤ E
      rw [← Subgroup.map_map]
      exact Subgroup.map_subtype_le _
    · exact isFourGroup_map_of_injective φ hφinj hV₀'

end Work.CORE2A
