import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.RED.DihedralSubgroup

/-!
# CORE2A: `DihOrCycSylow` is inherited by subgroups

If every Sylow 2-subgroup of a finite group `G` is cyclic or dihedral, then the same holds
for every subgroup `K ≤ G`.

The argument is the classical one.  A Sylow 2-subgroup `Q` of `K`, viewed inside `G` via
`K.subtype`, is a 2-subgroup `QG ≤ G`, hence lies in some Sylow 2-subgroup `P` of `G`.

* If `P` is cyclic, then so is every subgroup of it, in particular `QG`, and `Q ≃* QG`
  because `K.subtype` is injective; a group isomorphic to a cyclic group is cyclic.
* If `P ≅ DihedralGroup n`, push `Q` through this isomorphism; its image is a subgroup of
  `DihedralGroup n`, and by the (verified) lemma `Work.RED.DihedralSubgroup` every subgroup
  of a finite dihedral group is cyclic or dihedral again.  Transporting back along the
  two isomorphisms finishes.

Only the mathematical input "subgroups of dihedral groups are cyclic or dihedral" is taken
from the dihedral library (`Submission.Work.RED.DihedralSubgroup`); the transfer to the
ambient group is proved here.

The statement is phrased with `Work.GW2.DihOrCycSylow` (`Submission.Work.ASM.Defs`), the
canonical vocabulary of the project.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

/-- A finite dihedral group has nonzero parameter: `DihedralGroup 0` is infinite. -/
theorem neZero_of_finite_dihedral {n : ℕ} (h : Finite (DihedralGroup n)) : NeZero n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn] at h
    exact absurd h (not_finite_iff_infinite.mpr (inferInstance : Infinite (DihedralGroup 0)))
  · exact ⟨hn.ne'⟩

/-- The transfer step: if every subgroup of every finite dihedral group is cyclic or
dihedral (`hsub`), then `DihOrCycSylow` is inherited by subgroups. -/
theorem dihOrCycSylow_subgroup_of_dihedralSubgroup
    (hsub : ∀ (n : ℕ) [NeZero n] (H : Subgroup (DihedralGroup n)),
      IsCyclic ↥H ∨ ∃ m : ℕ, Nonempty (↥H ≃* DihedralGroup m))
    {G : Type} [Group G] [Finite G] (K : Subgroup G) (h : Work.GW2.DihOrCycSylow G) :
    Work.GW2.DihOrCycSylow ↥K := by
  intro Q
  -- `Q` viewed inside `G`, together with the isomorphism `↥Q ≃* ↥QG`.
  let QG : Subgroup G := (Q : Subgroup ↥K).map K.subtype
  have heQ : ↥(Q : Subgroup ↥K) ≃* ↥QG :=
    Subgroup.equivMapOfInjective (Q : Subgroup ↥K) K.subtype K.subtype_injective
  -- `QG` is a 2-subgroup of `G`, so it lies in a Sylow 2-subgroup `P` of `G`.
  have hQp : IsPGroup 2 ↥QG := (Q.isPGroup').of_equiv heQ
  obtain ⟨P, hPle⟩ := hQp.exists_le_sylow
  rcases h P with hcyc | ⟨n, ⟨e⟩⟩
  · -- `P` is cyclic, hence so is `QG`, and `Q ≃* QG`.
    left
    haveI : IsCyclic ↥(P : Subgroup G) := hcyc
    exact (MulEquiv.isCyclic heQ).mpr (isCyclic_of_le hPle)
  · -- `P ≅ DihedralGroup n`; push `Q` into `DihedralGroup n` and use `hsub`.
    haveI : NeZero n :=
      neZero_of_finite_dihedral
        (Finite.of_injective (e.symm : DihedralGroup n → ↥(P : Subgroup G)) e.symm.injective)
    let Q'' : Subgroup ↥(P : Subgroup G) := QG.subgroupOf (P : Subgroup G)
    let H' : Subgroup (DihedralGroup n) := Q''.map e.toMonoidHom
    have h1 : ↥Q'' ≃* ↥QG := Subgroup.subgroupOfEquivOfLe hPle
    have h2 : ↥Q'' ≃* ↥H' := Subgroup.equivMapOfInjective Q'' e.toMonoidHom e.injective
    rcases hsub n H' with hcyc' | ⟨m, ⟨em⟩⟩
    · left
      have hcycQ'' : IsCyclic ↥Q'' := (MulEquiv.isCyclic h2).mpr hcyc'
      have hcycQG : IsCyclic ↥QG := (MulEquiv.isCyclic h1).mp hcycQ''
      exact (MulEquiv.isCyclic heQ).mpr hcycQG
    · right
      exact ⟨m, ⟨heQ.trans (h1.symm.trans (h2.trans em))⟩⟩

theorem dihOrCycSylow_subgroup {G : Type} [Group G] [Finite G] (h : Work.GW2.DihOrCycSylow G)
    (K : Subgroup G) : Work.GW2.DihOrCycSylow ↥K :=
  dihOrCycSylow_subgroup_of_dihedralSubgroup
    (fun n _ H => Work.RED.DihedralSubgroup n H) K h

end Work.CORE2A
