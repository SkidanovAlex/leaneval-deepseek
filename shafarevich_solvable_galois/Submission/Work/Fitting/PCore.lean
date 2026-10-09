/-
Copyright (c) 2025. All rights reserved.

# The `p`-core of a group

For a prime `p`, the `p`-core `O_p(G) = pCore p G` is the largest normal `p`-subgroup of `G`,
realised here as the supremum of all normal `p`-subgroups.  For a finite group this supremum is
itself a normal `p`-subgroup, and the Fitting subgroup is the join of the `p`-cores
(`fitting_eq_iSup_pCore` in `Submission/Work/Fitting/Join.lean`).

## Main results

* `pCore`, `le_pCore` : definition and universal property;
* `pCore_normal`, `pCore_isPGroup`, `pCore_nilpotent` : `O_p(G)` is a normal `p`-subgroup,
  hence nilpotent (for finite `G`);
* `pCore_le_fitting` : `O_p(G) ≤ F(G)`;
* `Subgroup.map_subtype_normal_of_characteristic` : a characteristic subgroup of a normal
  subgroup is normal.
-/
import Mathlib
import Submission.Work.Fitting.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Fitting

set_option linter.style.haveILetI false
open scoped Classical
open Subgroup

variable {G : Type*} [Group G]

/-- The `p`-core of a group: the supremum of all normal `p`-subgroups. -/
noncomputable def pCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  ⨆ (N : {N : Subgroup G // N.Normal ∧ IsPGroup p N}), (N : Subgroup G)

theorem pCore_def (p : ℕ) (G : Type*) [Group G] :
    pCore p G = ⨆ (N : {N : Subgroup G // N.Normal ∧ IsPGroup p N}), (N : Subgroup G) := rfl

/-- Every normal `p`-subgroup is contained in the `p`-core. -/
theorem le_pCore {p : ℕ} {N : Subgroup G} (hN : N.Normal) (hp : IsPGroup p N) :
    N ≤ pCore p G :=
  le_iSup (fun N : {N : Subgroup G // N.Normal ∧ IsPGroup p N} => (N : Subgroup G)) ⟨N, hN, hp⟩

theorem pCore_normal (p : ℕ) : (pCore p G).Normal := by
  haveI : ∀ N : {N : Subgroup G // N.Normal ∧ IsPGroup p N}, (N : Subgroup G).Normal :=
    fun N => N.2.1
  exact Subgroup.iSup_normal _

theorem pCore_isPGroup (p : ℕ) : IsPGroup p (pCore p G) := by
  haveI : ∀ N : {N : Subgroup G // N.Normal ∧ IsPGroup p N}, (N : Subgroup G).Normal :=
    fun N => N.2.1
  exact Sylow.iSup_of_normal _ fun N => N.2.2

theorem pCore_nilpotent [Finite G] (p : ℕ) [Fact p.Prime] : Group.IsNilpotent (pCore p G) :=
  IsPGroup.isNilpotent (pCore_isPGroup p)

theorem pCore_le_fitting [Finite G] (p : ℕ) [Fact p.Prime] : pCore p G ≤ fitting G :=
  le_fitting (pCore_normal p) (pCore_nilpotent p)

end Work.Fitting

namespace Subgroup

open scoped Classical

/-- A characteristic subgroup of a normal subgroup is normal. -/
theorem map_subtype_normal_of_characteristic {G : Type*} [Group G] {M : Subgroup G} [M.Normal]
    {H : Subgroup M} [hH : H.Characteristic] : (H.map M.subtype).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
  have hmem : MulAut.conjNormal g m ∈ H := by
    have hmap : H.map (MulAut.conjNormal g).toMonoidHom = H :=
      Subgroup.characteristic_iff_map_eq.mp hH (MulAut.conjNormal g)
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hm
  rw [Subgroup.mem_map]
  exact ⟨MulAut.conjNormal g m, hmem, by simpa using MulAut.conjNormal_apply g m⟩

end Subgroup
