/-
Area CORE4 of the Gorenstein–Walter project.

# `O_p` is transported by a group isomorphism

`Work.GW2.pCore p L = (sSup {N : Subgroup L | N.Normal ∧ IsPGroup p N}).normalCore` is the largest
normal `p`-subgroup (`p`-core) `O_p(L)`, and
`Work.GW2.pCoreIn p K = (pCore p ↥K).map K.subtype` is the same subgroup of the ambient group.

The main result of this file, `Work.CORE4.PcoreInMapMulEquiv`, is that an isomorphism `φ : G ≃* H`
carries `O_p(K)` to `O_p(K.map φ)`:

    `pCoreIn p (K.map φ) = (pCoreIn p K).map φ`.

The proof is a two-line reduction to the corresponding statement for the `p`-core of a group.

The ingredients, all proved here in the general (not necessarily finite) setting, are:

* `le_pCore_of_normal_isPGroup` — the *universal property* of the `p`-core: every normal
  `p`-subgroup `N ≤ L` lies in `O_p(L)`.  This is `N ≤ sSup … ≤ (sSup …).normalCore`
  (`le_sSup` and `Subgroup.normal_le_normalCore`);
* `isPGroup_sSup_normal_isPGroup` / `pCore_isPGroup` — `O_p(L)` is a `p`-group, because the join
  of the normal `p`-subgroups is one (`Sylow.sSup_of_normal`) and subgroups of `p`-groups are
  `p`-groups (`IsPGroup.to_le`, via `Subgroup.normalCore_le`);
* `pCore_map_mulEquiv` — the `p`-core is transported by an isomorphism, by the universal property
  applied to `O_p(L)` and to its image under `ψ.symm`.

The subgroup-core `O_p(↥K)` is then compared with `O_p(↥(K.map φ))` along the isomorphism
`Subgroup.equivMapOfInjective K φ.toMonoidHom φ.injective`; the two subtype maps
`↥K →* H` agree (`Subgroup.coe_equivMapOfInjective_apply`), and `Subgroup.map_map` rewrites
the composite into the two sides of the goal.
-/
import Mathlib
import Submission.Work.CORE4.Defs

namespace Work.CORE4

open Subgroup

/-- The join of the normal `p`-subgroups of a group is a `p`-group. -/
theorem isPGroup_sSup_normal_isPGroup {L : Type*} [Group L] (p : ℕ) :
    IsPGroup p ↥(sSup {N : Subgroup L | N.Normal ∧ IsPGroup p N}) :=
  Sylow.sSup_of_normal _ (fun _ hN => hN.2) (fun _ hN => hN.1)

/-- **Universal property of the `p`-core.**  Every normal `p`-subgroup of `L` is contained in
`O_p(L)`.  No finiteness and no primality of `p` are needed. -/
theorem le_pCore_of_normal_isPGroup {L : Type*} [Group L] {p : ℕ} {N : Subgroup L}
    (hN : N.Normal) (hp : IsPGroup p N) : N ≤ Work.GW2.pCore p L :=
  (Subgroup.normal_le_normalCore (N := N)
    (H := sSup {M : Subgroup L | M.Normal ∧ IsPGroup p M}) (hN := hN)).mpr
    (le_sSup (show N ∈ {M : Subgroup L | M.Normal ∧ IsPGroup p M} from ⟨hN, hp⟩))

/-- `O_p(L)` is a `p`-group. -/
theorem pCore_isPGroup {L : Type*} [Group L] (p : ℕ) :
    IsPGroup p ↥(Work.GW2.pCore p L) := by
  rw [Work.GW2.pCore]
  exact (isPGroup_sSup_normal_isPGroup (L := L) p).to_le (Subgroup.normalCore_le _)

/-- The `p`-core is transported by a group isomorphism: an isomorphism carries the largest normal
`p`-subgroup to the largest normal `p`-subgroup. -/
theorem pCore_map_mulEquiv {L L' : Type*} [Group L] [Group L'] (e : L ≃* L') (p : ℕ) :
    (Work.GW2.pCore p L).map e.toMonoidHom = Work.GW2.pCore p L' := by
  refine le_antisymm ?_ ?_
  · -- the image of `O_p(L)` is a normal `p`-subgroup of `L'`
    exact le_pCore_of_normal_isPGroup
      ((Work.GW2.pCore_normal p L).map e.toMonoidHom e.surjective)
      (IsPGroup.map (pCore_isPGroup (L := L) p) e.toMonoidHom)
  · -- apply the previous inclusion to `e.symm` and push forward along `e`
    have h := le_pCore_of_normal_isPGroup
      (N := (Work.GW2.pCore p L').map e.symm.toMonoidHom)
      ((Work.GW2.pCore_normal p L').map e.symm.toMonoidHom e.symm.surjective)
      (IsPGroup.map (pCore_isPGroup (L := L') p) e.symm.toMonoidHom)
    have h2 : ((Work.GW2.pCore p L').map e.symm.toMonoidHom).map e.toMonoidHom ≤
        (Work.GW2.pCore p L).map e.toMonoidHom :=
      Subgroup.map_mono (f := e.toMonoidHom) h
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id L' := by
      ext x; simp
    rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h2
    exact h2

theorem PcoreInMapMulEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (p : ℕ)
    (K : Subgroup G) :
    Work.GW2.pCoreIn p (K.map φ.toMonoidHom) = (Work.GW2.pCoreIn p K).map φ.toMonoidHom := by
  -- the isomorphism `↥K ≃* ↥(K.map φ)` induced by `φ`
  let e : ↥K ≃* ↥(K.map φ.toMonoidHom) :=
    Subgroup.equivMapOfInjective K φ.toMonoidHom φ.injective
  -- the two maps `↥K →* H` agree
  have key : (K.map φ.toMonoidHom).subtype.comp e.toMonoidHom =
      φ.toMonoidHom.comp K.subtype := by
    ext x
    exact Subgroup.coe_equivMapOfInjective_apply K φ.toMonoidHom φ.injective x
  unfold Work.GW2.pCoreIn
  rw [← pCore_map_mulEquiv e p, Subgroup.map_map, key, ← Subgroup.map_map]

end Work.CORE4
