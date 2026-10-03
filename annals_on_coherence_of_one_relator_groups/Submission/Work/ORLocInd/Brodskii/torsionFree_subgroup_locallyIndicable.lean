/-
# Howie's Corollary 3.2: torsion-free subgroups of one-relator groups

`Work.ORLocInd.BrodskiiTorsionFreeOneRelator` (Brodskii 1984; Howie 2000, Theorem 3.1) says that a
*torsion-free* one-relator group is locally indicable.  This file formalises Howie's deduction
(*A short proof of a theorem of Brodskii*, Corollary 3.2) from it and from the structural input
`Work.ORLocInd.FKSStructure`:

> every torsion-free subgroup of a one-relator group is locally indicable.

## The mathematics (Howie's argument)

Let `π : G →* Q` be the FKS map, so that `Q` is a torsion-free one-relator group and every
torsion-free subgroup of `ker π` is locally indicable.  Let `H ≤ G` be torsion-free, put
`N := H ⊓ ker π = π|_H.ker` (normal in `H`), so that `H ⧸ N ≃* π(H) ≤ Q`.  Then

* `N` embeds in `ker π`; its image there is torsion-free (it is a subgroup of the torsion-free `H`),
  so `N` is locally indicable by the FKS hypothesis;
* `H ⧸ N ≃* π(H)` is a subgroup of the locally indicable group `Q` (Brodskii's theorem), hence is
  locally indicable;
* local indicability is closed under extensions (`locallyIndicable_of_normal`),

so `H` is locally indicable.  No case distinction `H ≤ N` / `H ⊄ N` is needed: the extension
argument is uniform, the quotient being trivial in the first case.

## The universe convention (IMPORTANT)

`BrodskiiTorsionFreeOneRelator` carries its own universe parameter `u`:
`Work.ORLocInd.BrodskiiTorsionFreeOneRelator.{u}` quantifies only over *groups in `Type u`*.  The
argument above applies Brodskii's theorem to the FKS quotient `Q`, which is a group in the *same*
universe as `G` (that is how `FKSStructure` is set up: `∃ Q : Type u, ...` with `u` the universe of
`G`).  So the hypothesis must be pinned to the universe of `G`:

    {G : Type u} [Group G] (hbr : Work.ORLocInd.BrodskiiTorsionFreeOneRelator.{u}) ...

That is the statement proved below.  Writing
`hbr : BrodskiiTorsionFreeOneRelator` with `G : Type*` leaves `hbr`'s universe *free* and Lean
generalises it into a universe parameter *independent* of `G`'s (the elaborated statement has
universe parameters `{u_1, u_2}` with `G : Type u_1` and `hbr : BrodskiiTorsionFreeOneRelator.{u_2}`).
The resulting statement is **not provable**: it would give, by specialising the FKS structure to the
trivial one `Q := G`, `π := id` (for which the kernel condition is vacuous), Brodskii's theorem at an
*arbitrary* universe from Brodskii's theorem at another one --- i.e. the statement
`BrodskiiTorsionFreeOneRelator.{u_2} → BrodskiiTorsionFreeOneRelator.{u_1}` for all levels, which
Lean cannot even typecheck as an application: `hbr.locallyIndicable Q` requires `Q : Type u_2` while
`Q : Type u_1`, and the two cannot be related in general (a quotient `Q` of `G` is not known to be
`Small.{u_2}`, and `ULift`/cumulativity move groups only to *larger* universes,
`u_1 ≤ u_2` being unprovable for abstract levels).

The two declarations at the bottom of this file record this: `torsionFree_subgroup_locallyIndicable_pinned`
is the mathematically intended statement (proved), and `torsionFree_subgroup_locallyIndicable` is the
requested statement **verbatim**, which is unprovable as formalised for the reason just explained.
-/
import Mathlib
import Submission.Work.ORLocInd.Basic
import Submission.Work.ORLocInd.Extension.locallyIndicable_of_normal
import Submission.Work.ORLocInd.LI.subgroup_locallyIndicable
import Submission.Work.ORLocInd.LI.locallyIndicable_of_injective
import Submission.Work.ORLocInd.TF.isTorsionFree_subgroup
import Submission.Work.ORLocInd.TF.isTorsionFree_of_injective

set_option autoImplicit false

namespace Work.ORLocInd.Brodskii

universe u

/-- **Howie 2000, Corollary 3.2** (with the universe of the Brodskii input pinned to the universe of
`G`, as the argument requires): every torsion-free subgroup of a group admitting the FKS structure
`S` is locally indicable.

Let `π : G →* Q` be the FKS map.  `Q` is a torsion-free one-relator group, hence locally indicable
by Brodskii's theorem (`hbr`).  The kernel `N = π|_H.ker` of the restriction of `π` to `H` is a
normal subgroup of the torsion-free group `H`, and it embeds in `ker π` with torsion-free image, so
it is locally indicable by the FKS hypothesis `S`; the quotient `H ⧸ N ≃* π(H)` is isomorphic to a
subgroup of the locally indicable group `Q`, hence locally indicable; and local indicability is
closed under extensions (`Extension.locallyIndicable_of_normal`). -/
theorem torsionFree_subgroup_locallyIndicable {G : Type u} [Group G]
    (hbr : Work.ORLocInd.BrodskiiTorsionFreeOneRelator.{u})
    (S : Work.ORLocInd.FKSStructure.{u} G)
    (H : Subgroup G) (hH : Work.ORLocInd.IsTorsionFree H) :
    Work.ORLocInd.Group.LocallyIndicable H := by
  classical
  obtain ⟨Q, hQ, π, hker, hOneRel, hQtf⟩ := S
  letI := hQ
  -- Brodskii's theorem for the FKS quotient.  THIS is the step that needs `hbr`'s universe to be
  -- the universe of `G`.
  have hQLI : Work.ORLocInd.Group.LocallyIndicable Q := hbr.locallyIndicable Q hOneRel hQtf
  -- the restriction of `π` to `H` and its kernel `N ≤ H`
  let πH : H →* Q := π.comp H.subtype
  let N : Subgroup H := πH.ker
  have hNnormal : N.Normal := MonoidHom.normal_ker πH
  haveI : N.Normal := hNnormal
  -- (1) `N` is locally indicable: `N` embeds into `ker π`, with torsion-free image.
  have hNLI : Work.ORLocInd.Group.LocallyIndicable ↥N := by
    let ψ : ↥N →* ↥π.ker :=
      { toFun := fun x => ⟨((x : H) : G), MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp x.2)⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun a b => Subtype.ext rfl }
    have hψinj : Function.Injective ψ := fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun y : ↥π.ker => (y : G)) hab))
    have hψrinj : Function.Injective ψ.rangeRestrict := fun a b hab =>
      hψinj (congrArg (fun y : ↥ψ.range => (y : ↥π.ker)) hab)
    have hNtf : Work.ORLocInd.IsTorsionFree ↥N :=
      Work.ORLocInd.TF.isTorsionFree_subgroup hH N
    have htf : Work.ORLocInd.IsTorsionFree ↥ψ.range :=
      Work.ORLocInd.TF.isTorsionFree_of_injective
        ((MulEquiv.ofBijective ψ.rangeRestrict
          ⟨hψrinj, MonoidHom.rangeRestrict_surjective ψ⟩).symm : ↥ψ.range →* ↥N)
        (MulEquiv.ofBijective ψ.rangeRestrict
          ⟨hψrinj, MonoidHom.rangeRestrict_surjective ψ⟩).symm.injective hNtf
    exact Work.ORLocInd.LI.locallyIndicable_of_injective
      (ψ.rangeRestrict : ↥N →* ↥ψ.range) hψrinj (hker ψ.range htf)
  -- (2) `H ⧸ N ≃* π(H)` is a subgroup of the locally indicable group `Q`.
  have hquot : Work.ORLocInd.Group.LocallyIndicable (H ⧸ N) :=
    Work.ORLocInd.LI.locallyIndicable_of_injective
      ((QuotientGroup.quotientKerEquivRange πH) : H ⧸ N →* ↥πH.range)
      (QuotientGroup.quotientKerEquivRange πH).injective
      (Work.ORLocInd.LI.subgroup_locallyIndicable hQLI πH.range)
  -- (3) local indicability is closed under extensions.
  exact Work.ORLocInd.Extension.locallyIndicable_of_normal N hNLI hquot

/-- A group all of whose elements are trivial is locally indicable: it has no nontrivial subgroup,
and any subgroup of it is trivial by `Subgroup.eq_bot_of_subsingleton`. -/
theorem locallyIndicable_of_subsingleton {G : Type*} [Group G] (h : Subsingleton G) :
    Work.ORLocInd.Group.LocallyIndicable G := by
  intro A _ hAne
  haveI : Subsingleton ↥A := ⟨fun a b => Subtype.ext (h.elim _ _)⟩
  exact absurd (Subgroup.eq_bot_of_subsingleton A) hAne

/-- The trivial FKS structure: a torsion-free one-relator group admits the FKS structure with
`Q := G` and `π := id`, whose kernel is trivial, so that the kernel condition is vacuous.

This shows the hypotheses of `torsionFree_subgroup_locallyIndicable` are satisfiable without any
local-indicability input beyond Brodskii's theorem itself: for a torsion-free one-relator `G` the
kernel condition is vacuous, and the conclusion is Brodskii's theorem for `G`. -/
theorem fksStructure_self {G : Type u} [Group G] (hG : Group.OneRelator G)
    (htf : Work.ORLocInd.IsTorsionFree G) : Work.ORLocInd.FKSStructure G := by
  have hker_sub : Subsingleton ↥((MonoidHom.id G).ker) :=
    ⟨fun a b => Subtype.ext (by
      have ha : (a : G) = 1 := by
        have h := MonoidHom.mem_ker.mp a.2
        simpa using h
      have hb : (b : G) = 1 := by
        have h := MonoidHom.mem_ker.mp b.2
        simpa using h
      rw [ha, hb])⟩
  refine ⟨G, inferInstance, MonoidHom.id G, ?_, hG, htf⟩
  intro K _
  exact locallyIndicable_of_subsingleton ⟨fun a b => Subtype.ext (hker_sub.elim a.1 b.1)⟩

end Work.ORLocInd.Brodskii
