/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Finitely generated stabilizers under a change of group along a bijective homomorphism

Let a group `H` act on the vertex set `V` of a `G`-tree `T` through a bijective homomorphism
`π : H →* G`, the `H`-action being the one induced by `π` (this is the hypothesis `h`).
Then the pulled-back `H`-tree `T.pullback π h` again has finitely generated vertex and edge
stabilizers:

* the stabilizer of a vertex `v` in `H` is exactly `(T.vertexStab v).comap π` (the lemma
  `Lemmas.pullback_vertexStab`), and likewise for the stabilizer of an edge
  (`pullback_edgeStab_comap` below), because membership in a stabilizer is tested through
  `π` by `h`;
* the preimage of a finitely generated subgroup under a bijective homomorphism is finitely
  generated, since `π` restricts to an isomorphism `(K.comap π) ≃* K`
  (`Lemmas.subgroup_fg_comap_iff_of_bijective`).

This is the stabilizer half of the bookkeeping needed when a tree action of a group `G` is
transported to a group `H` acting on the same tree through an isomorphism `H ≃* G`; the
cocompactness half is `Lemmas.pullback_isCocompact`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Basic
import Submission.Work.ORDunwoody.Lemmas.pullback_vertexStab
import Submission.Work.ORDunwoody.Lemmas.subgroup_fg_comap_iff_of_bijective

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ORDunwoody.Lemmas

open Work.ORDunwoody

/-- The stabilizer of an edge of a tree pulled back along `π : H →* G` is the preimage of the
stabilizer of that edge in `G`. -/
theorem pullback_edgeStab_comap {G H : Type*} [Group G] [Group H] {V : Type*} [MulAction G V]
    [MulAction H V] (π : H →* G) (h : ∀ (a : H) (v : V), a • v = π a • v)
    (T : GTree G V) (u v : V) :
    (T.pullback π h).edgeStab u v = (T.edgeStab u v).comap π := by
  rw [GTree.edgeStab_eq, GTree.edgeStab_eq, pullback_vertexStab, pullback_vertexStab,
    ← Subgroup.comap_inf]

theorem pullback_hasFGStab_of_bijective {G H : Type*} [Group G] [Group H] {V : Type*}
    [MulAction G V] [MulAction H V] (π : H →* G) (hπ : Function.Bijective π)
    (h : ∀ (a : H) (v : V), a • v = π a • v) (T : GTree G V) (hT : T.HasFGStab) :
    (T.pullback π h).HasFGStab := by
  refine ⟨fun v => ?_, fun u v huv => ?_⟩
  · rw [pullback_vertexStab]
    exact (subgroup_fg_comap_iff_of_bijective π hπ _).2 (hT.1 v)
  · rw [pullback_edgeStab_comap]
    exact (subgroup_fg_comap_iff_of_bijective π hπ _).2 (hT.2 u v huv)

end Work.ORDunwoody.Lemmas
