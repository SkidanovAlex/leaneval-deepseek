/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# JL Theorem 4.5: `FP₂` plus a tree action with coherent vertex stabilizers implies
finite presentability

This is the statement that node N14 of the route design consumes: `fp_of_FP2_of_tree`.

Proof (JL, §4):  Let `H ≤ G` be a finitely generated subgroup of type `FP₂(k)`, where `G`
acts on a tree `T` whose vertex stabilizers are coherent.  Since `H` is finitely generated
there is a cocompact `H`-invariant subtree `S₀ ⊆ T` (the "cocompact invariant subtree" input,
proved in `Submission.Work.ORDunwoody.Lemmas.exists_cocompact_invariant_subtree` and recorded
here as `cocompactSubtree`).  By JL Theorem 4.4 (`theorem_4_4`) applied to the cocompact
`H`-tree `S₀`, there is a cocompact `H`-tree `S` with finitely generated vertex and edge
stabilizers dominating `S₀`, hence dominating `T` over the inclusion `H ↪ G`
(`DominationMapOver.vertexStab_map_le`).  Each vertex stabilizer of `S` is a finitely
generated subgroup of a vertex stabilizer of `G`, hence finitely presented because the
latter is coherent (`isFinitelyPresented_of_le_coherent`); edge stabilizers are finitely
generated as well.  The structure theorem for groups acting on trees
(`BassSerreFinitelyPresented`) then exhibits `H` as the fundamental group of a finite graph
of finitely presented groups, so `H` is finitely presented.
-/
import Submission.Work.ORDunwoody.Theorem44
import Submission.Work.ORDunwoody.Lemmas.fg_map
import Submission.Work.ORDunwoody.Lemmas.isFinitelyPresented_of_le_coherent
import Submission.Work.ORDunwoody.Lemmas.exists_cocompact_invariant_subtree

set_option autoImplicit false

set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

/-- If a group `H` acts cocompactly on a tree `S` with finitely generated vertex and edge
stabilizers, and the vertex stabilizers `S.vertexStab w` are contained in coherent subgroups
of an ambient group `G` (as witnessed by a domination map over `H ↪ G` into the `G`-tree
`T`), then `H` is finitely presented.  This is Theorem 4.5 with the resolution step removed;
it is the form in which the theorem applies to Bass–Serre trees that already have finitely
generated stabilizers (e.g. the base case of the Magnus–Moldavanskii induction). -/
theorem isFinitelyPresented_of_cocompact_domination {G : Type u} [Group G] {V : Type u}
    [MulAction G V] (T : GTree G V) (hcoh : ∀ v : V, Group.Coherent (T.vertexStab v))
    (H : Subgroup G) {W : Type u} [MulAction H W] (S : GTree H W)
    (hSS : BassSerreFinitelyPresented H S)
    (hSc : S.IsCocompact) (hSfg : S.HasFGStab) (hdom : DominatesOver H.subtype S T) :
    Group.IsFinitelyPresented H := by
  obtain ⟨f⟩ := hdom
  have hfin : ∀ w : W, Group.IsFinitelyPresented (S.vertexStab w) := by
    intro w
    have hle : (S.vertexStab w).map H.subtype ≤ T.vertexStab (f w) := f.vertexStab_map_le w
    have hfg : ((S.vertexStab w).map H.subtype).FG := Lemmas.fg_map H.subtype (hSfg.1 w)
    haveI : Group.IsFinitelyPresented ((S.vertexStab w).map H.subtype) :=
      Lemmas.isFinitelyPresented_of_le_coherent _ _ (hcoh (f w)) hfg hle
    exact Group.IsFinitelyPresented.equiv
      (Subgroup.equivMapOfInjective (S.vertexStab w) H.subtype Subtype.coe_injective).symm
  exact hSS hSc hSfg.2 hfin

/-- The "cocompact invariant subtree" input of JL §4: a finitely generated subgroup
`H ≤ G` acting on a tree `T` has a cocompact `H`-invariant subtree whose inclusion into `T`
is a domination map over `H ↪ G`.  This is *proved* (in
`Submission.Work.ORDunwoody.Lemmas.exists_cocompact_invariant_subtree`) and recorded here as
an inhabitant of the named input `CocompactSubtree`. -/
theorem cocompactSubtree {G : Type u} [Group G] {V : Type u} [MulAction G V]
    (T : GTree G V) : CocompactSubtree G T :=
  fun H hH => Lemmas.exists_cocompact_invariant_subtree T H hH

/-- JL Theorem 4.5 with the cocompact-subtree input as an explicit hypothesis — useful when
the invariant subtree is known concretely. -/
theorem fp_of_FP2_of_tree_of_hull {k : Type u} [CommRing k] [Nontrivial k] {G : Type u}
    [Group G] {V : Type u} [MulAction G V] (T : GTree G V)
    (hT : ∀ v : V, Group.Coherent (T.vertexStab v))
    (hBS : BieriStrebel k) (hDR : DunwoodyResolutionAll G)
    (hQ : QuotientTreeByNormalClosureOfElliptic k) (hFree : FreeOnTreeIsFree k)
    (hSub : CocompactSubtree G T) (hSS : BassSerreFinitelyPresentedAll G)
    (H : Subgroup G) (hH : IsFP2 k H) :
    Group.IsFinitelyPresented H := by
  -- `FP₂` implies finitely generated, by Bieri–Strebel.
  have hHfg : H.FG := by
    obtain ⟨H', instH', π, hπ, hH'fp, hker⟩ := (hBS H).mp hH
    letI : Group H' := instH'
    obtain ⟨n, φ, hφ, -⟩ := hH'fp.out
    haveI : Group.FG H' := Group.fg_of_surjective hφ
    exact (Group.fg_iff_subgroup_fg H).mp (Group.fg_of_surjective hπ)
  -- a cocompact `H`-invariant subtree of `T`
  obtain ⟨W, instW, S₀, hS₀c, hdom₀⟩ := hSub H hHfg
  letI : MulAction H W := instW
  -- JL Theorem 4.4 applied to the `H`-tree `S₀`
  obtain ⟨X, instX, S, hSc, hSfg, hdom⟩ :=
    theorem_4_4 (G := H) (V := W) hBS hDR hQ hFree S₀ hS₀c hH
  letI : MulAction H X := instX
  have hdom' : DominatesOver H.subtype S T := DominatesOver.trans_dominates hdom hdom₀
  exact isFinitelyPresented_of_cocompact_domination (G := G) (V := V) T hT
    (H := H) S (hSS H S) hSc hSfg hdom'

/-- **JL Theorem 4.5 (first assertion).**  Let `G` act on a tree `T` with coherent vertex
stabilizers.  If `H ≤ G` is of type `FP₂` over `k`, then `H` is finitely presented.

The remaining hypotheses are the deep inputs owned by the neighbouring nodes:
`BieriStrebel` (JL Lemma 4.3, node N11), `DunwoodyResolution` (GL17 Prop. 2.17, node N13),
`FP2TreePromotion` (the descent step in JL Theorem 4.4, nodes N12/N13) and
`BassSerreFinitelyPresented` (the structure theorem for groups acting on trees, node N12).
The cocompact-subtree input is not a hypothesis: it is `cocompactSubtree` above. -/
theorem fp_of_FP2_of_tree {k : Type u} [CommRing k] [Nontrivial k] {G : Type u} [Group G]
    {V : Type u} [MulAction G V] (T : GTree G V)
    (hT : ∀ v : V, Group.Coherent (T.vertexStab v))
    (hBS : BieriStrebel k) (hDR : DunwoodyResolutionAll G)
    (hQ : QuotientTreeByNormalClosureOfElliptic k) (hFree : FreeOnTreeIsFree k)
    (hSS : BassSerreFinitelyPresentedAll G)
    (H : Subgroup G) (hH : IsFP2 k H) :
    Group.IsFinitelyPresented H :=
  fp_of_FP2_of_tree_of_hull T hT hBS hDR hQ hFree (cocompactSubtree T) hSS H hH

end Work.ORDunwoody
