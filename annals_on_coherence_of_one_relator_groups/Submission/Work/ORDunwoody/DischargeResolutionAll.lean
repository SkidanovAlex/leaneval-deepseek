/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# Discharging `DunwoodyResolutionAll`

`Hypotheses.lean` names the Dunwoody resolution (GL17 Proposition 2.17, constant case) as the
`Prop` `DunwoodyResolutionAll`, and every theorem of `Theorem44.lean`, `Theorem45.lean` and
`Corollaries.lean` carries it as a hypothesis.  This file discharges it with the theorem
`dunwoodyResolution` (`Submission/Work/ORDunwoody/dunwoodyResolution.lean`), so that JL
Theorems 4.4 and 4.5 hold with Bieri–Strebel (node N11) as their only remaining input.

The main results are

* `dunwoodyResolutionAll_holds X : DunwoodyResolutionAll X`;
* `fp_of_FP2_of_tree'`: JL Theorem 4.5 with *only* `BieriStrebel k` as a hypothesis;
* `groupCoherent_of_tree'`: the second assertion of JL Theorem 4.5 with the same single input.
-/
import Submission.Work.ORDunwoody.dunwoodyResolution
import Submission.Work.ORDunwoody.Dunwoody.ResolutionAssembly
import Submission.Work.ORDunwoody.Reduced

set_option autoImplicit false

set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

/-- **The Dunwoody resolution for every group of the universe of the anchor `X`** (GL17
Proposition 2.17, constant case), discharged by `dunwoodyResolution`. -/
theorem dunwoodyResolutionAll_holds (X : Type u) : DunwoodyResolutionAll X := by
  intro G _ V _ T hf hc
  exact dunwoodyResolution G T hf hc

/-- **JL Theorem 4.5, with the Dunwoody resolution discharged.**  The only remaining input is
Bieri–Strebel (JL Lemma 4.3, node N11). -/
theorem fp_of_FP2_of_tree' {k : Type u} [CommRing k] [Nontrivial k] {G : Type u} [Group G]
    {V : Type u} [MulAction G V] (T : GTree G V)
    (hT : ∀ v : V, Group.Coherent (T.vertexStab v))
    (hBS : BieriStrebel k) (H : Subgroup G) (hH : IsFP2 k H) :
    Group.IsFinitelyPresented H :=
  fp_of_FP2_of_tree_of_bieri_dunwoody T hT hBS (dunwoodyResolutionAll_holds G) H hH

/-- The second assertion of JL Theorem 4.5, with the Dunwoody resolution discharged. -/
theorem groupCoherent_of_tree' {k : Type u} [CommRing k] [Nontrivial k] {G : Type u} [Group G]
    {V : Type u} [MulAction G V] (T : GTree G V)
    (hT : ∀ v : V, Group.Coherent (T.vertexStab v))
    (hBS : BieriStrebel k) (hall : HomologicallyCoherent k G) : Group.Coherent G :=
  fun H hH => fp_of_FP2_of_tree' T hT hBS H (hall H hH)

/-- JL Theorem 4.4, with the Dunwoody resolution discharged. -/
theorem theorem_4_4' {k : Type u} [CommRing k] [Nontrivial k] {G : Type u} [Group G]
    {V : Type u} [MulAction G V] (hBS : BieriStrebel k)
    (T : GTree G V) (hT : T.IsCocompact) (hfp2 : IsFP2 k G) :
    ∃ (W : Type u) (_ : MulAction G W) (S : GTree G W),
      S.IsCocompact ∧ S.HasFGStab ∧ Dominates S T :=
  theorem_4_4_of_bieri_dunwoody hBS (dunwoodyResolutionAll_holds G) T hT hfp2

end Work.ORDunwoody
