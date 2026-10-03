/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# JL Theorems 4.4/4.5 with the Bass–Serre inputs discharged

`Hypotheses.lean` names the inputs of JL §4; `Interface.lean` proves all of them except the
Dunwoody resolution (`DunwoodyResolutionAll`, the statement of `dunwoodyResolution.lean`, this
node's own remaining obligation).  The theorems of `Corollaries.lean` nevertheless still carry
`QuotientTreeByNormalClosureOfElliptic`, `FreeOnTreeIsFree` and `BassSerreFinitelyPresentedAll`
as hypotheses, because they were written before the discharge existed.

This file removes them: `fp_of_FP2_of_tree_of_bieri_dunwoody` is JL Theorem 4.5 with exactly two
inputs left, Bieri–Strebel (node N11) and the Dunwoody resolution (node N13, this node).  A caller
that has those two can use the theorems here without ever mentioning the Bass–Serre vocabulary.
-/
import Submission.Work.ORDunwoody.Corollaries
import Submission.Work.ORDunwoody.Interface

set_option autoImplicit false

set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

/-- **JL Theorem 4.4 with the Bass–Serre inputs discharged.**  The only inputs left are
Bieri–Strebel (node N11) and the Dunwoody resolution (node N13). -/
theorem theorem_4_4_of_bieri_dunwoody {k : Type u} [CommRing k] [Nontrivial k] {G : Type u}
    [Group G] {V : Type u} [MulAction G V]
    (hBS : BieriStrebel k) (hDR : DunwoodyResolutionAll G)
    (T : GTree G V) (hT : T.IsCocompact) (hfp2 : IsFP2 k G) :
    ∃ (W : Type u) (_ : MulAction G W) (S : GTree G W),
      S.IsCocompact ∧ S.HasFGStab ∧ Dominates S T :=
  theorem_4_4 hBS hDR (quotientTreeByNormalClosureOfElliptic_holds k)
    (freeOnTreeIsFree_holds k) T hT hfp2

/-- **JL Theorem 4.5 with the Bass–Serre inputs discharged.**  The only inputs left are
Bieri–Strebel (node N11) and the Dunwoody resolution (node N13). -/
theorem fp_of_FP2_of_tree_of_bieri_dunwoody {k : Type u} [CommRing k] [Nontrivial k]
    {G : Type u} [Group G] {V : Type u} [MulAction G V] (T : GTree G V)
    (hT : ∀ v : V, Group.Coherent (T.vertexStab v))
    (hBS : BieriStrebel k) (hDR : DunwoodyResolutionAll G)
    (H : Subgroup G) (hH : IsFP2 k H) :
    Group.IsFinitelyPresented H :=
  fp_of_FP2_of_tree T hT hBS hDR (quotientTreeByNormalClosureOfElliptic_holds k)
    (freeOnTreeIsFree_holds k) (bassSerreFinitelyPresentedAll_holds G) H hH

/-- The second assertion of JL Theorem 4.5, with the Bass–Serre inputs discharged. -/
theorem groupCoherent_of_tree_of_bieri_dunwoody {k : Type u} [CommRing k] [Nontrivial k]
    {G : Type u} [Group G] {V : Type u} [MulAction G V] (T : GTree G V)
    (hT : ∀ v : V, Group.Coherent (T.vertexStab v))
    (hBS : BieriStrebel k) (hDR : DunwoodyResolutionAll G)
    (hall : HomologicallyCoherent k G) : Group.Coherent G :=
  fun H hH => fp_of_FP2_of_tree_of_bieri_dunwoody T hT hBS hDR H (hall H hH)

end Work.ORDunwoody
