import Mathlib
import Submission.Work.RatHurewicz.Cofibre.path_compress_twoSet
import Submission.Work.RatHurewicz.finiteGraphDefs
import Submission.Work.RatHurewicz.finiteGraphGen

namespace Work.RatHurewicz

/-- **The fundamental group of a finite graph is finitely generated.**

`E` = the edges, `V` = the vertices (both finite, discrete), `a e` and `b e` the endpoints of the
edge `e`.  The graph `G` is the quotient of `V ⊕ (E × I)` by the identifications
`(e,0) ~ a e` and `(e,1) ~ b e` (all four directions listed below), with basepoint the image of
`v₀`.  Claim: `π₁(G, v₀)` is finitely generated.

Intended proof: the edge-path theorem — every path in `G` is homotopic relative to its endpoints to
a finite concatenation of edge-paths — after which the loops `(tree path) ++ e ++ (tree path)`
generate.  Available tools: `Work.RatHurewicz.Cofibre.path_compress_twoSet` (van Kampen
surjectivity in path form), Mathlib's `Path` / `Path.Homotopic` API and Lebesgue-number lemmas.
The module must be importable together with `Submission.Work.StemsB.PiMap` and
`Submission.Work.EmbeddedSpheres.Hurewicz.Face`; avoid `Submission.Work.Cohomology.prodSphereAux`
and `Submission.Work.EmbeddedSpheres.Hurewicz.Relation` (they declare `homologyBiprodIso` twice,
clashing with `Cohomology.CompatTrans.prodSphereAux`). -/
theorem finiteGraphPiFg (E V : Type) [Fintype E] [Fintype V]
    [TopologicalSpace E] [DiscreteTopology E] [TopologicalSpace V] [DiscreteTopology V]
    (a b : E → V) (v₀ : V) :
    Group.FG (HomotopyGroup (Fin 1)
      (Quotient (Relation.EqvGen.setoid fun p q : V ⊕ (E × unitInterval) =>
        (∃ e : E, p = Sum.inl (a e) ∧ q = Sum.inr (e, 0))
        ∨ (∃ e : E, p = Sum.inl (b e) ∧ q = Sum.inr (e, 1))
        ∨ (∃ e : E, p = Sum.inr (e, 0) ∧ q = Sum.inl (a e))
        ∨ (∃ e : E, p = Sum.inr (e, 1) ∧ q = Sum.inl (b e))))
      (Quotient.mk'' (Sum.inl v₀))) := by
  -- the fundamental group at the basepoint is finitely generated
  have h1 : Group.FG (FundamentalGroup (GraphX a b) (gq a b (Sum.inl v₀))) :=
    FinGraph.genSub_fg a b v₀
  -- transfer to the Hurewicz group π₁
  have h2 : Group.FG (HomotopyGroup (Fin 1) (GraphX a b) (gq a b (Sum.inl v₀))) := by
    refine Group.fg_of_surjective
      (f := (HomotopyGroup.pi1MulEquivFundamentalGroup (X := GraphX a b)
        (x := gq a b (Sum.inl v₀))).symm.toMonoidHom)
      (EquivLike.surjective (HomotopyGroup.pi1MulEquivFundamentalGroup (X := GraphX a b)
        (x := gq a b (Sum.inl v₀))).symm)
  -- the two presentations of the graph agree definitionally
  exact h2

end Work.RatHurewicz
