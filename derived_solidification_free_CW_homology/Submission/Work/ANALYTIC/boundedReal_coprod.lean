import Mathlib
import Submission.Work.ANALYTIC.BoundedRealType
import Submission.Work.ANALYTIC.RealSideDefs

/-!
# `∏^bnd ℝ` on a finite coproduct of light profinite sets

`boundedRealTypePresheaf` (`Submission/Work/ANALYTIC/BoundedRealType.lean`) is the underlying
presheaf of *types* of the presheaf `boundedRealPresheaf`
(`Submission/Work/ANALYTIC/RealSideDefs.lean`): at a light profinite set `S` its value is the set
of uniformly bounded families `(x_n)` of continuous `ℝ`-valued functions on `S`.  It is the
`ℝ`-valued analogue of `boundedTypePresheaf` (`∏^bnd ℤ`).

This file shows that, for a *finite* family `X : α → LightProfinite`, restriction to the summands
gives a bijection

`boundedRealTypePresheaf (∐_a X a) ≅ ∏_a boundedRealTypePresheaf (X a)`,

i.e. the map that sends a bounded family on the explicit finite coproduct of the `X a` (whose
underlying space is the disjoint union `Σ a, X a`) to its family of restrictions along the
inclusions `finiteCoproduct.ι X a` is bijective.  Together with
`Work.ANALYTIC.boundedReal_preservesFiniteProducts` and
`Work.ANALYTIC.boundedReal_equalizerCondition` this is the statement that `∏^bnd ℝ` is a sheaf on
the coherent (resp. regular) topology of `LightProfinite`, hence a light condensed abelian group.

The proof is the `ℝ`-valued counterpart of `Work.ANALYTIC.boundedSeq_coprod`
(`Submission/Work/ANALYTIC/boundedSeq_coprod.lean`), and rests on the same two ingredients:

* injectivity: every point of `∐_a X a` lies in one of the summands, since it is a point `⟨a, s⟩`
  of the disjoint union;
* surjectivity: coordinates are glued along the (disjoint) union — a function on `Σ a, X a` is
  continuous iff its restriction to each summand is — and, crucially, the index set `α` is
  *finite*, so that the sum of the finitely many (nonnegative) bounds of the given families is
  again a bound.  Finiteness is essential here: for an infinite `α` the glued family need not be
  uniformly bounded.
-/

open CategoryTheory

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC

theorem boundedReal_coprod {α : Type} [Finite α] (X : α → LightProfinite) :
    Function.Bijective (fun x : Work.ANALYTIC.boundedRealTypePresheaf.obj (Opposite.op (CompHausLike.finiteCoproduct X)) =>
      fun a => Work.ANALYTIC.boundedRealTypePresheaf.map (CompHausLike.finiteCoproduct.ι X a).op x) := by
  classical
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · -- injectivity: test the two restricted families on a point `⟨a, s⟩` of the coproduct
    apply Subtype.ext
    funext n
    apply ContinuousMap.ext
    intro p
    obtain ⟨a, s⟩ := p
    have key := congrArg (fun z : boundedRealSet (X a) => z.1 n s) (congrFun h a)
    change (boundedRealTypePresheaf.map (CompHausLike.finiteCoproduct.ι X a).op x).1 n s =
      (boundedRealTypePresheaf.map (CompHausLike.finiteCoproduct.ι X a).op y).1 n s
    exact key
  · -- surjectivity: glue the given families, with the sum of the bounds as a bound
    haveI : Fintype α := Fintype.ofFinite α
    choose N hN using fun a => (y a).2
    let x : boundedRealSet (CompHausLike.finiteCoproduct X) :=
      ⟨fun n =>
        ⟨fun p => (y p.1).1 n p.2, by
          -- a function on the disjoint union is continuous iff it is so on each summand
          apply continuous_sigma
          intro a
          exact ((y a).1 n).continuous⟩,
        ⟨∑ a, max (N a) 0, fun n p => by
          -- the bound is `∑_a max (N a) 0 ≥ max (N a) 0 ≥ N a ≥ |y_a(n)(s)|`
          show |(y p.1).1 n p.2| ≤ ∑ a, max (N a) 0
          calc |(y p.1).1 n p.2| ≤ N p.1 := hN p.1 n p.2
            _ ≤ max (N p.1) 0 := le_max_left _ _
            _ ≤ ∑ a, max (N a) 0 :=
                Finset.single_le_sum (fun i _ => le_max_right _ _) (Finset.mem_univ p.1)⟩⟩
    refine ⟨x, ?_⟩
    funext a
    apply Subtype.ext
    funext n
    apply ContinuousMap.ext
    intro s
    change (boundedRealTypePresheaf.map (CompHausLike.finiteCoproduct.ι X a).op x).1 n s = (y a).1 n s
    rfl

end Work.ANALYTIC
