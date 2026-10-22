import Mathlib
import Submission.Work.ANALYTIC.BoundedType

/-!
# `∏^bnd ℤ` on a finite coproduct of light profinite sets

`boundedTypePresheaf` (`Submission/Work/ANALYTIC/BoundedType.lean`) is the underlying presheaf of
*types* of the presheaf of uniformly bounded sequences of `Submission/Work/ANALYTIC/Bounded.lean`:
at a light profinite set `S` its value is the set of uniformly bounded families `(x_n)` of
continuous `ℤ`-valued functions on `S`.

This file shows that, for a *finite* family `X : α → LightProfinite`, restriction to the summands
gives a bijection

`boundedTypePresheaf (∐_a X a) ≅ ∏_a boundedTypePresheaf (X a)`,

i.e. the map that sends a bounded sequence on the explicit finite coproduct of the `X a` (whose
underlying space is the disjoint union `Σ a, X a`) to its family of restrictions along the
inclusions `finiteCoproduct.ι X a` is bijective.  This is one half of the sheaf condition for the
coherent topology on `LightProfinite` (`Submission/Work/ANALYTIC/boundedSeq_sheaf.lean`).

The two ingredients are:

* injectivity: every point of `∐_a X a` lies in one of the summands, since it is a point `⟨a, s⟩`
  of the disjoint union;
* surjectivity: coordinates are glued along the (disjoint) union — a function on `Σ a, X a` is
  continuous iff its restriction to each summand is — and, crucially, the index set `α` is
  *finite*, so that the supremum of the finitely many bounds of the given families is again a
  bound.  Finiteness is essential here: for an infinite `α` the glued family need not be uniformly
  bounded.
-/

open CategoryTheory

noncomputable section

set_option linter.style.haveILetI false

namespace Work.ANALYTIC

/-- Evaluation of the restriction of a bounded sequence along a morphism `f : S ⟶ T` of light
profinite sets: the `n`-th coordinate at a point `s` of the source is the `n`-th coordinate of the
original sequence at the image of `s`.  This is `rfl`, since this is how `boundedPresheaf` is
defined. -/
theorem boundedTypePresheaf_map_apply {S T : LightProfinite} (f : S ⟶ T) (x : boundedSeqSet T)
    (n : ℕ) (s : S) :
    (boundedTypePresheaf.map f.op x).1 n s = x.1 n (f s) := rfl

/-- The points of the explicit finite coproduct are the points of the summands. -/
theorem finiteCoproduct_ι_apply {α : Type} [Finite α] (X : α → LightProfinite) (a : α)
    (s : X a) :
    (CompHausLike.finiteCoproduct.ι X a s : ↥(CompHausLike.finiteCoproduct X).toTop) = ⟨a, s⟩ :=
  rfl

theorem boundedSeq_coprod {α : Type} [Finite α] (X : α → LightProfinite) :
    Function.Bijective (fun x : boundedTypePresheaf.obj (Opposite.op (CompHausLike.finiteCoproduct X)) =>
      fun a => boundedTypePresheaf.map (CompHausLike.finiteCoproduct.ι X a).op x) := by
  classical
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · -- injectivity: test the two restricted families on a point `⟨a, s⟩` of the coproduct
    apply Subtype.ext
    funext n
    apply ContinuousMap.ext
    intro p
    obtain ⟨a, s⟩ := p
    have key := congrArg (fun z : boundedSeqSet (X a) => z.1 n s) (congrFun h a)
    change (boundedTypePresheaf.map (CompHausLike.finiteCoproduct.ι X a).op x).1 n s =
      (boundedTypePresheaf.map (CompHausLike.finiteCoproduct.ι X a).op y).1 n s
    exact key
  · -- surjectivity: glue the given families, with the supremum of the bounds as a bound
    haveI : Fintype α := Fintype.ofFinite α
    choose N hN using fun a => (y a).2
    let B : α → ℕ := fun a => (max (N a) 0).toNat
    let x : boundedSeqSet (CompHausLike.finiteCoproduct X) :=
      ⟨fun n =>
        ⟨fun p => (y p.1).1 n p.2, by
          -- a function on the disjoint union is continuous iff it is so on each summand
          apply continuous_sigma
          intro a
          exact ((y a).1 n).continuous⟩,
        ⟨((Finset.sup Finset.univ B : ℕ) : ℤ), fun n p => by
          -- the bound is `sup_a (max (N a) 0) ≥ max (N a) 0 ≥ N a ≥ |y_a(n)(s)|`
          show |(y p.1).1 n p.2| ≤ (((Finset.sup Finset.univ B : ℕ)) : ℤ)
          calc |(y p.1).1 n p.2| ≤ N p.1 := hN p.1 n p.2
            _ ≤ max (N p.1) 0 := le_max_left _ _
            _ = ((B p.1 : ℕ) : ℤ) := (Int.toNat_of_nonneg (le_max_right _ _)).symm
            _ ≤ _ := by
                exact_mod_cast
                  (Finset.le_sup (Finset.mem_univ p.1) : B p.1 ≤ Finset.sup Finset.univ B)⟩⟩
    refine ⟨x, ?_⟩
    funext a
    apply Subtype.ext
    funext n
    apply ContinuousMap.ext
    intro s
    change (boundedTypePresheaf.map (CompHausLike.finiteCoproduct.ι X a).op x).1 n s = (y a).1 n s
    rfl

end Work.ANALYTIC
