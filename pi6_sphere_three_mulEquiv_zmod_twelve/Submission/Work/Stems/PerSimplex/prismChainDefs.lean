import Mathlib
import Submission.Work.Stems.hurewiczMapN_surjective

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The prism chain of a homotopy of simplices

For a continuous map `G : Δ^d × I → X` (a homotopy of a `d`-simplex) we define its **prism chain**
`prismChain d G ∈ C_{d+1}(X)`, the alternating sum of the chains of the `d + 1` simplicial pieces
of the product triangulation of `Δ^d × I`.  This is the chain-level avatar of the prism operator;
the face version of the current file's main theorem (`prismChainBoundary` in the sibling module)
computes its boundary as the difference of the top and bottom chains minus the alternating sum of
the prism chains of the face homotopies.
-/

open CategoryTheory AlgebraicTopology Simplicial
open scoped Topology unitInterval Simplicial BigOperators

namespace Work.Stems.PerSimplex

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- The `k`-th simplicial piece of the product triangulation of `Δ^d × I` carries the singular
`(d+1)`-simplex `G ∘ pp d k`.  The **prism chain** is their alternating sum. -/
def prismChain (d : ℕ) (G : C(↥(stdSimplex ℝ (Fin (d+1))) × unitInterval, X)) :
    (Work.Stems.hChain X).X (d+1) :=
  ∑ k : Fin (d+1), (-1:ℤ)^((k:ℕ)+1) •
    Work.Stems.simplexChain (X:=X) (d+1)
      (Work.RatHurewicz.Bridge.simplexOf (d+1) (G.comp (Work.Serre.pp d k)))

@[simp] theorem prismChain_def (d : ℕ)
    (G : C(↥(stdSimplex ℝ (Fin (d+1))) × unitInterval, X)) :
    prismChain (X := X) d G
      = ∑ k : Fin (d+1), (-1:ℤ)^((k:ℕ)+1) •
          Work.Stems.simplexChain (X:=X) (d+1)
            (Work.RatHurewicz.Bridge.simplexOf (d+1) (G.comp (Work.Serre.pp d k))) := rfl

end

end Work.Stems.PerSimplex
