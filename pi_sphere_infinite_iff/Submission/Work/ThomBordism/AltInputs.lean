import Mathlib
import Submission.Work.ThomBordism.boundaryAssembly
import Submission.Work.ThomBordism.bdryInterfaces
import Submission.Work.ThomBordism.boundaryOfLefschetz

/-!
# The two inputs of the alternative route to `BoundaryMaximalIsotropic`

`Submission/Work/ThomBordism/bdryMaximalIsoAlt.lean` reduces the crux
`Work.ThomBordism.BoundaryMaximalIsotropic` to two statements, isolated here so that they can be
attacked independently:

* `Work.ThomBordism.Detection` (`Submission/Work/ThomBordism/boundaryOfLefschetz.lean`) — the
  non-degeneracy of the rationalised Kronecker pairing `H⁴(W;ℚ) × H₄(W;ℚ) → ℚ` in its second
  variable.  Over a field this is the universal coefficient theorem for the singular chain complex;
  it also follows from the Poincaré duality of the double `D = W ∪_∂W W̄` (whose cap product with
  the fundamental class is bijective, `Work.Cohomology.pd_capPair_of_good`) together with the
  folding map `D → W`: the fold exhibits `H₄(W;ℚ) → H₄(D;ℚ)` as injective and
  `H⁴(D;ℚ) → H⁴(W;ℚ)` as split surjective, and `⟨u, z⟩_W = ⟨f^* u, ι_* z⟩_D`
  (`Work.Cohomology.kronH_natural`).

* `Work.ThomBordism.KerPhiZero` — **the geometric input**: the transgression map
  `Φ y = i_*(y ⌢ ∂w) = (δ y) ⌢ w` (`Work.ThomBordism.phiBdry`, the transgression identity
  `Work.ThomBordism.transgressionCapPairConnecting`) has kernel inside `ker δ`:
  `Φ y = 0 → δ y = 0` for `y ∈ H⁴(∂W;ℚ)`.  Equivalently, the relative cap product with the relative
  fundamental class, `y ↦ y ⌢ w : H⁵(W,∂W;ℚ) → H₄(W;ℚ)`, is injective on `im δ`.  This is the
  `(5,4)`-bidegree injectivity half of middle-dimensional Lefschetz duality for the pair `(W, ∂W)`
  ("half lives, half dies"), and it follows from the full statement
  `Work.ThomBordism.LefschetzDualityBdry W` (`∀ k m, k + m = 9 → Function.Bijective (· ⌢ w)`,
  `Submission/Work/ThomBordism/bdryInterfaces.lean`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicTopology
open scoped TensorProduct

namespace Work.ThomBordism

noncomputable section

variable {ι : Type} [Fintype ι] {F : ι → Man8}

/-- **The geometric input.**  The transgression map `Φ = i_*(· ⌢ ∂w) = δ(·) ⌢ w`, rationalised, has
kernel contained in `ker δ`: a rational class `y ∈ H⁴(∂W;ℚ)` with `Φ y = 0` lies in the image of
the restriction `H⁴(W;ℚ) → H⁴(∂W;ℚ)`.

Equivalently: the rational relative cap product with the fundamental class,
`y ↦ y ⌢ w : H⁵(W,∂W;ℚ) → H₄(W;ℚ)`, is injective on the image of `δ`; this is the `(5,4)`-bidegree
injectivity half of middle-dimensional Lefschetz duality for the pair `(W, ∂W)`, and it is implied
by `Work.ThomBordism.LefschetzDualityBdry W` (bijectivity of `· ⌢ w` in every bidegree). -/
def KerPhiZero : Prop :=
  ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F)
    (y : Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of (bdrySet W.W)))),
    (phiBdry W).baseChange ℚ y = 0 → deltaRat W y = 0

end

end Work.ThomBordism
