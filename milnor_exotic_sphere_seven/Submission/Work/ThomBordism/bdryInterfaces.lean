import Mathlib
import Submission.Work.ThomBordism.boundaryAssembly
import Submission.Work.Cohomology.RelCapHTransfer
import Submission.Work.Cohomology.PairSequence
import Submission.Work.Cohomology.KroneckerH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Interfaces for the middle-degree Lefschetz duality of the pair `(W, ∂W)`

`Work.ThomBordism.BoundaryMaximalIsotropic` — the crux of `Work.ThomBordism.BoundarySigma` — is
the maximality half of **middle-dimensional Lefschetz duality** for the pair `(W, ∂W)` of a
`NullBordismFamily`.  This file fixes the vocabulary in which the two halves of the argument are
stated:

* `LefschetzDualityBdry W` — **middle Lefschetz duality**: the relative cap product with the
  relative fundamental class `W.w` is bijective in every bidegree `(k, m)` with `k + m = 9`.  This
  is the workspace's named input `Work.Surgery.LefschetzDuality`
  (`Submission/Work/Surgery/RelativeDisc.lean`), instantiated for `(W, bdrySet W.W)`; the
  `Work.Surgery` copy cannot be imported here together with `Work.ThomBordism.Interface` because of
  the remaining import clash `Work.Cohomology.prodSphereAux` (two modules of that name,
  `Submission/Work/Cohomology/prodSphereAux.lean` and
  `Submission/Work/Cohomology/CompatTrans/prodSphereAux.lean`).
* `deltaRat` — the rationalised connecting map `δ : H⁴(∂W;ℚ) → H⁵(W,∂W;ℚ)` of the pair.

## Main results

* `Work.ThomBordism.lefschetzDualityBdry` (delegated) — `LefschetzDualityBdry W` for every `W`;
* `Work.ThomBordism.boundaryOfLefschetz` (delegated) —
  `(∀ W, LefschetzDualityBdry W) → BoundaryMaximalIsotropic`, the *formal* reduction, whose
  content is the elementary transgression identity
  `B (r u) y = ± ⟨u, (δ y) ⌢ w⟩` (Leibniz rule for the cap product plus naturality of the
  Kronecker pairing: `i_*(y ⌢ ∂w) = ± δy ⌢ w`);
* `Work.ThomBordism.boundaryMaximalIsotropic` — the target, from the two.
-/

set_option autoImplicit false

open CategoryTheory AlgebraicTopology
open scoped TensorProduct

namespace Work.ThomBordism

noncomputable section

variable {ι : Type} [Fintype ι] {F : ι → Man8}

/-- **The rationalised relative cohomology** `Hᵏ(W, ∂W; ℚ)`. -/
abbrev relH (W : NullBordismFamily ι F) (k : ℕ) : Type :=
  ℚ ⊗[ℤ] ↑(Work.Cohomology.relCohomology ℤ (TopCat.of W.W) (bdrySet W.W) k)

/-- **The rationalised homology** `Hₖ(W; ℚ)`. -/
abbrev homH (W : NullBordismFamily ι F) (k : ℕ) : Type :=
  ℚ ⊗[ℤ] ↑((Work.Cohomology.chainC ℤ (TopCat.toSSet.obj (TopCat.of W.W))).homology k)

/-- **The rationalised connecting map** `δ : H⁴(∂W;ℚ) ⟶ H⁵(W,∂W;ℚ)` of the pair `(W, ∂W)`. -/
def deltaRat (W : NullBordismFamily ι F) :
    Work.SignatureBordism.ratCohomology 4 (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))) →ₗ[ℚ]
      relH W 5 :=
  (Work.Cohomology.pairδ ℤ (TopCat.of W.W) (bdrySet W.W) 4).hom.baseChange ℚ

/-- **The relative cap product pairing** `Hᵏ(W,∂W;ℤ) →ₗ (H_{k+m}(W,∂W;ℤ) →ₗ H_m(W;ℤ))`. -/
def lefschetzMapBdry (W : NullBordismFamily ι F) (k m : ℕ) :
    ↑(Work.Cohomology.relCohomology ℤ (TopCat.of W.W) (bdrySet W.W) k) →ₗ[ℤ]
      (↑((Work.Cohomology.relChains (TopCat.of W.W) (bdrySet W.W)).homology (k + m)) →ₗ[ℤ]
        ↑((Work.Cohomology.singularChains ℤ (TopCat.of W.W)).homology m)) :=
  Work.Cohomology.relCapPair (TopCat.of W.W) (bdrySet W.W) k m


/-- **Poincaré–Lefschetz duality for the pair `(W, ∂W)`**: the relative cap product with the
relative fundamental class `W.w` is bijective in every bidegree `(k, m)` with `k + m = 9`. -/
def LefschetzDualityBdry (W : NullBordismFamily ι F) : Prop :=
  ∀ k m (h : k + m = 9),
    Function.Bijective (fun z => (lefschetzMapBdry W k m) z (h ▸ W.w))

end

end Work.ThomBordism
