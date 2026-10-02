import Mathlib
import Submission.Work.TangentClasses.Bundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

/-!
# The tangent bundle of a smooth manifold

The chapter's notion of a real vector bundle is gluing data over an open cover
(`Submission/Work/TangentClasses/Bundle.lean`).  A smooth manifold comes with exactly such data
for its tangent bundle: the cover by the charts of the atlas, and the transition functions given
by the derivatives (Jacobians) of the chart transitions.  Mathlib constructs this as
`tangentBundleCore 𝕜 I M : VectorBundleCore 𝕜 M E (atlas H M)`; in this module we name it
`Work.TangentClasses.tangentBundle` and record its basic API:

* `tangentBundle_baseSet` — the cover is the sources of the charts;
* `tangentBundle_coordChange_achart` — the transition function between the preferred charts at
  `x` and `x'` is the Fréchet derivative of the chart transition `extChartAt I x' ∘ (extChartAt I
  x)⁻¹` within `range I`;
* `tangentBundle_fiber` / `tangentBundle_totalSpace` — its fibre is `TangentSpace I x = E` and its
  total space is Mathlib's `TangentBundle I M` (which carries the `VectorBundle ℝ E`,
  `FiberBundle E`, `ChartedSpace (ModelProd H E)` and smooth-manifold structures, and — when
  `M` is `C^{n+1}` — the `ContMDiffVectorBundle` structure, `tangentBundle_contMDiff`);
* `tangentBundle_rank` — its rank is `finrank ℝ E`;
* `tangentBundle_model_coordChange` — **the tangent bundle of the model space `E` is trivial**:
  every transition function is the identity (Mathlib's `TangentBundle.coordChange_model_space`).
  This is the bundle-level form of "`T(M × ℝ^k)` differs from `TM` by a trivial summand", i.e. of
  the stability of characteristic classes;
* `tangentBundle_prod_coordChange` (delegated, `TangentClasses/ProdBundle.lean`) — **the Jacobian
  computation for a product**: on the product `M × N` the transition functions of the tangent
  bundle are the block-diagonal (Whitney-sum) combinations of those of `TM` and `TN`.  Together
  with the gluing-data operations of `Bundle.lean` this is the bundle-level statement behind
  `p(T(M × N)) = p(TM) · p(TN)`.
-/

namespace Work.TangentClasses

open Bundle
open scoped Manifold ContDiff
open Set

noncomputable section

/-! ## The normed structure on the product model

Mathlib provides the product model `ModelProd E E'` (a type tag for `E × E'`) with the topological
structure but not with the normed structure; the tangent bundle of a manifold charted on
`ModelProd H H'` — e.g. the product `M × N` of two manifolds — needs it.  The instances below are
the product ones. -/

instance instModelProdNormedAddCommGroup {E E' : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup E'] : NormedAddCommGroup (ModelProd E E') :=
  inferInstanceAs (NormedAddCommGroup (E × E'))

instance instModelProdNormedSpace {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    [NormedSpace ℝ E] [NormedSpace ℝ E'] : NormedSpace ℝ (ModelProd E E') :=
  inferInstanceAs (NormedSpace ℝ (E × E'))

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]

/-- **The tangent bundle of a smooth manifold**, as a real bundle in the chapter's gluing model:
the cover is the atlas of `M` and the transition functions are the derivatives of the chart
transitions.  This is Mathlib's `tangentBundleCore`. -/
def tangentBundle (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I 1 M] : RealBundle M E (atlas H M) :=
  tangentBundleCore I M

variable {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- The cover of the tangent bundle is the cover by the chart sources. -/
theorem tangentBundle_baseSet (i : atlas H M) :
    (tangentBundle I M).baseSet i = i.1.source := rfl

/-- The transition function of the tangent bundle between the preferred charts at `x` and `x'` is
the derivative of the chart transition — the Jacobian of the change of coordinates. -/
theorem tangentBundle_coordChange_achart (x x' z : M) :
    (tangentBundle I M).coordChange (achart H x) (achart H x') z =
      fderivWithin ℝ (extChartAt I x' ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) :=
  rfl

/-- The transition function, as a family indexed by the points of the manifold (the
`tangentCoordChange` of Mathlib). -/
theorem tangentBundle_coordChange_eq_tangentCoordChange (x x' z : M) :
    (tangentBundle I M).coordChange (achart H x) (achart H x') z = tangentCoordChange I x x' z :=
  rfl

/-- The fibre of the tangent bundle is the tangent space. -/
theorem tangentBundle_fiber (x : M) : (tangentBundle I M).Fiber x = TangentSpace I x := rfl

/-- The total space of the tangent bundle is Mathlib's `TangentBundle`. -/
theorem tangentBundle_totalSpace : (tangentBundle I M).TotalSpace = TangentBundle I M := rfl

/-- The rank of the tangent bundle is the dimension of the model space. -/
theorem tangentBundle_rank : (tangentBundle I M).rank = Module.finrank ℝ E := rfl

/-- The tangent bundle of a `C^{n+1}` manifold is a `C^n` vector bundle. -/
theorem tangentBundle_contMDiff (n : ℕ∞ω) [IsManifold I (n + 1) M] :
    (tangentBundle I M).IsContMDiff I n :=
  tangentBundleCore.isContMDiff

/-- **The tangent bundle of the model space is trivial**: all its transition functions are the
identity (Mathlib's `TangentBundle.coordChange_model_space`).  This is the bundle-level form of the
stability of the characteristic classes of the tangent bundle under products with `ℝ^k`. -/
@[simp] theorem tangentBundle_model_coordChange {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (b b' x : F) :
    (tangentBundle (𝓘(ℝ, F)) F).coordChange (achart F b) (achart F b') x = 1 :=
  TangentBundle.coordChange_model_space b b' x

end

end Work.TangentClasses
