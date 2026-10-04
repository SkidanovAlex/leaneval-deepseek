import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.far_sphere_size
import Submission.Work.Diff.C.rgrad_fcos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The polarization step of Half 2

`Work.Diff.C.rhess_rdist_bound_of_hHess` (`Diff/C/far_sphere_size.lean`, PROVED) bounds the *diagonal*
of the shape operator of `S(q, d)` modulo the constant `cot d`:

`|rhess (rdist q) x V V - cot (rdist q x) · ⟪V,V⟫| ≤ (ε/sin (rdist q x)) · ‖V‖²`  for `V ⊥ ∇(rdist q)`,

and `Work.Diff.C.rhess_symm` (`Diff/C/rhess_symm.lean`, PROVED) says the same bilinear form is
symmetric.  Since `rhess cov f x` is bilinear (it is `⟪cov (∇f) x ·, ·⟫`), the polarization identity
`B(V,W) = (B(V+W,V+W) - B(V-W,V-W))/4` (valid for symmetric `B`), together with the scaling trick
`V ↦ V/t`, `W ↦ tW` and `2‖V‖‖W‖ ≤ ‖V/t‖·t‖W‖`-minimisation, upgrades the diagonal bound to **all
pairs**:

`|rhess (rdist q) x V W - cot (rdist q x) · ⟪V,W⟫| ≤ (ε / sin (rdist q x)) · ‖V‖ · ‖W‖`

(for `V, W ⊥ ∇(rdist q)`).  This is the "shape operator is scalar to leading order" statement that
Half 2 of `Work.Diff.C.GeoCrux.ShapeFiniteDiffProp` uses (see `geoCrux/ShapeDiffDefs.lean`).

Inputs, both proved: `rhess_rdist_bound_of_hHess` (diagonal bound) and `rhess_symm` (symmetry, hence
`htor : cov.torsion = 0` is required).  **Simpler route, avoiding polarization altogether** (pointed
out by the reviewer): `HessBoundRegion` bounds the *full bilinear form*
`|rhess (fcos q) x V W + fcos q x · ⟪V,W⟫| ≤ ε₁‖V‖‖W‖`, and the chain rule for `cos`
(`Work.Diff.C.rhess_cos_far`, `Diff/C/far_sphere_size.lean`, PROVED) turns this into the statement
below *directly*, for all pairs, as soon as `Real.sin (rdist q x) > 0` — which is exactly why the
pointwise hypotheses `hsm`, `hpos`, `hdπ` are carried.  The constant `ε₁/sin` (not `2ε₁/sin`) is
therefore correct.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle Set VectorField CovariantDerivative Metric

namespace Work.Diff.C.GeoCrux

/-- **Polarized shape-operator bound.**  On the orthogonal complement of `∇(rdist q)`, the deviation
of the shape operator of the geodesic sphere from `cot (rdist q ·)` times the metric is bounded by
`ε / sin (rdist q x)` in *every* pair of directions, not only the diagonal. -/
abbrev ShapePolarizedProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {c ε₁ : ℝ} {q : M}
    (hHess : HessBoundRegion (I := I) (M := M) cov c ε₁ (fcos (I := I) (M := M) q))
    {x : M} (hx : -1 + c < fcos (I := I) (M := M) q x)
    (hsm : CMDiffAt ∞ (fun z : M ↦ rdist (I := I) (M := M) q z) x)
    (hpos : 0 < rdist (I := I) (M := M) q x)
    (hdπ : rdist (I := I) (M := M) q x < Real.pi)
    (V W : TangentSpace I x)
    (hV : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x) V = 0)
    (hW : Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) x) W = 0),
    |Work.Diff.C.rhess cov (fun z : M ↦ rdist (I := I) (M := M) q z) x V W
        - Real.cot (rdist (I := I) (M := M) q x) * Inner.inner ℝ V W|
      ≤ (ε₁ / Real.sin (rdist (I := I) (M := M) q x)) * ‖V‖ * ‖W‖


/-! ## Direct-proof skeleton (for the prover)

The direct route (no polarization) is: `HessBoundRegion` gives
`|rhess (fcos q) x V W + fcos q x · ⟪V,W⟫| ≤ ε₁‖V‖‖W‖`; `Work.Diff.C.rhess_cos_far` (PROVED) gives
`rhess (cos ∘ F) x V W = -cos (F x)·(mvfderiv F x V · mvfderiv F x W) - sin (F x)·rhess F x V W`
with `F := rdist q`; `Work.Diff.C.rgrad_fcos` (PROVED) gives
`∇(fcos q) x = (-sin d) • ∇F x`, whence `V ⊥ ∇(fcos q) x ⟹ mvfderiv F x V = 0` (and same for `W`);
so `rhess (fcos q) x V W = -sin d · rhess F x V W` and the Hessian bound becomes
`|-sin d·R + cos d·⟪V,W⟫| ≤ ε₁‖V‖‖W‖`;
dividing by `sin d > 0` and using `sin d·cot d = cos d` gives the statement.

Two formalisation snags encountered when attempting this inline (both routine):
`mvfderiv I F x V` and `mfderiv I 𝓘(ℝ,ℝ) F x V` must be aligned before `Work.Diff.C.inner_rgrad`
can be used (use the workspace lemma `inner_rgrad_mvfderiv`-style rather than `inner_rgrad`), and the
final step wants `abs_mul`/`abs_of_pos hsin` applied to
`sin d * |R - cot d·⟪V,W⟫|` with `sin d·cot d = cos d` (`field_simp`) rather than a bare `ring_nf`.
-/
end Work.Diff.C.GeoCrux
