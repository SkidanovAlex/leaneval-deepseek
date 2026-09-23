import Submission.Distance

/-!
# The Riemannian distance: Mathlib's `riemannianEDist`

Mathlib already contains a Riemannian (extended) distance
`Manifold.riemannianEDist I x y`, defined as the infimum of the lengths `pathELength I γ a b` of
`C¹` paths from `x` to `y`, together with

* the triangle inequality `Manifold.riemannianEDist_triangle`,
* symmetry and `riemannianEDist_self`,
* the construction `PseudoEMetricSpace.ofRiemannianMetric` / `EMetricSpace.ofRiemannianMetric`
  whose topology is *definitionally* the manifold topology,
* the two one-sided comparison lemmas `eventually_riemannianEDist_lt` (points close in the topology
  are close for the Riemannian distance) and `setOfPred_riemannianEDist_lt_subset_nhds` (points close
  for the Riemannian distance are close in the topology).

The only hypothesis missing in our setting is `IsContinuousRiemannianBundle`, which is however an
immediate consequence of the smoothness hypothesis `IsContMDiffRiemannianBundle` (Mathlib does not
provide the instance because the smoothness level `n` cannot be guessed).  This module supplies it,
and collects the resulting facts about `riemannianEDist` that the rest of the development uses.

## Main results

* `isContinuousRiemannianBundle_of_contMDiffRiemannianBundle`;
* `Manifold.riemannianEDist_pos`, `Manifold.riemannianEDist_eq_zero_iff`: the Riemannian distance
  is positive between distinct points;
* `riemannianEDist_le_pathELength` (Mathlib) gives upper bounds from explicit paths;
* the `EMetricSpace` structure `EMetricSpace.ofRiemannianMetric I M` has the manifold topology and
  satisfies `edist x y = riemannianEDist I x y` (`edist_eq_riemannianEDist`).

## Consequence for the project

The whole *metric* chapter (piecewise paths, additivity of length, triangle inequality, comparison
with the topology) is available in Mathlib.  The development in this workspace should from now on
use `Manifold.riemannianEDist` and `Manifold.pathELength`; the files `Submission/Length.lean` and
`Submission/Distance.lean` are kept only because they provide the explicit speed/length API in
charts (`curveSpeed_chartCurve`, `curveSpeed`), which is convenient for computations along
geodesics.
-/
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Submission.EDist

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- **A smooth Riemannian bundle is a continuous Riemannian bundle.**  Mathlib cannot infer this
as an instance because the smoothness level `n` would have to be guessed. -/
theorem isContinuousRiemannianBundle_of_contMDiffRiemannianBundle {n : ℕ∞ω}
    [IsContMDiffRiemannianBundle I n E (fun (x : M) ↦ TangentSpace I x)] :
    IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) := by
  obtain ⟨g, hg, hg'⟩ := IsContMDiffRiemannianBundle.exists_contMDiff (IB := I) (n := n)
    (F := E) (E := fun (x : M) ↦ TangentSpace I x)
  exact ⟨g, hg.continuous, hg'⟩

/-- The instance form of `isContinuousRiemannianBundle_of_contMDiffRiemannianBundle`.  It has to be
activated locally (`haveI`) to avoid an instance loop. -/
theorem isContinuousRiemannianBundle_infty :
    IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
  isContinuousRiemannianBundle_of_contMDiffRiemannianBundle (I := I) (n := ∞)

section Distance

variable [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

/-- **The Riemannian distance between distinct points is positive.** -/
theorem riemannianEDist_pos [RegularSpace M] {x y : M} (h : x ≠ y) :
    0 < Manifold.riemannianEDist I x y :=
  lt_of_le_of_ne' (by simp : (0 : ℝ≥0∞) ≤ _) (fun h0 => by
    have hU : ({y}ᶜ : Set M) ∈ 𝓝 x :=
      isClosed_singleton.isOpen_compl.mem_nhds (by simpa using h)
    obtain ⟨c, hc, hcs⟩ := _root_.setOfPred_riemannianEDist_lt_subset_nhds' I hU
    have hy : y ∈ {z : M | Manifold.riemannianEDist I x z < c} := by
      rw [Set.mem_ofPred_eq, h0]; exact hc
    exact (hcs hy) (by simp))

/-- The Riemannian distance vanishes exactly on the diagonal. -/
theorem riemannianEDist_eq_zero_iff [RegularSpace M] {x y : M} :
    Manifold.riemannianEDist I x y = 0 ↔ x = y :=
  ⟨fun h => by
      by_contra hne
      exact absurd h (ne_of_gt (riemannianEDist_pos (I := I) hne)),
    fun h => by rw [h]; exact Manifold.riemannianEDist_self⟩

/-- With the emetric structure induced by the Riemannian metric, `edist` is the Riemannian
extended distance. -/
theorem edist_eq_riemannianEDist [RegularSpace M] (x y : M) :
    letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    edist x y = Manifold.riemannianEDist I x y := by
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  exact IsRiemannianManifold.out x y

/-- The topology of the emetric space associated with the Riemannian metric is the manifold
topology.  (The two are definitionally equal, which is why this is `rfl`.) -/
theorem topologicalSpace_ofRiemannianMetric [RegularSpace M] :
    letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    (inferInstance : TopologicalSpace M) = (inferInstance : TopologicalSpace M) := rfl

/-- Points close for the topology have small Riemannian distance. -/
theorem eventually_riemannianEDist_lt [RegularSpace M] (x : M) {c : ℝ≥0∞} (hc : 0 < c) :
    ∀ᶠ y in 𝓝 x, Manifold.riemannianEDist I x y < c :=
  _root_.eventually_riemannianEDist_lt I x hc

/-- Points at small Riemannian distance from `x` lie in any prescribed neighbourhood of `x`. -/
theorem setOf_riemannianEDist_lt_subset_nhds [RegularSpace M] {x : M} {s : Set M}
    (hs : s ∈ 𝓝 x) :
    ∃ c > 0, {y | Manifold.riemannianEDist I x y < c} ⊆ s :=
  _root_.setOfPred_riemannianEDist_lt_subset_nhds' I hs

/-- A continuous curve has finite Riemannian distance between its endpoints: the extended distance
is bounded by the (finite) length of an explicit path. -/
theorem riemannianEDist_le_pathELength {γ : ℝ → M} {a b : ℝ} {x y : M}
    (hγ : CMDiff[Icc a b] 1 γ) (ha : γ a = x) (hb : γ b = y) (hab : a ≤ b) :
    Manifold.riemannianEDist I x y ≤ Manifold.pathELength I γ a b :=
  Manifold.riemannianEDist_le_pathELength hγ ha hb hab

end Distance

end Submission.EDist
