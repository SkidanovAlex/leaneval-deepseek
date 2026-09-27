import Mathlib
import Submission.Work.Projection.Basic
import Submission.Work.Projection.Defs

/-!
# The chartwise "bad direction" sets for a general model with corners

The file `Submission/Work/Projection/Defs.lean` sets up the bad-direction sets of the Whitney
projection argument for the standard model `𝓡 n` on `EuclideanSpace ℝ (Fin n)`, using charts
`chartAt (EuclideanSpace ℝ (Fin n)) p` with values in the half space `H`.

Here we redo the construction for an arbitrary model with corners `I : ModelWithCorners ℝ E H`,
using the *extended* charts `extChartAt I p : M → E` with values in the model space `E` itself.
This makes the domains of the parametrising maps subsets of `E × E`, so that the Hausdorff
dimension bounds of `dimH_badImmCharts`/`dimH_badInjCharts` become statements about
`finrank ℝ (E × E) = 2 * finrank ℝ E`.

Since `mfderiv` is defined using `fderivWithin` with respect to `range I`, the definitions here
use `fderivWithin ℝ _ (Set.range I)` which coincides with `fderiv` when `I` is boundaryless
(`fderivWithin_range_I`).  Using `fderivWithin` keeps the definitions meaningful for manifolds
with boundary as well.
-/

open scoped Manifold ContDiff
open Topology

namespace Work.Projection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

section Defs

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The representation `y ↦ f (extChart⁻¹ y)` of `f` in the extended chart at `p`. -/
noncomputable def chartRepI {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1))) (p : M) :
    E → EuclideanSpace ℝ (Fin (k+1)) :=
  fun y => f ((extChartAt I p).symm y)

lemma chartRepI_extChartAt {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1))) (p x : M)
    (hx : x ∈ (extChartAt I p).source) :
    chartRepI (I := I) f p ((extChartAt I p) x) = f x := by
  simp only [chartRepI]
  rw [PartialEquiv.left_inv (extChartAt I p) hx]

/-- The open set on which the parametrisation of the immersion-bad set of the extended chart at
`p` is smooth: the first coordinate lies in the chart target and the relevant derivative has
nonzero last coordinate. -/
noncomputable def immDomI {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1))) (p : M) :
    Set (E × E) :=
  {yw | yw.1 ∈ (extChartAt I p).target ∧
        (fderivWithin ℝ (chartRepI (I := I) f p) (Set.range I) yw.1 yw.2) (Fin.last k) ≠ 0}

/-- The parametrisation of the immersion-bad set of the extended chart at `p`. -/
noncomputable def immParamI {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1))) (p : M) :
    E × E → EuclideanSpace ℝ (Fin k) :=
  fun yw => extract (fderivWithin ℝ (chartRepI (I := I) f p) (Set.range I) yw.1 yw.2)

/-- The immersion-bad directions of a map `f`, defined chartwise with the extended charts:
`u` is bad for the chart at `p i` if `(u,1)` lies in the image of the derivative of the chart
representation of `f`. -/
noncomputable def badImmChartsI {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1))) (p : ℕ → M) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  {u | ∃ i, ∃ y ∈ (extChartAt I (p i)).target, ∃ w : E,
        fderivWithin ℝ (chartRepI (I := I) f (p i)) (Set.range I) y w = vVec u}

/-- Every immersion-bad direction occurs as the value of the parametrisation of the bad set of one
of the charts. -/
lemma badImmChartsI_subset {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {k : ℕ}
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (p : ℕ → M) :
    badImmChartsI (I := I) f p ⊆
      ⋃ i, immParamI (I := I) f (p i) '' (immDomI (I := I) f (p i)) := by
  rintro u ⟨i, y, hy, w, hw⟩
  refine Set.mem_iUnion.2 ⟨i, ⟨(y, w), ⟨hy, ?_⟩, ?_⟩⟩
  · rw [hw, vVec_last]
    norm_num
  · simp only [immParamI]
    rw [hw, extract_vVec]

/-- The open set on which the parametrisation of the injectivity-bad set of the extended charts at
`p`, `q` is smooth. -/
noncomputable def injDomI {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1))) (p q : M) :
    Set (E × E) :=
  {yz | yz.1 ∈ (extChartAt I p).target ∧
        yz.2 ∈ (extChartAt I q).target ∧
        (chartRepI (I := I) f p yz.1 - chartRepI (I := I) f q yz.2) (Fin.last k) ≠ 0}

/-- The parametrisation of the injectivity-bad set of the extended charts at `p`, `q`. -/
noncomputable def injParamI {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1))) (p q : M) :
    E × E → EuclideanSpace ℝ (Fin k) :=
  fun yz => extract (chartRepI (I := I) f p yz.1 - chartRepI (I := I) f q yz.2)

/-- The injectivity-bad directions of a map `f`, defined chartwise with the extended charts:
`u` is bad if two points in the extended charts at `p i` and `p j` have images whose difference is
a nonzero multiple of `(u,1)`. -/
noncomputable def badInjChartsI {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    {k : ℕ} (f : M → EuclideanSpace ℝ (Fin (k+1))) (p : ℕ → M) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  {u | ∃ i j, ∃ y ∈ (extChartAt I (p i)).target, ∃ z ∈ (extChartAt I (p j)).target,
        (chartRepI (I := I) f (p i) y - chartRepI (I := I) f (p j) z) (Fin.last k) ≠ 0 ∧
        extract (chartRepI (I := I) f (p i) y - chartRepI (I := I) f (p j) z) = u}

/-- Every injectivity-bad direction occurs as the value of the parametrisation of the bad set of
one of the pairs of charts. -/
lemma badInjChartsI_subset {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] {k : ℕ}
    (f : M → EuclideanSpace ℝ (Fin (k+1))) (p : ℕ → M) :
    badInjChartsI (I := I) f p ⊆
      ⋃ i, ⋃ j, injParamI (I := I) f (p i) (p j) '' (injDomI (I := I) f (p i) (p j)) := by
  rintro u ⟨i, j, y, hy, z, hz, hlast, hext⟩
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ?_⟩⟩
  exact ⟨(y, z), ⟨hy, hz, hlast⟩, hext⟩

/-- When `I` is boundaryless, `fderivWithin ℝ g (Set.range I)` is `fderiv ℝ g`. -/
@[simp]
lemma fderivWithin_range_I {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [I.Boundaryless] (g : E → F) (y : E) :
    fderivWithin ℝ g (Set.range I) y = fderiv ℝ g y := by
  rw [I.range_eq_univ, fderivWithin_univ]

end Defs

end Work.Projection
