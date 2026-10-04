import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.chartcalc
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.EXT.chartData_contDiffOn

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for `Work.Diff.EXT.chartMat_bounds_of_christoffel_bounds`

Fixed chart centre `x₀ : M` and model space `E` with `n = finrank ℝ E`.

* `cmMatEntry G x₀ t i j : E → ℝ` is the `(i,j)` component of the chart matrix
  `y ↦ chartMat G x₀ t y` as a function of the chart coordinate;
* `cGamEntry G x₀ t p i j : E → ℝ` is the chart Christoffel entry `Γ^p_{ij}` read at
  `(extChartAt I x₀).symm y`;
* `chartCoef G x₀ t i j m : E → ℝ` is the coefficient of the coordinate differential
  `dy^m` in the first derivative of `cmMatEntry G x₀ t i j`, i.e. the right hand side of the
  metric-compatibility identity `∂_m g_{ij} = Σ_p (Γ^p_{mi} g_{pj} + Γ^p_{mj} g_{ip})`;
* `coordExpCLM` is the continuous linear map `c ↦ ∑ m, c m • φ_m` from the coordinate space
  `Fin n → ℝ` to the dual `E →L[ℝ] ℝ` used to expand a differential form in the basis.
-/

set_option linter.unusedSectionVars false

namespace Work.Diff.EXT

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [I.Boundaryless] [T2Space M]

/-- The `(i,j)` component of the chart matrix of the family `G`, as a function of the chart
coordinate. -/
noncomputable abbrev cmMatEntry (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartMat (I := I) (M := M) G x₀ t y i j

/-- The chart Christoffel entry, as a function of the chart coordinate. -/
noncomputable abbrev cGamEntry (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (p i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => Work.Diff.GE.cGam (G t) x₀ (pt (I := I) x₀ y) p i j

/-- The coefficient of `dy^m` in the first derivative of the chart matrix component `(i,j)`. -/
noncomputable abbrev chartCoef (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ)
    (i j m : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => ∑ p : Fin (Module.finrank ℝ E),
    (cGamEntry (I := I) (M := M) G x₀ t p m i y * cmMatEntry (I := I) (M := M) G x₀ t p j y
      + cGamEntry (I := I) (M := M) G x₀ t p m j y * cmMatEntry (I := I) (M := M) G x₀ t i p y)

/-- The expansion of a family of coordinates in the basis of the model space, as a continuous
linear map `(Fin n → ℝ) →L[ℝ] (E →L[ℝ] ℝ)`. -/
noncomputable def coordExpCLM : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
  ∑ m : Fin (Module.finrank ℝ E),
    (ContinuousLinearMap.proj m).smulRight
      ((Module.finBasis ℝ E).coord m).toContinuousLinearMap

lemma coordExpCLM_apply (c : Fin (Module.finrank ℝ E) → ℝ) :
    coordExpCLM (E := E) c
      = ∑ m : Fin (Module.finrank ℝ E),
          c m • ((Module.finBasis ℝ E).coord m).toContinuousLinearMap := by
  simp [coordExpCLM]


/-! ## Bounding a product-valued function by the sum of its components

These two lemmas are the finite-product packaging step: the `k`-th Fréchet derivative of a function
with values in a finite product is bounded by the sum of the `k`-th derivatives of the components
(the projections are `1`-Lipschitz in the supremum norm, and the norm of a tuple is at most the sum
of the norms of its entries). -/

/-- **A continuous multilinear map into a finite product is bounded by the sum of the norms of its
components.** -/
lemma norm_le_sum_proj_comp_pi
    {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {k : ℕ} (Φ : E [×k]→L[ℝ] ((i : ι) → F i)) :
    ‖Φ‖ ≤ ∑ i, ‖(ContinuousLinearMap.proj i).compContinuousMultilinearMap Φ‖ := by
  rw [ContinuousMultilinearMap.opNorm_le_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)]
  intro m
  have h1 : ‖Φ m‖
      ≤ ∑ i, ‖((ContinuousLinearMap.proj i).compContinuousMultilinearMap Φ) m‖ := by
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    intro i
    simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.proj_apply]
    exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  calc ‖Φ m‖ ≤ ∑ i, ‖((ContinuousLinearMap.proj i).compContinuousMultilinearMap Φ) m‖ := h1
    _ ≤ ∑ i, ‖(ContinuousLinearMap.proj i).compContinuousMultilinearMap Φ‖ * ∏ s, ‖m s‖ :=
        Finset.sum_le_sum fun i _ => ContinuousMultilinearMap.le_opNorm _ m
    _ = (∑ i, ‖(ContinuousLinearMap.proj i).compContinuousMultilinearMap Φ‖) * ∏ s, ‖m s‖ :=
        (Finset.sum_mul ..).symm

/-- **The `k`-th jet of a product-valued function is bounded by the sum of the `k`-jets of its
components.** -/
lemma norm_iteratedFDeriv_pi_le_sum_gen
    {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {f : E → ((i : ι) → F i)} {y : E} {k : ℕ} {N : ℕ∞ω} (hf : ContDiffAt ℝ N f y)
    (hk : (k : ℕ∞ω) ≤ N) :
    ‖iteratedFDeriv ℝ k f y‖ ≤ ∑ i, ‖iteratedFDeriv ℝ k (fun z => f z i) y‖ := by
  have key : ∀ i : ι, iteratedFDeriv ℝ k (fun z => f z i) y
      = (ContinuousLinearMap.proj i).compContinuousMultilinearMap (iteratedFDeriv ℝ k f y) := by
    intro i
    have h := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
      (ContinuousLinearMap.proj i) hf (i := k) hk
    simpa [Function.comp_def] using h
  simp only [key]
  exact norm_le_sum_proj_comp_pi (iteratedFDeriv ℝ k f y)

end Work.Diff.EXT
