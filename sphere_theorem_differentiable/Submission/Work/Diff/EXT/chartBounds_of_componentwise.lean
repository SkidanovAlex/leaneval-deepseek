import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.LocalExtDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.EXT.chartBounds_of_componentwise`

The chart matrix `y ↦ chartMat G x₀ t y` of a family of metrics takes its values in the
finite-dimensional space

`MatE = Fin n → Fin n → ℝ`,  `n = finrank ℝ E`,

whose norm is the supremum norm (`pi_norm_le_iff_of_nonneg`).  Consequently a bound on the `k`-th
Fréchet derivative of every *component* `y ↦ chartMat G x₀ t y i j` gives a bound on the norm of
the `k`-th Fréchet derivative of the matrix-valued function itself: the derivative of a
product-valued function is the product of the derivatives of its components
(`ContinuousLinearMap.iteratedFDeriv_comp_left`, applied to the projections `MatE →L ℝ`), and on a
finite product the norm is bounded by the sum of the norms of the components.

This is the content of the requested lemma `chartBounds_of_componentwise`: the hypothesis
`hcomp` bounds all components on `K`, and the conclusion bounds the full jet on
`interior K ⊆ K`.  Note that the exponents of `ℕ∞ω` matter here: `(⊤ : ℕ∞)` coerces to the
*smooth* order `∞`, which is all that the iterated derivatives require.
-/

namespace Work.Diff.EXT

open scoped ContDiff
open Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A continuous multilinear map into a finite product is bounded by the sum of the norms of its
components.** -/
lemma norm_le_sum_proj_comp {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {k : ℕ} (Φ : E [×k]→L[ℝ] ((i : ι) → F i)) :
    ‖Φ‖ ≤ ∑ i, ‖(ContinuousLinearMap.proj i).compContinuousMultilinearMap Φ‖ := by
  rw [ContinuousMultilinearMap.opNorm_le_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)]
  intro m
  have h1 : ‖Φ m‖
      ≤ ∑ i, ‖((ContinuousLinearMap.proj i).compContinuousMultilinearMap Φ) m‖ := by
    rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    intro i
    -- `(Φ m) i` is the `i`-th summand
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
lemma norm_iteratedFDeriv_le_sum_components
    {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {f : E → ((i : ι) → F i)} {y : E} {k : ℕ} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f y)
    (hk : (k : ℕ∞ω) ≤ n) :
    ‖iteratedFDeriv ℝ k f y‖ ≤ ∑ i, ‖iteratedFDeriv ℝ k (fun z => f z i) y‖ := by
  have key : ∀ i : ι, iteratedFDeriv ℝ k (fun z => f z i) y
      = (ContinuousLinearMap.proj i).compContinuousMultilinearMap (iteratedFDeriv ℝ k f y) := by
    intro i
    have h := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
      (ContinuousLinearMap.proj i) hf (i := k) hk
    simpa [Function.comp_def] using h
  simp only [key]
  exact norm_le_sum_proj_comp (iteratedFDeriv ℝ k f y)

/-- The `i`-th component of a smooth product-valued function is smooth. -/
lemma contDiffAt_apply_of_contDiffAt_pi {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    {f : E → ((i : ι) → F i)} {y : E} {n : ℕ∞ω} (hf : ContDiffAt ℝ n f y) (i : ι) :
    ContDiffAt ℝ n (fun z => f z i) y := by
  have hproj : ContDiffAt ℝ n (ContinuousLinearMap.proj (φ := F) i) (f y) :=
    (ContinuousLinearMap.contDiff _).contDiffAt
  have h := hproj.comp y hf
  simpa [Function.comp_def, ContinuousLinearMap.proj_apply] using h

/-- Pointwise form of the requested lemma: the componentwise bounds for a single `t` and `y`
give the norm bound for the full matrix-valued jet. -/
lemma norm_iteratedFDeriv_chartMat_le [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (G : ℝ → Submission.Diff.SMet I M) (x₀ : M) (t : ℝ) (y : E) (k : ℕ) (C : ℝ)
    (hsm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => chartMat (I := I) (M := M) G x₀ t y') y)
    (hC : ∀ i j : Fin (Module.finrank ℝ E),
      ‖iteratedFDeriv ℝ k (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun y' : E => chartMat (I := I) (M := M) G x₀ t y') y‖
      ≤ ∑ _ : Fin (Module.finrank ℝ E), ∑ _ : Fin (Module.finrank ℝ E), C := by
  have hk : (k : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by simp
  calc ‖iteratedFDeriv ℝ k (fun y' : E => chartMat (I := I) (M := M) G x₀ t y') y‖
      ≤ ∑ i, ‖iteratedFDeriv ℝ k
          (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i) y‖ :=
        norm_iteratedFDeriv_le_sum_components hsm hk
    _ ≤ ∑ i, ∑ j, ‖iteratedFDeriv ℝ k
          (fun y' : E => chartMat (I := I) (M := M) G x₀ t y' i j) y‖ :=
        Finset.sum_le_sum fun i _ =>
          norm_iteratedFDeriv_le_sum_components (contDiffAt_apply_of_contDiffAt_pi hsm i) hk
    _ ≤ ∑ _ : Fin (Module.finrank ℝ E), ∑ _ : Fin (Module.finrank ℝ E), C :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hC i j

theorem chartBounds_of_componentwise
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKin : (extChartAt I x₀) x₀ ∈ interior K)
    (hsm : ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ContDiffAt ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y)
    (hcomp : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ i j : Fin (Module.finrank ℝ E),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y' i j) y‖ ≤ C) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ interior K,
      ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.EXT.chartMat (I := I) (M := M) G x₀ t y') y‖ ≤ C := by
  intro k
  obtain ⟨C, hC0, hC⟩ := hcomp k
  refine ⟨∑ _ : Fin (Module.finrank ℝ E), ∑ _ : Fin (Module.finrank ℝ E), C, ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hC0
  · intro t ht y hy
    exact norm_iteratedFDeriv_chartMat_le (I := I) (M := M) G x₀ t y k C
      (hsm t ht y (interior_subset hy)) fun i j => hC t ht y (interior_subset hy) i j

end Work.Diff.EXT
