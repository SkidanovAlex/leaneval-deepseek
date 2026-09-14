import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

namespace Commons.Analysis.Convolution

/-- The topological support of the reflected translate `x ↦ k (y - x)` is contained in the
preimage of the topological support of `k` under the reflection `x ↦ y - x`. -/
theorem tsupport_comp_sub_subset {G β : Type*} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [Zero β] (k : G → β) (y : G) :
    tsupport (fun x => k (y - x)) ⊆ (fun x : G => y - x) ⁻¹' tsupport k :=
  tsupport_comp_subset_preimage k (continuous_const.sub continuous_id)

/-- Derivative of a left-translate `x ↦ k (y - x)` in terms of the derivative of `k`. -/
theorem fderiv_comp_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : E → ℝ) (y x : E) (hk : DifferentiableAt ℝ k (y - x)) :
    fderiv ℝ (fun x : E => k (y - x)) x = (fderiv ℝ k (y - x)).comp (-1 : E →L[ℝ] E) := by
  have h_sub : HasFDerivAt (fun x : E => y - x) (-1 : E →L[ℝ] E) x := by
    have h1 : HasFDerivAt (fun x : E => y - x) ((0 : E →L[ℝ] E) - 1) x :=
      (hasFDerivAt_const (x := x) y).sub (hasFDerivAt_id (x := x))
    simpa using h1
  exact (hk.hasFDerivAt.comp x h_sub).fderiv

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution in
theorem fderiv_moll_weakGrad {n : ℕ} (k u : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (s : Set (EuclideanSpace ℝ (Fin n)))
    (y : EuclideanSpace ℝ (Fin n))
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hks : HasCompactSupport k)
    (hu : LocallyIntegrable u volume) (hGint : LocallyIntegrable G volume)
    (hksupp : ∀ z ∈ tsupport k, (y - z) ∈ s)
    (hG : ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → tsupport φ ⊆ s →
      ∀ v : EuclideanSpace ℝ (Fin n),
      ∫ x, u x * (fderiv ℝ φ x) v = - ∫ x, φ x * ⟪G x, v⟫_ℝ) :
    ∀ v : EuclideanSpace ℝ (Fin n),
      (fderiv ℝ (fun y => ∫ t, u t * k (y - t) ∂volume) y) v
      = ∫ t, k (y - t) * ⟪G t, v⟫_ℝ ∂volume := by
  intro v
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by simp)
  have hkcont : Continuous (fderiv ℝ k) := hk.continuous_fderiv (by simp)
  -- Rewrite the mollification as a convolution.
  have hF_eq : MeasureTheory.convolution (𝕜 := ℝ) u k (ContinuousLinearMap.mul ℝ ℝ) volume
      = (fun y => ∫ t, u t * k (y - t) ∂volume) := by
    funext z
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
  -- Its total derivative, computed as a convolution.
  have hF1 : fderiv ℝ (fun y => ∫ t, u t * k (y - t) ∂volume)
      = fun z => MeasureTheory.convolution (𝕜 := ℝ) u (fderiv ℝ k)
          (ContinuousLinearMap.precompR (EuclideanSpace ℝ (Fin n))
            (ContinuousLinearMap.mul ℝ ℝ)) volume z := by
    funext z
    have h := hks.hasFDerivAt_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ) hu hk1 z
    rw [hF_eq] at h
    exact h.fderiv
  -- Evaluation of that derivative in direction `v`.
  have hderiv : (fderiv ℝ (fun y => ∫ t, u t * k (y - t) ∂volume) y) v
      = ∫ t, u t * ((fderiv ℝ k (y - t)) v) ∂volume := by
    rw [hF1]
    rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hu (hks.fderiv ℝ) hkcont y v]
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
  rw [hderiv]
  -- The reflected test function `φ x = k (y - x)`.
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun x : EuclideanSpace ℝ (Fin n) => k (y - x)) :=
    hk.comp (contDiff_const.sub contDiff_id)
  have hφ_supp : tsupport (fun x : EuclideanSpace ℝ (Fin n) => k (y - x)) ⊆ s := by
    intro x hx
    have h1 : x ∈ (fun x : EuclideanSpace ℝ (Fin n) => y - x) ⁻¹' tsupport k :=
      tsupport_comp_sub_subset k y hx
    simpa using hksupp (y - x) h1
  -- Pointwise identity between the two integrands.
  have key : ∀ t, u t * ((fderiv ℝ k (y - t)) v)
      = - (u t * ((fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => k (y - x)) t) v)) := by
    intro t
    have h1 : (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => k (y - x)) t) v
        = - ((fderiv ℝ k (y - t)) v) := by
      rw [fderiv_comp_sub k y t ((hk.differentiable (by simp)).differentiableAt)]
      simp
    rw [h1]
    ring
  calc ∫ t, u t * ((fderiv ℝ k (y - t)) v) ∂volume
      = ∫ t, - (u t * ((fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => k (y - x)) t) v)) ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall key)
    _ = - ∫ t, u t * ((fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => k (y - x)) t) v) ∂volume :=
        integral_neg _
    _ = - (- ∫ t, (fun x : EuclideanSpace ℝ (Fin n) => k (y - x)) t * ⟪G t, v⟫_ℝ ∂volume) := by
        rw [hG (fun x : EuclideanSpace ℝ (Fin n) => k (y - x)) hφ_smooth hφ_supp v]
    _ = ∫ t, k (y - t) * ⟪G t, v⟫_ℝ ∂volume := by
        rw [neg_neg]

end Commons.Analysis.Convolution