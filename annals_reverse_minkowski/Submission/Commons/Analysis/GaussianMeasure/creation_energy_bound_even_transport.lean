import Mathlib
import Submission.Commons.Analysis.GaussianMeasure.brascamp_lieb_truncated
import Submission.Commons.Analysis.InnerProductSpace.fderiv_fderiv_comp_linearIsometryEquiv

open MeasureTheory
open scoped BigOperators

namespace Commons.Analysis.GaussianMeasure

/-- Laplacian invariance under a linear isometry equivalence:
the Laplacian of `y ↦ g (e.symm y)` at `e x` is the Laplacian of `g` at `x`. -/
theorem laplacian_comp_linearIsometryEquiv {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (g : E → ℝ) (hg : ContDiff ℝ 2 g) (x : E) :
    Laplacian.laplacian (fun y : F => g (e.symm y)) (e x) = Laplacian.laplacian g x := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  let b' : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ F := b.map e
  have h1 : Laplacian.laplacian (fun y : F => g (e.symm y)) (e x)
      = ∑ i, fderiv ℝ (fderiv ℝ (fun y : F => g (e.symm y))) (e x) (b' i) (b' i) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (fun y : F => g (e.symm y)) b']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedFDeriv_two_apply]
    simp
  have h2 : Laplacian.laplacian g x
      = ∑ i, fderiv ℝ (fderiv ℝ g) x (b i) (b i) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g b]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [iteratedFDeriv_two_apply]
    simp
  rw [h1, h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hbi : b' i = e (b i) := OrthonormalBasis.map_apply b e i
  have hconv : e.symm (b' i) = b i := by rw [hbi, e.symm_apply_apply]
  rw [Commons.Analysis.InnerProductSpace.fderiv_fderiv_comp_linearIsometryEquiv e.symm g hg (e x)
      (b' i) (b' i), e.symm_apply_apply x, hconv]


theorem creation_energy_bound_even_transport (H : ∀ (n : ℕ) (f u : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ 2 f → (∀ x, f (-x) = f x) → (∀ x v : EuclideanSpace ℝ (Fin n), 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) → ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2) → (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n), |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) → ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → (∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n), |u x| ≤ C * (1 + ‖x‖) ^ N ∧ |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ u) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) → 4 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x))) ≤ (∫ x, (- Laplacian.laplacian u x + inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ f x)) ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x)))) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] (f u : E → ℝ) (hf : ContDiff ℝ 2 f) (hfe : ∀ x, f (-x) = f x) (hH : ∀ x v : E, 2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ f) x v v) (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) (hgf : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E, |fderiv ℝ f x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ f) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) (hu : ContDiff ℝ 2 u) (hueven : ∀ x, u (-x) = u x) (hgu : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : E, |u x| ≤ C * (1 + ‖x‖) ^ N ∧ |fderiv ℝ u x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧ |fderiv ℝ (fderiv ℝ u) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2) : 4 * Real.pi * (∫ x, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x))) ≤ (∫ x, (- Laplacian.laplacian u x + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x))) := by
  classical
  let k : ℕ := Module.finrank ℝ E
  let e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) := (stdOrthonormalBasis ℝ E).repr
  let g : EuclideanSpace ℝ (Fin k) → ℝ := fun y => f (e.symm y)
  let h : EuclideanSpace ℝ (Fin k) → ℝ := fun y => u (e.symm y)
  have hf' : ContDiff ℝ 2 g := hf.comp e.symm.contDiff
  have hfe' : ∀ y, g (-y) = g y := by
    intro y
    show f (e.symm (-y)) = f (e.symm y)
    rw [map_neg, hfe]
  have hH' : ∀ y v : EuclideanSpace ℝ (Fin k),
      2 * Real.pi * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ g) y v v := by
    intro y v
    have h1 : fderiv ℝ (fderiv ℝ g) y v v
        = fderiv ℝ (fderiv ℝ f) (e.symm y) (e.symm v) (e.symm v) := by
      show fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin k) => f (e.symm y))) y v v = _
      exact Commons.Analysis.InnerProductSpace.fderiv_fderiv_comp_linearIsometryEquiv e.symm f hf y v v
    rw [h1]
    have h2 := hH (e.symm y) (e.symm v)
    rwa [e.symm.norm_map v] at h2
  have hconv' : ConvexOn ℝ Set.univ (fun y => g y - Real.pi * ‖y‖ ^ 2) := by
    show ConvexOn ℝ Set.univ
      (fun y : EuclideanSpace ℝ (Fin k) => f (e.symm y) - Real.pi * ‖y‖ ^ 2)
    exact convexOn_comp_linearIsometryEquiv e.symm f hconv
  have hgf' : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin k),
      |fderiv ℝ g x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ g) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2 := by
    obtain ⟨C, hC0, N, hCN⟩ := hgf
    refine ⟨C, hC0, N, fun y v => ⟨?_, ?_⟩⟩
    · have h1 : (fderiv ℝ g y) v = (fderiv ℝ f (e.symm y)) (e.symm v) := by
        show (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin k) => f (e.symm z)) y) v = _
        exact fderiv_comp_isometry_apply e.symm f y
          (hf.contDiffAt.differentiableAt (by norm_num)) v
      rw [h1]
      have h3 := (hCN (e.symm y) (e.symm v)).1
      have h4 : (1 + ‖e.symm y‖) ^ N = (1 + ‖y‖) ^ N := by rw [e.symm.norm_map]
      have h5 : ‖e.symm v‖ = ‖v‖ := e.symm.norm_map v
      rwa [h4, h5] at h3
    · have h1 : (fderiv ℝ (fderiv ℝ g) y) v v
          = (fderiv ℝ (fderiv ℝ f) (e.symm y)) (e.symm v) (e.symm v) := by
        show (fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin k) => f (e.symm z))) y) v v = _
        exact Commons.Analysis.InnerProductSpace.fderiv_fderiv_comp_linearIsometryEquiv e.symm f hf y v v
      rw [h1]
      have h3 := (hCN (e.symm y) (e.symm v)).2
      have h4 : (1 + ‖e.symm y‖) ^ N = (1 + ‖y‖) ^ N := by rw [e.symm.norm_map]
      have h5 : ‖e.symm v‖ = ‖v‖ := e.symm.norm_map v
      rwa [h4, h5] at h3
  have hu' : ContDiff ℝ 2 h := hu.comp e.symm.contDiff
  have hue' : ∀ y, h (-y) = h y := by
    intro y
    show u (e.symm (-y)) = u (e.symm y)
    rw [map_neg, hueven]
  have hgu' : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin k),
      |h x| ≤ C * (1 + ‖x‖) ^ N ∧
      |fderiv ℝ h x v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ h) x v v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2 := by
    obtain ⟨C, hC0, N, hCN⟩ := hgu
    refine ⟨C, hC0, N, fun y v => ⟨?_, ?_, ?_⟩⟩
    · show |u (e.symm y)| ≤ C * (1 + ‖y‖) ^ N
      have h3 := (hCN (e.symm y) (e.symm v)).1
      have h4 : (1 + ‖e.symm y‖) ^ N = (1 + ‖y‖) ^ N := by rw [e.symm.norm_map]
      rwa [h4] at h3
    · have h1 : (fderiv ℝ h y) v = (fderiv ℝ u (e.symm y)) (e.symm v) := by
        show (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin k) => u (e.symm z)) y) v = _
        exact fderiv_comp_isometry_apply e.symm u y
          (hu.contDiffAt.differentiableAt (by norm_num)) v
      rw [h1]
      have h3 := (hCN (e.symm y) (e.symm v)).2.1
      have h4 : (1 + ‖e.symm y‖) ^ N = (1 + ‖y‖) ^ N := by rw [e.symm.norm_map]
      have h5 : ‖e.symm v‖ = ‖v‖ := e.symm.norm_map v
      rwa [h4, h5] at h3
    · have h1 : (fderiv ℝ (fderiv ℝ h) y) v v
          = (fderiv ℝ (fderiv ℝ u) (e.symm y)) (e.symm v) (e.symm v) := by
        show (fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin k) => u (e.symm z))) y) v v = _
        exact Commons.Analysis.InnerProductSpace.fderiv_fderiv_comp_linearIsometryEquiv e.symm u hu y v v
      rw [h1]
      have h3 := (hCN (e.symm y) (e.symm v)).2.2
      have h4 : (1 + ‖e.symm y‖) ^ N = (1 + ‖y‖) ^ N := by rw [e.symm.norm_map]
      have h5 : ‖e.symm v‖ = ‖v‖ := e.symm.norm_map v
      rwa [h4, h5] at h3
  have hmain := H k g h hf' hfe' hH' hconv' hgf' hu' hue' hgu'
  have hLpt : ∀ x : E, ‖fderiv ℝ h (e x)‖ ^ 2 * Real.exp (-(g (e x)))
      = ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)) := by
    intro x
    have hgx : grad h (e x) = e (grad u x) := by
      change grad (fun y : EuclideanSpace ℝ (Fin k) => u (e.symm y)) (e x) = e (grad u x)
      rw [grad_comp_isometry e.symm u (e x) (hu.contDiffAt.differentiableAt (by norm_num)),
        LinearIsometryEquiv.symm_symm, e.symm_apply_apply x]
    have hnorm : ‖fderiv ℝ h (e x)‖ = ‖fderiv ℝ u x‖ := by
      rw [← grad_norm_eq h (e x), hgx, e.norm_map, grad_norm_eq u x]
    have hgx' : g (e x) = f x := by
      show f (e.symm (e x)) = f x
      rw [e.symm_apply_apply]
    rw [hnorm, hgx']
  have hRpt : ∀ x : E,
      (- Laplacian.laplacian h (e x) + inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (fderiv ℝ g (e x))) ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (fderiv ℝ h (e x)))) ^ 2 * Real.exp (-(g (e x)))
      = (- Laplacian.laplacian u x + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x)) := by
    intro x
    have hl : Laplacian.laplacian h (e x) = Laplacian.laplacian u x := by
      show Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin k) => u (e.symm y)) (e x)
        = Laplacian.laplacian u x
      exact laplacian_comp_linearIsometryEquiv e u hu x
    have hgf1 : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (fderiv ℝ g (e x))
        = e ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) := by
      change grad (fun y : EuclideanSpace ℝ (Fin k) => f (e.symm y)) (e x) = e (grad f x)
      rw [grad_comp_isometry e.symm f (e x) (hf.contDiffAt.differentiableAt (by norm_num)),
        LinearIsometryEquiv.symm_symm, e.symm_apply_apply x]
    have hgu1 : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (fderiv ℝ h (e x))
        = e ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)) := by
      change grad (fun y : EuclideanSpace ℝ (Fin k) => u (e.symm y)) (e x) = e (grad u x)
      rw [grad_comp_isometry e.symm u (e x) (hu.contDiffAt.differentiableAt (by norm_num)),
        LinearIsometryEquiv.symm_symm, e.symm_apply_apply x]
    have hgx' : g (e x) = f x := by
      show f (e.symm (e x)) = f x
      rw [e.symm_apply_apply]
    rw [hl, hgf1, hgu1, e.inner_map_map, hgx']
  have hL : (∫ x : E, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
      = ∫ y : EuclideanSpace ℝ (Fin k), ‖fderiv ℝ h y‖ ^ 2 * Real.exp (-(g y)) := by
    calc (∫ x : E, ‖fderiv ℝ u x‖ ^ 2 * Real.exp (-(f x)))
        = ∫ x : E,
            (fun y : EuclideanSpace ℝ (Fin k) => ‖fderiv ℝ h y‖ ^ 2 * Real.exp (-(g y))) (e x) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          exact (hLpt x).symm
      _ = ∫ y : EuclideanSpace ℝ (Fin k), ‖fderiv ℝ h y‖ ^ 2 * Real.exp (-(g y)) :=
          integral_comp_isometry e
            (fun y : EuclideanSpace ℝ (Fin k) => ‖fderiv ℝ h y‖ ^ 2 * Real.exp (-(g y)))
  have hR : (∫ y : EuclideanSpace ℝ (Fin k),
        (- Laplacian.laplacian h y + inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (fderiv ℝ g y)) ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (fderiv ℝ h y))) ^ 2 * Real.exp (-(g y)))
      = ∫ x : E,
        (- Laplacian.laplacian u x + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x)) := by
    calc (∫ y : EuclideanSpace ℝ (Fin k),
          (- Laplacian.laplacian h y + inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (fderiv ℝ g y)) ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (fderiv ℝ h y))) ^ 2 * Real.exp (-(g y)))
        = ∫ x : E, (fun y : EuclideanSpace ℝ (Fin k) =>
            (- Laplacian.laplacian h y + inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (fderiv ℝ g y)) ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (fderiv ℝ h y))) ^ 2 * Real.exp (-(g y))) (e x) :=
          (integral_comp_isometry e (fun y : EuclideanSpace ℝ (Fin k) =>
            (- Laplacian.laplacian h y + inner ℝ ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (fderiv ℝ g y)) ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm (fderiv ℝ h y))) ^ 2 * Real.exp (-(g y)))).symm
      _ = ∫ x : E,
          (- Laplacian.laplacian u x + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ^ 2 * Real.exp (-(f x)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          exact hRpt x
  rw [← hL] at hmain
  rw [hR] at hmain
  exact hmain



end Commons.Analysis.GaussianMeasure
