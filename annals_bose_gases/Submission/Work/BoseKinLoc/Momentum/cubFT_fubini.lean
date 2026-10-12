import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseKinLoc.Momentum.cubFT_1d
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Fubini over `ℝ³ = EuclideanSpace ℝ (Fin 3)` for functions of a single coordinate

`EuclideanSpace ℝ (Fin 3)` is `WithLp 2 (Fin 3 → ℝ)`, i.e. a type synonym for `Fin 3 → ℝ` with a
different (but volume preserving) measurable structure, so Mathlib's product-measure Fubini lemmas
do not apply syntactically.  This module transfers them once and for all along the volume-preserving
measurable equivalence `MeasurableEquiv.toLp 2 (Fin 3 → ℝ)`.

The consequences used by the cube-Fourier estimates are

* `integral_euclidean_prod`, `integral_euclidean_prod_real`:
  `∫ x, ∏ i, f i (x i) = ∏ i, ∫ s, f i s`;
* `setIntegral_pi_prod`: the same for the product set `{x | ∀ i, x i ∈ s i}`;
* `setIntegral_acube_prod`: the special case `s i = [-1/2,1/2]`, i.e. `acube 1`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false

/-- Membership in the unit cube `acube 1`, in the coordinate spelling used by the 1D factors. -/
lemma mem_acube_one (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ acube 1 ↔ ∀ i, x i ∈ Set.Icc (-(1/2)) (1/2) := by
  simp [acube, neg_div]

/-- **Fubini for `ℝ³`** (complex-valued version): a product of functions of a single coordinate
integrates to the product of the 1D integrals. -/
theorem integral_euclidean_prod (f : Fin 3 → ℝ → ℂ) :
    ∫ x : EuclideanSpace ℝ (Fin 3), ∏ i, f i (x i) = ∏ i, ∫ s : ℝ, f i s := by
  have h := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))
  have hg : (fun x : EuclideanSpace ℝ (Fin 3) =>
      ∏ i, f i (((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm) x i)) =
      (fun x : EuclideanSpace ℝ (Fin 3) => ∏ i, f i (x i)) := by funext x; rfl
  rw [← hg, h.integral_comp' (fun y : Fin 3 → ℝ => ∏ i, f i (y i))]
  exact MeasureTheory.integral_fintype_prod_volume_eq_prod f

/-- **Fubini for `ℝ³`** (real-valued version). -/
theorem integral_euclidean_prod_real (f : Fin 3 → ℝ → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin 3), ∏ i, f i (x i) = ∏ i, ∫ s : ℝ, f i s := by
  have h := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))
  have hg : (fun x : EuclideanSpace ℝ (Fin 3) =>
      ∏ i, f i (((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm) x i)) =
      (fun x : EuclideanSpace ℝ (Fin 3) => ∏ i, f i (x i)) := by funext x; rfl
  rw [← hg, h.integral_comp' (fun y : Fin 3 → ℝ => ∏ i, f i (y i))]
  exact MeasureTheory.integral_fintype_prod_volume_eq_prod f

/-- **Fubini for `ℝ³` on a product set**: the integral over `{x | ∀ i, x i ∈ s i}` of a product of
functions of single coordinates is the product of the 1D set integrals. -/
theorem setIntegral_pi_prod {s : Fin 3 → Set ℝ} (hs : ∀ i, MeasurableSet (s i))
    (g : Fin 3 → ℝ → ℂ) :
    ∫ x in {y : EuclideanSpace ℝ (Fin 3) | ∀ i, y i ∈ s i}, ∏ i, g i (x i)
      = ∏ i, ∫ t in s i, g i t := by
  have hms : MeasurableSet {y : EuclideanSpace ℝ (Fin 3) | ∀ i, y i ∈ s i} := by
    have h1 : {y : EuclideanSpace ℝ (Fin 3) | ∀ i, y i ∈ s i}
        = WithLp.ofLp ⁻¹' {f : Fin 3 → ℝ | ∀ i, f i ∈ s i} := rfl
    rw [h1]
    refine MeasurableSet.preimage ?_ (WithLp.measurable_ofLp 2 (Fin 3 → ℝ))
    convert MeasurableSet.iInter (fun i => (measurable_pi_apply i) (hs i)) using 1
    ext f; simp
  rw [← integral_indicator hms]
  · have h_point : ({y : EuclideanSpace ℝ (Fin 3) | ∀ i, y i ∈ s i}).indicator
        (fun x : EuclideanSpace ℝ (Fin 3) => ∏ i, g i (x i))
        = fun x : EuclideanSpace ℝ (Fin 3) =>
            ∏ i, (s i).indicator (g i) (x i) := by
      funext x
      by_cases hx : ∀ i, x i ∈ s i
      · rw [Set.indicator_of_mem (s := {y : EuclideanSpace ℝ (Fin 3) | ∀ i, y i ∈ s i}) hx
          (fun x : EuclideanSpace ℝ (Fin 3) => ∏ i, g i (x i))]
        exact (Finset.prod_congr rfl fun i _ => Set.indicator_of_mem (hx i) (g i)).symm
      · rw [Set.indicator_of_notMem (s := {y : EuclideanSpace ℝ (Fin 3) | ∀ i, y i ∈ s i}) hx
          (fun x : EuclideanSpace ℝ (Fin 3) => ∏ i, g i (x i))]
        obtain ⟨i, hi⟩ := not_forall.mp hx
        exact (Finset.prod_eq_zero (Finset.mem_univ i)
          (Set.indicator_of_notMem hi (g i))).symm
    rw [h_point, integral_euclidean_prod]
    exact Finset.prod_congr rfl fun i _ =>
      (MeasureTheory.integral_indicator (hs i))

/-- **Fubini for `ℝ³` on the unit cube** `acube 1 = [-1/2,1/2]³`. -/
theorem setIntegral_acube_prod (g : Fin 3 → ℝ → ℂ) :
    ∫ x in acube 1, ∏ i, g i (x i) = ∏ i, ∫ t in Set.Icc (-(1/2)) (1/2), g i t := by
  have hset : acube (1 : ℝ) = {y : EuclideanSpace ℝ (Fin 3) |
      ∀ i, y i ∈ Set.Icc (-(1/2)) (1/2)} := by
    ext y; exact mem_acube_one y
  rw [hset]
  exact setIntegral_pi_prod (fun _ => measurableSet_Icc) g

end Work.BoseKinLoc.Momentum
