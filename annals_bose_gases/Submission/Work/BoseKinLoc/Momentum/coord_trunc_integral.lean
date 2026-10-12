import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseKinLoc.Momentum.cubFT_fubini
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Fubini over `ℝ³` with one truncated coordinate

Given functions `f j : ℝ → ℝ` of a single coordinate and a distinguished index `i`, the product
`∏ j, f j (q j)` factorises, so its integral over `EuclideanSpace ℝ (Fin 3)` is the product of the
one-dimensional integrals.  Here one of the factors is replaced by the truncation
`t ↦ if c < |t| then f i t else 0`, i.e. by the indicator of the exterior set `{u | c < |u|}`,
and the product over the remaining coordinates is peeled off with `Finset.mul_prod_erase`.

The main statement `coord_trunc_integral` is the special case needed for the momentum-localisation
estimates.

Note that no integrability hypothesis is needed: Mathlib's
`MeasureTheory.integral_fintype_prod_volume_eq_prod` is unconditional, and the junk value `0`
assigned to non-integrable functions is compatible on both sides.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Momentum

/-- **Fubini for `ℝ³` with the `i`-th coordinate peeled off.** -/
theorem integral_euclidean_prod_erase (g : Fin 3 → ℝ → ℝ) (i : Fin 3) :
    ∫ q : EuclideanSpace ℝ (Fin 3), g i (q i) * ∏ j ∈ Finset.univ.erase i, g j (q j)
      = (∫ t : ℝ, g i t) * ∏ j ∈ Finset.univ.erase i, (∫ t : ℝ, g j t) := by
  have hpt : (fun q : EuclideanSpace ℝ (Fin 3) =>
        g i (q i) * ∏ j ∈ Finset.univ.erase i, g j (q j))
      = fun q : EuclideanSpace ℝ (Fin 3) => ∏ j : Fin 3, g j (q j) := by
    funext q
    exact Finset.mul_prod_erase Finset.univ (fun j : Fin 3 => g j (q j)) (Finset.mem_univ i)
  rw [hpt, integral_euclidean_prod_real]
  exact (Finset.mul_prod_erase Finset.univ (fun j : Fin 3 => ∫ t : ℝ, g j t)
    (Finset.mem_univ i)).symm

/-- The anchored (`ite`) integral of a truncation equals the integral over the exterior set. -/
theorem integral_ite_abs_eq_setIntegral (f : ℝ → ℝ) (c : ℝ) :
    (∫ t : ℝ, (if c < |t| then f t else 0)) = ∫ t in {u : ℝ | c < |u|}, f t := by
  have hmeas : MeasurableSet {u : ℝ | c < |u|} :=
    measurableSet_lt measurable_const measurable_abs
  rw [← MeasureTheory.integral_indicator hmeas]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  by_cases h : c < |t| <;> simp [Set.indicator, h]

theorem coord_trunc_integral (f : Fin 3 → ℝ → ℝ) (i : Fin 3) (c : ℝ) :
    ∫ q : EuclideanSpace ℝ (Fin 3),
        (if c < |q i| then f i (q i) else 0) * ∏ j ∈ Finset.univ.erase i, f j (q j)
      = (∫ t in {u : ℝ | c < |u|}, f i t) * ∏ j ∈ Finset.univ.erase i, (∫ t : ℝ, f j t) := by
  set g : Fin 3 → ℝ → ℝ :=
    fun j t => if j = i then (if c < |t| then f i t else 0) else f j t with hg
  have hL : (∫ q : EuclideanSpace ℝ (Fin 3),
        (if c < |q i| then f i (q i) else 0) * ∏ j ∈ Finset.univ.erase i, f j (q j))
      = ∫ q : EuclideanSpace ℝ (Fin 3), g i (q i) * ∏ j ∈ Finset.univ.erase i, g j (q j) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with q
    have h1 : g i (q i) = (if c < |q i| then f i (q i) else 0) := by simp [hg]
    have h2 : (∏ j ∈ Finset.univ.erase i, g j (q j))
        = ∏ j ∈ Finset.univ.erase i, f j (q j) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [hg, hji]
    rw [h1, h2]
  rw [hL, integral_euclidean_prod_erase g i]
  congr 1
  · have hgi : (∫ t : ℝ, g i t) = ∫ t : ℝ, (if c < |t| then f i t else 0) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      simp [hg]
    rw [hgi, integral_ite_abs_eq_setIntegral]
  · refine Finset.prod_congr rfl fun j hj => ?_
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    simp [hg, hji]

end Work.BoseKinLoc.Momentum
