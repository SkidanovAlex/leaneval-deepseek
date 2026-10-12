import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxC1_add_cnPlus
import Submission.Work.FockBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

open MeasureTheory
open scoped Real BigOperators ENNReal

set_option maxHeartbeats 800000

theorem boxFlat_add_boxQ_eq_card {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {k : ℕ} {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hsec : Φ = Work.FockBridge.sectorPiece A k Φ) :
    Work.BoseFixB1S.boxFlatCount volA ℓ A Φ + Work.BoseFixB1S.boxQCount volA ℓ A Φ
      = (k : ℝ) * ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
  classical
  -- ## Step 1: the per-slot Parseval splitting, summed over the slots
  have hsum : Work.BoseFixB1S.boxFlatCount volA ℓ A Φ + Work.BoseFixB1S.boxQCount volA ℓ A Φ
      = ∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 := by
    rw [Work.BoseFixB1S.boxFlatCount, Work.BoseFixB1S.boxQCount, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ =>
      Work.BoseFixB1S.boxPInd_sq_add_boxQInd_sq hℓ hA hvolA hAc i hΦc)
  -- ## Step 2: integrability of the per-slot densities on the (compact) box
  have hint : ∀ i : Fin N, IntegrableOn (fun x : Submission.BoseGases.X N =>
      A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
        (Submission.BoseGases.abox N ℓ) volume := by
    intro i
    obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
    have hmeas : Measurable (fun x : Submission.BoseGases.X N =>
        A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x) :=
      ((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul hΦc.measurable
    have hb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ C := by
      intro x hx
      have hx1 : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
        by_cases h : x i ∈ A <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
      have hx2 : |Φ x| ≤ C := by
        have h := hC x hx
        rwa [Real.norm_eq_abs] at h
      calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
          = |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| := abs_mul _ _
        _ ≤ 1 * C := mul_le_mul hx1 hx2 (abs_nonneg _) zero_le_one
        _ = C := one_mul C
    have hsq := Work.BoseFixB1S.integrableOn_sq_of_bound (N := N) hℓ hmeas hb
    refine hsq.congr ?_
    filter_upwards with x
    by_cases h : x i ∈ A
    · rw [Set.indicator_of_mem h]; ring
    · rw [Set.indicator_of_notMem h]; ring
  -- ## Step 3: exchange the slot sum with the box integral
  rw [hsum]
  have hswap : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          ∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 := by
    rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
  rw [hswap]
  -- ## Step 4: pointwise, the slot sum is `n_A(x)·Φ² = k·Φ²` on the sector
  have hpt : ∀ x : Submission.BoseGases.X N,
      (∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
        = (k : ℝ) * (Φ x) ^ 2 := by
    intro x
    rw [← Finset.sum_mul, ← Work.FockBridge.boxCount_eq_sum_indicator A x]
    by_cases hx : x ∈ Work.FockBridge.sectorSet A k
    · rw [Work.FockBridge.boxCount_eq_of_mem_sectorSet A hx]
    · have hz : Φ x = 0 := by
        rw [congrFun hsec x, Work.FockBridge.sectorPiece]
        exact Set.indicator_of_notMem (M := ℝ) hx Φ
      rw [hz]; ring
  rw [show (fun x : Submission.BoseGases.X N =>
        ∑ i : Fin N, A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
      = fun x => (k : ℝ) * (Φ x) ^ 2 from funext hpt, MeasureTheory.integral_const_mul]

end Work.BoseFixB1B
