import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.decouple_defs

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory Finset
open scoped ENNReal BigOperators

set_option linter.unusedVariables false

/-- **Reduction to exact cardinalities.**  If the `2r`-th moment bound holds for the sums over the
`j`-element subsets of `S`, uniformly for all `j ≤ k`, then it holds for the sum over all subsets of
cardinality at most `k`, with the constant multiplied by `(k+1)^{2r}`.  The subsets of `S` of
cardinality at most `k` decompose as the disjoint union of the `j`-element subsets, `j ∈ range (k+1)`
(`Finset.sum_biUnion`); on each layer one uses the triangle inequality for `enorm`, the power-mean
inequality `ENNReal.rpow_sum_le_const_mul_sum_rpow`, `lintegral_mono`, `lintegral_finsetSum'`
(which needs `hfm`) and the monotonicity of the square function under `Pj ⊆ P≤k`. -/
theorem cardLe_bound {X : Type*} [MeasurableSpace X] {α : Type*} [DecidableEq α]
    (S : Finset α) (k r : ℕ) (hr : 1 ≤ r) (f : Finset α → X → ℂ) (μ : MeasureTheory.Measure X)
    {D : ℝ} (hD : 0 ≤ D)
    (hfm : ∀ A, A ⊆ S → A.card ≤ k → AEMeasurable (f A) μ)
    (hfix : ∀ j, j ≤ k →
      MeasureTheory.lintegral μ (fun x => enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2 * (r : ℝ)))
        ≤ ENNReal.ofReal D *
          MeasureTheory.lintegral μ (fun x => (∑ A ∈ S.powerset.filter (fun A => A.card = j), enorm (f A x) ^ (2 : ℝ)) ^ r)) :
    MeasureTheory.lintegral μ (fun x => enorm (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), f A x) ^ (2 * (r : ℝ)))
      ≤ ENNReal.ofReal (((k : ℝ) + 1) ^ (2 * r) * D) *
        MeasureTheory.lintegral μ (fun x => (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), enorm (f A x) ^ (2 : ℝ)) ^ r) := by
  classical
  have hr0 : (0:ℝ) ≤ 2*(r:ℝ) := by
    have : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    linarith
  have hr1 : (1:ℝ) ≤ 2*(r:ℝ) := by
    have : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
    linarith
  -- Decompose the sum over `S.powerset.filter (card ≤ k)` into its cardinality layers.
  have hsum : ∀ x, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), f A x)
      = ∑ j ∈ Finset.range (k+1), ∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x := by
    intro x
    have hUnion : (Finset.range (k+1)).biUnion (fun j => S.powerset.filter (fun A => A.card = j))
        = S.powerset.filter (fun A => A.card ≤ k) := by
      ext A
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
      constructor
      · rintro ⟨j, hj, hA, hcard⟩
        exact ⟨hA, by omega⟩
      · rintro ⟨hA, hcard⟩
        exact ⟨A.card, by omega, hA, rfl⟩
    have hDisj : (↑(Finset.range (k+1)) : Set ℕ).PairwiseDisjoint
        (fun j => S.powerset.filter (fun A => A.card = j)) := by
      intro j hj j' hj' hjj'
      rw [Function.onFun, Finset.disjoint_left]
      intro A hA hA'
      simp only [Finset.mem_filter] at hA hA'
      exact hjj' (hA.2.symm.trans hA'.2)
    rw [← hUnion]
    exact Finset.sum_biUnion hDisj
  -- Pointwise bound: triangle inequality, then the power-mean inequality on the `k+1` layers.
  have hpt : ∀ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), f A x) ^ (2*(r:ℝ))
      ≤ ((k:ℝ≥0∞) + 1) ^ (2*(r:ℝ) - 1) *
          ∑ j ∈ Finset.range (k+1), enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ)) := by
    intro x
    rw [hsum x]
    calc enorm (∑ j ∈ Finset.range (k+1), ∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ))
        ≤ (∑ j ∈ Finset.range (k+1), enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x)) ^ (2*(r:ℝ)) :=
          ENNReal.rpow_le_rpow (enorm_sum_le _ _) hr0
      _ ≤ ↑(#(Finset.range (k+1))) ^ (2*(r:ℝ) - 1) *
            ∑ j ∈ Finset.range (k+1), enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ)) :=
          ENNReal.rpow_sum_le_const_mul_sum_rpow _ _ hr1
      _ = ((k:ℝ≥0∞) + 1) ^ (2*(r:ℝ) - 1) *
            ∑ j ∈ Finset.range (k+1), enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ)) := by
          rw [Finset.card_range]; norm_num
  -- Measurability of the layer sums (needed for `lintegral_finsetSum'`).
  have hmea : ∀ j ∈ Finset.range (k+1),
      AEMeasurable (fun x => enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ))) μ := by
    intro j hj
    have hjk : j ≤ k := by simp only [Finset.mem_range] at hj; omega
    have hG : AEMeasurable (fun x => ∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) μ := by
      refine Finset.aemeasurable_fun_sum _ (fun A hA => ?_)
      simp only [Finset.mem_filter, Finset.mem_powerset] at hA
      exact hfm A hA.1 (by omega)
    exact (ENNReal.continuous_rpow_const (y := 2*(r:ℝ))).measurable.comp_aemeasurable hG.enorm
  have hsummea : AEMeasurable (fun x => ∑ j ∈ Finset.range (k+1), enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ))) μ :=
    Finset.aemeasurable_fun_sum _ hmea
  have hT : (∫⁻ x, ∑ j ∈ Finset.range (k+1), enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ)) ∂μ)
      = ∑ j ∈ Finset.range (k+1), ∫⁻ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ)) ∂μ :=
    lintegral_finsetSum' _ hmea
  have hstep1 : (∫⁻ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), f A x) ^ (2*(r:ℝ)) ∂μ)
      ≤ ((k:ℝ≥0∞) + 1) ^ (2*(r:ℝ) - 1) *
          ∫⁻ x, ∑ j ∈ Finset.range (k+1), enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ)) ∂μ := by
    calc ∫⁻ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), f A x) ^ (2*(r:ℝ)) ∂μ
        ≤ ∫⁻ x, (((k:ℝ≥0∞) + 1) ^ (2*(r:ℝ) - 1) * (∑ j ∈ Finset.range (k+1), enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ)))) ∂μ :=
          lintegral_mono hpt
      _ = ((k:ℝ≥0∞) + 1) ^ (2*(r:ℝ) - 1) * ∫⁻ x, ∑ j ∈ Finset.range (k+1), enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ)) ∂μ :=
          lintegral_const_mul'' _ hsummea
  -- Each layer is bounded by the hypothesis; the layer square functions are monotone in the layer.
  have hper : ∀ j ∈ Finset.range (k+1),
      (∫⁻ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ)) ∂μ)
        ≤ ENNReal.ofReal D * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), enorm (f A x) ^ (2:ℝ)) ^ r ∂μ := by
    intro j hj
    have hjk : j ≤ k := by simp only [Finset.mem_range] at hj; omega
    have hsub : S.powerset.filter (fun A => A.card = j) ⊆ S.powerset.filter (fun A => A.card ≤ k) := by
      intro A hA
      simp only [Finset.mem_filter, Finset.mem_powerset] at hA ⊢
      exact ⟨hA.1, by omega⟩
    have hle : ∀ x, (∑ A ∈ S.powerset.filter (fun A => A.card = j), enorm (f A x) ^ (2:ℝ))
        ≤ (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), enorm (f A x) ^ (2:ℝ)) :=
      fun x => Finset.sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ => by positivity)
    refine (hfix j hjk).trans (mul_le_mul_right ?_ _)
    exact lintegral_mono (fun x => ENNReal.pow_le_pow_left (hle x))
  have hfinal : (∑ j ∈ Finset.range (k+1), ∫⁻ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ)) ∂μ)
      ≤ ((k:ℝ≥0∞) + 1) * (ENNReal.ofReal D * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), enorm (f A x) ^ (2:ℝ)) ^ r ∂μ) := by
    calc ∑ j ∈ Finset.range (k+1), ∫⁻ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ)) ∂μ
        ≤ ∑ j ∈ Finset.range (k+1), (ENNReal.ofReal D * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), enorm (f A x) ^ (2:ℝ)) ^ r ∂μ) :=
          Finset.sum_le_sum hper
      _ = ((k:ℝ≥0∞) + 1) * (ENNReal.ofReal D * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), enorm (f A x) ^ (2:ℝ)) ^ r ∂μ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
  -- The exponent bookkeeping: `(k+1)^{2r-1} * (k+1) = (k+1)^{2r}`.
  have hKc : ((k:ℝ≥0∞) + 1) ^ (2*(r:ℝ) - 1) * ((k:ℝ≥0∞) + 1) = ((k:ℝ≥0∞) + 1) ^ (2*(r:ℝ)) := by
    have h0 : ((k:ℝ≥0∞) + 1) ≠ 0 := by simp
    have ht : ((k:ℝ≥0∞) + 1) ≠ ⊤ := by simp
    have h := ENNReal.rpow_add (x := ((k:ℝ≥0∞) + 1)) (2*(r:ℝ)-1) 1 h0 ht
    rw [ENNReal.rpow_one] at h
    rw [← h, show (2*(r:ℝ)-1) + 1 = 2*(r:ℝ) by ring]
  have hconst : ENNReal.ofReal (((k:ℝ) + 1) ^ (2*r) * D)
      = ((k:ℝ≥0∞) + 1) ^ (2*(r:ℝ)) * ENNReal.ofReal D := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
    have hck : ENNReal.ofReal ((k:ℝ) + 1) = ((k:ℝ≥0∞) + 1) := by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_natCast]
      norm_num
    rw [hck, ← ENNReal.rpow_natCast]
    rw [show ((2*r : ℕ) : ℝ) = 2*(r:ℝ) by push_cast; ring]
  calc (∫⁻ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), f A x) ^ (2*(r:ℝ)) ∂μ)
      ≤ ((k:ℝ≥0∞) + 1) ^ (2*(r:ℝ) - 1) *
          ∫⁻ x, ∑ j ∈ Finset.range (k+1), enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ)) ∂μ := hstep1
    _ = ((k:ℝ≥0∞) + 1) ^ (2*(r:ℝ) - 1) *
          ∑ j ∈ Finset.range (k+1), ∫⁻ x, enorm (∑ A ∈ S.powerset.filter (fun A => A.card = j), f A x) ^ (2*(r:ℝ)) ∂μ := by rw [hT]
    _ ≤ ((k:ℝ≥0∞) + 1) ^ (2*(r:ℝ) - 1) *
          (((k:ℝ≥0∞) + 1) * (ENNReal.ofReal D * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), enorm (f A x) ^ (2:ℝ)) ^ r ∂μ)) := mul_le_mul_right hfinal _
    _ = ((k:ℝ≥0∞) + 1) ^ (2*(r:ℝ)) * (ENNReal.ofReal D * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), enorm (f A x) ^ (2:ℝ)) ^ r ∂μ) := by rw [← mul_assoc, hKc]
    _ = ENNReal.ofReal (((k:ℝ) + 1) ^ (2*r) * D) * ∫⁻ x, (∑ A ∈ S.powerset.filter (fun A => A.card ≤ k), enorm (f A x) ^ (2:ℝ)) ^ r ∂μ := by rw [← mul_assoc, ← hconst]

end Work.BourgainPlan.IonescuWainger
