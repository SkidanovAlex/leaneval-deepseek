import Mathlib
import Submission.Work.BoseKinLoc.Momentum.coord_trunc_integral
import Submission.Work.BoseKinLoc.Momentum.euclidean_prod_integrable
import Submission.Work.BoseKinLoc.Momentum.exterior_coord_gt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseKinLoc.Momentum

/-- **Union bound for a product of three one-dimensional density tails.**

Let `f 0, f 1, f 2 : ℝ → ℝ` be non-negative integrable functions with total masses `B i` and with
tail masses `A i` beyond `L/√3`, i.e. `∫_{|u| ≥ L/√3} f i ≤ A i`.  Then the integral of the
three-fold product `∏ i, f i (q i)` over the exterior of the ball of radius `L` in `ℝ³` is
bounded by `∑ i, A i * ∏_{j ≠ i} B j`.

Geometrically: on `‖q‖ > L` at least one coordinate exceeds `L/√3` in modulus
(`exterior_coord_gt`), so on the exterior region the product is at most the sum over `i` of the
product with the `i`-th factor truncated to `|q i| > L/√3`.  Integrating and applying Fubini
(`coord_trunc_integral`) turns the `i`-th summand into the product of the truncated one-dimensional
integral with the remaining total masses. -/
theorem exterior_prod_le (f : Fin 3 → ℝ → ℝ) (A B : Fin 3 → ℝ) (L : ℝ) (hL : 0 < L)
    (hf_nn : ∀ i t, 0 ≤ f i t) (hf_int : ∀ i, MeasureTheory.Integrable (f i))
    (hB : ∀ i, ∫ t : ℝ, f i t = B i)
    (hA : ∀ i, ∫ t in {u : ℝ | L / Real.sqrt 3 ≤ |u|}, f i t ≤ A i) :
    ∫ q in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖}, ∏ i, f i (q i) ≤
      ∑ i, A i * ∏ j ∈ Finset.univ.erase i, B j := by
  classical
  -- The `i`-th summand of the union bound: the product with the `i`-th factor truncated to
  -- the region `|q i| > L/√3`.
  set b : Fin 3 → EuclideanSpace ℝ (Fin 3) → ℝ := fun i q =>
    (if L / Real.sqrt 3 < |q i| then f i (q i) else 0) *
      ∏ j ∈ Finset.univ.erase i, f j (q j) with hb
  have hb_nonneg : ∀ i q, 0 ≤ b i q := by
    intro i q
    simp only [hb]
    refine mul_nonneg ?_ (Finset.prod_nonneg (fun j _ => hf_nn j (q j)))
    by_cases h : L / Real.sqrt 3 < |q i|
    · simp [h, hf_nn i (q i)]
    · simp [h]
  have hb_int : ∀ i, MeasureTheory.Integrable (b i) := by
    intro i
    simp only [hb]
    -- The `i`-th factor truncated to `|t| > L/√3` is integrable.
    have hFi : MeasureTheory.Integrable
        (fun t : ℝ => if L / Real.sqrt 3 < |t| then f i t else 0) := by
      have hfun : (fun t : ℝ => if L / Real.sqrt 3 < |t| then f i t else 0)
          = Set.indicator {u : ℝ | L / Real.sqrt 3 < |u|} (f i) := by
        funext t
        by_cases h : L / Real.sqrt 3 < |t|
        · rw [Set.indicator_of_mem (by simpa using h), if_pos h]
        · rw [Set.indicator_of_notMem (by simpa using h), if_neg h]
      rw [hfun]
      exact (hf_int i).indicator (measurableSet_lt measurable_const measurable_abs)
    -- The family with the `i`-th factor replaced by its truncation.
    have hg_int : ∀ j, MeasureTheory.Integrable
        ((Function.update f i fun t : ℝ => if L / Real.sqrt 3 < |t| then f i t else 0) j) := by
      intro j
      rcases eq_or_ne j i with rfl | hji
      · rw [Function.update_apply, if_pos rfl]
        exact hFi
      · have hjn : (Function.update f i
            fun t : ℝ => if L / Real.sqrt 3 < |t| then f i t else 0) j = f j := by
          rw [Function.update_apply, if_neg hji]
        rw [hjn]
        exact hf_int j
    have hprod := euclidean_prod_integrable hg_int
    have hEq : (fun q : EuclideanSpace ℝ (Fin 3) => ∏ j,
          (Function.update f i fun t : ℝ => if L / Real.sqrt 3 < |t| then f i t else 0) j (q j))
        = (fun q : EuclideanSpace ℝ (Fin 3) =>
          (if L / Real.sqrt 3 < |q i| then f i (q i) else 0) *
            ∏ j ∈ Finset.univ.erase i, f j (q j)) := by
      funext q
      rw [← Finset.mul_prod_erase Finset.univ
        (fun j => (Function.update f i
          fun t : ℝ => if L / Real.sqrt 3 < |t| then f i t else 0) j (q j))
        (Finset.mem_univ i)]
      congr 1
      · rw [Function.update_apply, if_pos rfl]
      · refine Finset.prod_congr rfl (fun j hj => ?_)
        rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hj)]
    rw [hEq] at hprod
    exact hprod
  have hP_int : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) => ∏ i, f i (q i)) := euclidean_prod_integrable hf_int
  have hsum_int : MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) => ∑ i, b i q) :=
    MeasureTheory.integrable_finsetSum Finset.univ (fun i _ => hb_int i)
  have hS_meas : MeasurableSet {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  -- Pointwise union bound: on the exterior of the ball some coordinate is `> L/√3`.
  have hpoint : ∀ q ∈ {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖}, ∏ i, f i (q i) ≤ ∑ i, b i q := by
    intro q hq
    obtain ⟨i0, hi0⟩ := exterior_coord_gt L hL q hq
    refine le_trans (le_of_eq ?_)
      (Finset.single_le_sum (fun i _ => hb_nonneg i q) (Finset.mem_univ i0))
    simp only [hb, if_pos hi0]
    exact (Finset.mul_prod_erase Finset.univ (fun j => f j (q j)) (Finset.mem_univ i0)).symm
  -- Fubini: the integral of a summand is the product of the truncated and the total masses.
  have hfub : ∀ i : Fin 3, ∫ q : EuclideanSpace ℝ (Fin 3), b i q =
      (∫ t in {u : ℝ | L / Real.sqrt 3 < |u|}, f i t) *
        ∏ j ∈ Finset.univ.erase i, (∫ t : ℝ, f j t) := by
    intro i
    simp only [hb]
    exact coord_trunc_integral f i (L / Real.sqrt 3)
  -- Enlarging `{|u| > L/√3}` to `{|u| ≥ L/√3}` and using the hypothesis.
  have hle : ∀ i, ∫ t in {u : ℝ | L / Real.sqrt 3 < |u|}, f i t ≤ A i := by
    intro i
    refine le_trans (MeasureTheory.setIntegral_mono_set (μ := volume) (f := f i)
      (t := {u : ℝ | L / Real.sqrt 3 ≤ |u|}) (s := {u : ℝ | L / Real.sqrt 3 < |u|})
      (hf_int i).integrableOn ?_ ?_) (hA i)
    · exact Filter.Eventually.of_forall (fun t => hf_nn i t)
    · exact Filter.Eventually.of_forall (fun t ht => by
        show L / Real.sqrt 3 ≤ |t|
        exact le_of_lt (by simpa using ht))
  have hB_nonneg : ∀ j, 0 ≤ B j := by
    intro j
    rw [← hB j]
    exact MeasureTheory.integral_nonneg (fun t => hf_nn j t)
  calc ∫ q in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖}, ∏ i, f i (q i)
      ≤ ∫ q in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖}, ∑ i, b i q :=
        MeasureTheory.setIntegral_mono_on (μ := volume) hP_int.integrableOn
          hsum_int.integrableOn hS_meas hpoint
    _ = ∑ i, ∫ q in {q : EuclideanSpace ℝ (Fin 3) | L < ‖q‖}, b i q :=
        MeasureTheory.integral_finsetSum Finset.univ (fun i _ => (hb_int i).integrableOn)
    _ ≤ ∑ i, ∫ q : EuclideanSpace ℝ (Fin 3), b i q :=
        Finset.sum_le_sum (fun i _ => MeasureTheory.setIntegral_le_integral (hb_int i)
          (Filter.Eventually.of_forall (hb_nonneg i)))
    _ = ∑ i, (∫ t in {u : ℝ | L / Real.sqrt 3 < |u|}, f i t) *
          ∏ j ∈ Finset.univ.erase i, (∫ t : ℝ, f j t) :=
        Finset.sum_congr rfl (fun i _ => hfub i)
    _ ≤ ∑ i, A i * ∏ j ∈ Finset.univ.erase i, B j := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [Finset.prod_congr rfl (fun j _ => hB j)]
        exact mul_le_mul_of_nonneg_right (hle i) (Finset.prod_nonneg (fun j _ => hB_nonneg j))

end Work.BoseKinLoc.Momentum
