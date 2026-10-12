import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxMuAgreeB1
import Submission.Work.BoseFixB1.boxQInd_self_boxPInd
import Submission.Work.BoseFixB1S.boxPInd_pair_mixed_peel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory

set_option maxHeartbeats 1600000

/-!
# `Work.BoseFixB1.boxMuLine_slot_split`

The `μ`-line of the FS-faithful box-projection potential word splits at the distinguished
slot `i`: the box projection `P_i = UBBInputs8.boxPInd V A i` is idempotent in its own slot
(`P_i P_i Φ = P_i Φ`), so the diagonal term `j = i` of `∑_j P_j (P_i Φ)` cancels against the
`−P_i Φ` part of `−(1 + μV) P_i Φ`, leaving the `j ≠ i` sum minus the `μV`-multiple.
Integrating the resulting pointwise identity (all pieces being bounded measurable functions
on the finite-measure box) gives the stated integral identity.

The auxiliary lemmas `aux_*` below are the private versions of the four facts that are also
being proved as standalone modules (`integral_finset_sum_ite`, `boxPInd_self_idem`,
`boxMuLine_pointwise`, `integrableOn_boxMu_fibres`).
-/

/-! ## Auxiliary facts -/

/-- Splitting a finite sum off its `i`-th term. -/
private theorem aux_sum_ite_ne_add {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (a : ι → ℝ) : (∑ j, (if j ≠ i then a j else 0)) + a i = ∑ j, a j := by
  rw [← Finset.sum_filter (fun j => j ≠ i) a, Finset.filter_ne', Finset.sum_erase_add]
  exact Finset.mem_univ i

/-- `P_i` is idempotent in its own slot. -/
private theorem aux_boxPInd_self_idem {N : ℕ} {V : ℝ} (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    (i : Fin N) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A i Φ)
      = Work.UBBInputs8.boxPInd V A i Φ := by
  funext x
  have hVne : V ≠ 0 := ne_of_gt hV
  let c : ℝ := A.indicator (fun _ => (1 : ℝ)) (x i)
  let a : ℝ := (1 / V) * (∫ z in A, Φ (Function.update x i z))
  have hc : c = A.indicator (fun _ => (1 : ℝ)) (x i) := rfl
  have ha : a = (1 / V) * (∫ z in A, Φ (Function.update x i z)) := rfl
  have hPx : Work.UBBInputs8.boxPInd V A i Φ x = a * c := by
    rw [Work.UBBInputs8.boxPInd, ha, hc]
  have hPz : ∀ z ∈ A, Work.UBBInputs8.boxPInd V A i Φ (Function.update x i z) = a := by
    intro z hz
    rw [Work.UBBInputs8.boxPInd, ha]
    simp only [Function.update_self i z x, Function.update_idem, Set.indicator_of_mem hz]
    ring
  have hInt : (∫ z in A, Work.UBBInputs8.boxPInd V A i Φ (Function.update x i z)) = a * V := by
    rw [setIntegral_congr_fun hA (fun z hz => hPz z hz)]
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, hVeq.symm, mul_comm]
  have hQQ : Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A i Φ) x = a * c := by
    rw [Work.UBBInputs8.boxPInd, hInt, ← hc]
    have h1 : (1 / V) * (a * V) = a := by field_simp
    rw [h1]
  rw [hQQ, hPx]

/-- The integral of a finite sum of "all terms but the `i`-th" is the sum of the integrals. -/
private theorem aux_integral_finset_sum_ite {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X) {s : Set X} (i : ι)
    {f : ι → X → ℝ} (hf : ∀ j, MeasureTheory.IntegrableOn (f j) s μ) :
    (∫ x in s, (∑ j, (if j ≠ i then f j x else 0)) ∂μ)
      = ∑ j, (if j ≠ i then ∫ x in s, f j x ∂μ else 0) := by
  have hite : ∀ j : ι, MeasureTheory.Integrable (fun x => if j ≠ i then f j x else 0)
      (μ.restrict s) := by
    intro j
    by_cases hj : j ≠ i
    · refine (hf j).congr ?_
      filter_upwards with x
      simp [hj]
    · refine (MeasureTheory.integrable_zero X ℝ (μ.restrict s)).congr ?_
      filter_upwards with x
      simp [hj]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hite j)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hj : j ≠ i
  · rw [if_pos hj]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => by simp [hj]))
  · rw [if_neg hj]
    have hzero : (fun x => if j ≠ i then f j x else 0) = fun _ : X => (0 : ℝ) := by
      funext x
      simp [hj]
    rw [hzero]
    simp

/-- The pointwise `μ`-line splitting. -/
private theorem aux_boxMuLine_pointwise {N : ℕ} {V μ : ℝ} (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    (i : Fin N) (fib : EuclideanSpace ℝ (Fin 3) → ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    ∀ x : Submission.BoseGases.X N,
      (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
        * ((∑ j : Fin N, Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
            - (1 + μ * V) * Work.UBBInputs8.boxPInd V A i Φ x)
      = (∑ j : Fin N, (if j ≠ i then
            (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
              * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
          else 0))
        - μ * V * ((Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
            * Work.UBBInputs8.boxPInd V A i Φ x) := by
  intro x
  have hidem := aux_boxPInd_self_idem (N := N) hV hA hVeq i Φ
  have hid : Work.UBBInputs8.boxPInd V A i (Work.UBBInputs8.boxPInd V A i Φ) x
      = Work.UBBInputs8.boxPInd V A i Φ x := by rw [hidem]
  have hsplit : (∑ j : Fin N, (if j ≠ i then
          Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x else 0))
        + Work.UBBInputs8.boxPInd V A i Φ x
      = ∑ j : Fin N, Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x := by
    have h := aux_sum_ite_ne_add i
      (fun j => Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
    rwa [hid] at h
  have hmul : (∑ j : Fin N, (if j ≠ i then
        (Work.UBBInputs8.boxQInd V A i Φ x * fib (x i))
          * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
      else 0))
      = (Work.UBBInputs8.boxQInd V A i Φ x * fib (x i))
        * (∑ j : Fin N, (if j ≠ i then
            Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x else 0)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_ite, mul_zero]
  rw [hsplit.symm, hmul]
  ring

/-- Integrability of the two slot families on the box. -/
private theorem aux_integrableOn_boxMu_fibres {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hFm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hC : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ C)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (i j : Fin N) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * (Work.UBBInputs8.boxPInd V A i Φ x))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  obtain ⟨C₀, hC₀⟩ :=
    (Submission.BoseGases.abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
  let CΦ : ℝ := max C₀ 0
  have hCΦ0 : 0 ≤ CΦ := le_max_right _ _
  have hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ CΦ := by
    intro x hx
    rw [← Real.norm_eq_abs]
    exact le_trans (hC₀ x hx) (le_max_left _ _)
  let D : ℝ := max C 0
  have hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ D :=
    fun z hz => le_trans (hC z hz) (le_max_left _ _)
  have hPb : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A k Φ x| ≤ CΦ :=
    fun k => Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc k hΦb
  have hPPb : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A k (Work.UBBInputs8.boxPInd V A i Φ) x| ≤ CΦ :=
    fun k => Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc k (hPb i)
  have hQb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd V A i Φ x| ≤ 2 * CΦ := by
    intro x hx
    have hP := hPb i x hx
    have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases h : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ CΦ := by
      rw [abs_mul]
      calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * CΦ :=
            mul_le_mul hind (hΦb x hx) (abs_nonneg _) (by norm_num)
        _ = CΦ := one_mul CΦ
    have hQ : Work.UBBInputs8.boxQInd V A i Φ x
        = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
          - Work.UBBInputs8.boxPInd V A i Φ x := rfl
    rw [hQ]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
            - Work.UBBInputs8.boxPInd V A i Φ x|
          ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
            + |Work.UBBInputs8.boxPInd V A i Φ x| := abs_sub _ _
      _ ≤ CΦ + CΦ := add_le_add h1 hP
      _ = 2 * CΦ := by ring
  have hPIm : Measurable (Work.UBBInputs8.boxPInd V A i Φ) :=
    Work.BoseFixB1S.measurable_boxPInd V A hA i hΦc.measurable
  have hQm : Measurable (Work.UBBInputs8.boxQInd V A i Φ) := by
    have hfun : Work.UBBInputs8.boxQInd V A i Φ
        = fun x : Submission.BoseGases.X N =>
            A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
              - Work.UBBInputs8.boxPInd V A i Φ x := rfl
    rw [hfun]
    exact (((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul
      hΦc.measurable).sub hPIm
  have hPm : ∀ k : Fin N,
      Measurable (Work.UBBInputs8.boxPInd V A k (Work.UBBInputs8.boxPInd V A i Φ)) :=
    fun k => Work.BoseFixB1S.measurable_boxPInd V A hA k hPIm
  refine ⟨?_, ?_⟩
  · have hS : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          Work.UBBInputs8.boxQInd V A i Φ x
            * Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      (hQm.mul (hPm j)).aestronglyMeasurable
    have hSb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxQInd V A i Φ x
            * Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x|
          ≤ (2 * CΦ) * CΦ := by
      intro x hx
      rw [abs_mul]
      exact mul_le_mul (hQb x hx) (hPPb j x hx) (abs_nonneg _) (by linarith)
    have h := Work.BoseFixB1.integrableOn_abox_slot_mul hℓ i hFm hfibb hS hSb
    convert h using 1
    ext x
    ring
  · have hS : MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X N =>
          Work.UBBInputs8.boxQInd V A i Φ x * Work.UBBInputs8.boxPInd V A i Φ x)
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
      (hQm.mul hPIm).aestronglyMeasurable
    have hSb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
        |Work.UBBInputs8.boxQInd V A i Φ x * Work.UBBInputs8.boxPInd V A i Φ x|
          ≤ (2 * CΦ) * CΦ := by
      intro x hx
      rw [abs_mul]
      exact mul_le_mul (hQb x hx) (hPb i x hx) (abs_nonneg _) (by linarith)
    have h := Work.BoseFixB1.integrableOn_abox_slot_mul hℓ i hFm hfibb hS hSb
    convert h using 1
    ext x
    ring

/-! ## The `μ`-line splitting -/

theorem boxMuLine_slot_split {N : ℕ} {ℓ V μ : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hFm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hC : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ C)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) (i : Fin N) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * ((∑ j : Fin N, Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
              - (1 + μ * V) * Work.UBBInputs8.boxPInd V A i Φ x))
      = (∑ j : Fin N, if j ≠ i then
            (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
                * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x))
          else 0)
        - μ * V * (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
              * (Work.UBBInputs8.boxPInd V A i Φ x)) := by
  classical
  have hIntD : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
        * (Work.UBBInputs8.boxPInd V A i Φ x))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    (aux_integrableOn_boxMu_fibres hℓ hV hA hVeq hAc hFm hC hΦc i i).2
  have hInt : ∀ j : Fin N, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
        * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    fun j => (aux_integrableOn_boxMu_fibres hℓ hV hA hVeq hAc hFm hC hΦc i j).1
  have hIntSummand : ∀ j : Fin N,
      MeasureTheory.Integrable (fun x : Submission.BoseGases.X N =>
        if j ≠ i then
          (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
            * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
        else 0)
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) := by
    intro j
    by_cases hj : j ≠ i
    · refine (hInt j).congr ?_
      filter_upwards with x
      simp [hj]
    · refine (MeasureTheory.integrable_zero (Submission.BoseGases.X N) ℝ
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ))).congr ?_
      filter_upwards with x
      simp [hj]
  have hIntSum : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N =>
      ∑ j : Fin N, (if j ≠ i then
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
        else 0))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    MeasureTheory.integrable_finsetSum Finset.univ (fun j _ => hIntSummand j)
  have hIntMuD : MeasureTheory.Integrable (fun x : Submission.BoseGases.X N =>
      μ * V * ((Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
        * (Work.UBBInputs8.boxPInd V A i Φ x)))
      (MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)) :=
    hIntD.const_mul (μ * V)
  have hpt := aux_boxMuLine_pointwise (μ := μ) hV hA hVeq i fib Φ
  calc
    (∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * ((∑ j : Fin N, Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
              - (1 + μ * V) * Work.UBBInputs8.boxPInd V A i Φ x))
        = (∫ x in Submission.BoseGases.abox N ℓ,
            ((∑ j : Fin N, (if j ≠ i then
                (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
                  * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
              else 0))
              - μ * V * ((Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
                  * Work.UBBInputs8.boxPInd V A i Φ x))) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ x in Submission.BoseGases.abox N ℓ,
            (∑ j : Fin N, (if j ≠ i then
                (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
                  * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x)
              else 0)))
          - (∫ x in Submission.BoseGases.abox N ℓ,
              μ * V * ((Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
                * Work.UBBInputs8.boxPInd V A i Φ x)) :=
          MeasureTheory.integral_sub hIntSum hIntMuD
    _ = (∑ j : Fin N, (if j ≠ i then
              (∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
                  * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x))
            else 0))
          - (∫ x in Submission.BoseGases.abox N ℓ,
              μ * V * ((Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
                * Work.UBBInputs8.boxPInd V A i Φ x)) :=
          congrArg (fun t => t - (∫ x in Submission.BoseGases.abox N ℓ,
                μ * V * ((Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
                  * Work.UBBInputs8.boxPInd V A i Φ x)))
            (aux_integral_finset_sum_ite MeasureTheory.volume
              (s := Submission.BoseGases.abox N ℓ) i
              (f := fun j x => (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
                * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x))
              (fun j => hInt j))
    _ = (∑ j : Fin N, (if j ≠ i then
              (∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
                  * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x))
            else 0))
          - μ * V * (∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
                * Work.UBBInputs8.boxPInd V A i Φ x) :=
          congrArg (fun t => (∑ j : Fin N, (if j ≠ i then
              (∫ x in Submission.BoseGases.abox N ℓ,
                (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
                  * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x))
            else 0)) - t)
            (MeasureTheory.integral_const_mul (μ * V)
              (fun x : Submission.BoseGases.X N =>
                (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
                  * Work.UBBInputs8.boxPInd V A i Φ x))

end Work.BoseFixB1
