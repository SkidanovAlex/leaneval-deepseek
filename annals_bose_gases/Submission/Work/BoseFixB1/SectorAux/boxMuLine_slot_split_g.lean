import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.boxMuLine_slot_split
import Submission.Work.BoseFixB1S.PQIdentAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.SectorAux

open MeasureTheory

set_option maxHeartbeats 1600000

/-!
# `Work.BoseFixB1.SectorAux.boxMuLine_slot_split_g`

The `GoodState` (measurable + bounded on the box, no continuity) counterpart of
`Work.BoseFixB1.boxMuLine_slot_split`: the `μ`-line of the FS-faithful box-projection potential
word splits at the distinguished slot `i`,

    ∫ (QᵢΦ)·fib(xᵢ)·(Σ_j P_j(PᵢΦ) − (1+μV)PᵢΦ)
      = Σ_{j≠i} ∫ (QᵢΦ)·fib(xᵢ)·P_j(PᵢΦ) − μV·∫ (QᵢΦ)·fib(xᵢ)·PᵢΦ .

The proof is the one of `boxMuLine_slot_split`, with the two places where that proof used
`Continuous Φ` replaced by the hypotheses actually available here:

* idempotence `PᵢPᵢ = Pᵢ` — `Work.BoseFixB1S.boxPInd_idempotent` (needs only `A` measurable);
* integrability of the slot families — `Work.BoseFixB1.integrableOn_abox_slot_mul` with the
  bound `D = max Cb 0` for `Φ`, pushed through `Work.BoseFixB1S.abs_boxPInd_le`
  (which needs only a bound of `Φ` on the box).

The pointwise algebra is unchanged: `Pᵢ` is idempotent, so the `j = i` term of `Σ_j P_j(PᵢΦ)`
is `PᵢΦ` and cancels the `−PᵢΦ` part of `−(1+μV)PᵢΦ`, leaving `Σ_{j≠i}` and the `−μV·PᵢΦ`.
-/

/-! ## Auxiliary facts -/

/-- Splitting a finite sum off its `i`-th term. -/
private theorem aux_sum_ite_ne_add {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι)
    (a : ι → ℝ) : (∑ j, (if j ≠ i then a j else 0)) + a i = ∑ j, a j := by
  rw [← Finset.sum_filter (fun j => j ≠ i) a, Finset.filter_ne', Finset.sum_erase_add]
  exact Finset.mem_univ i

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
private theorem aux_boxMuLine_pointwise_g {N : ℕ} {ℓ V μ : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
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
  have hidem := Work.BoseFixB1S.boxPInd_idempotent hℓ hV hA hVeq hAc i Φ
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

/-- Integrability of the two slot families on the box, for a state that is only measurable and
bounded on the box. -/
private theorem aux_integrableOn_boxMu_fibres_g {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hFm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hC : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ C)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb) (i j : Fin N) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
        (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
          * (Work.UBBInputs8.boxPInd V A i Φ x))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := by
  let D : ℝ := max Cb 0
  let Df : ℝ := max C 0
  have hD0 : 0 ≤ D := le_max_right _ _
  have hΦbD : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ D :=
    fun x hx => le_trans (hΦb x hx) (le_max_left _ _)
  have hfibb : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ Df :=
    fun z hz => le_trans (hC z hz) (le_max_left _ _)
  have hPb : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A k Φ x| ≤ D :=
    fun k => Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc k hΦbD
  have hPPb : ∀ k : Fin N, ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxPInd V A k (Work.UBBInputs8.boxPInd V A i Φ) x| ≤ D :=
    fun k => Work.BoseFixB1S.abs_boxPInd_le hℓ hV hA hVeq hAc k (hPb i)
  have hPIm : Measurable (Work.UBBInputs8.boxPInd V A i Φ) :=
    Work.BoseFixB1S.measurable_boxPInd V A hA i hΦm
  have hQm : Measurable (Work.UBBInputs8.boxQInd V A i Φ) := by
    have hfun : Work.UBBInputs8.boxQInd V A i Φ
        = fun x : Submission.BoseGases.X N =>
            A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
              - Work.UBBInputs8.boxPInd V A i Φ x := rfl
    rw [hfun]
    exact (((measurable_const.indicator hA).comp (measurable_pi_apply i)).mul
      hΦm).sub hPIm
  have hPm : ∀ k : Fin N,
      Measurable (Work.UBBInputs8.boxPInd V A k (Work.UBBInputs8.boxPInd V A i Φ)) :=
    fun k => Work.BoseFixB1S.measurable_boxPInd V A hA k hPIm
  have hQb : ∀ x ∈ Submission.BoseGases.abox N ℓ,
      |Work.UBBInputs8.boxQInd V A i Φ x| ≤ 2 * D := by
    intro x hx
    have hP := hPb i x hx
    have hind : |A.indicator (fun _ => (1 : ℝ)) (x i)| ≤ 1 := by
      by_cases h : x i ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
    have h1 : |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x| ≤ D := by
      rw [abs_mul]
      calc |A.indicator (fun _ => (1 : ℝ)) (x i)| * |Φ x| ≤ 1 * D :=
            mul_le_mul hind (hΦbD x hx) (abs_nonneg _) (by norm_num)
        _ = D := one_mul D
    have hQ : Work.UBBInputs8.boxQInd V A i Φ x
        = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
          - Work.UBBInputs8.boxPInd V A i Φ x := rfl
    rw [hQ]
    calc |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
            - Work.UBBInputs8.boxPInd V A i Φ x|
          ≤ |A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x|
            + |Work.UBBInputs8.boxPInd V A i Φ x| := abs_sub _ _
      _ ≤ D + D := add_le_add h1 hP
      _ = 2 * D := by ring
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
          ≤ (2 * D) * D := by
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
          ≤ (2 * D) * D := by
      intro x hx
      rw [abs_mul]
      exact mul_le_mul (hQb x hx) (hPb i x hx) (abs_nonneg _) (by linarith)
    have h := Work.BoseFixB1.integrableOn_abox_slot_mul hℓ i hFm hfibb hS hSb
    convert h using 1
    ext x
    ring

/-! ## The `μ`-line splitting -/

theorem boxMuLine_slot_split_g {N : ℕ} {ℓ V μ : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).real A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {fib : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hFm : MeasureTheory.AEStronglyMeasurable fib
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)))
    {C : ℝ} (hC : ∀ z ∈ Submission.BoseGases.acube ℓ, |fib z| ≤ C)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦm : Measurable Φ) {Cb : ℝ}
    (hΦb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Φ x| ≤ Cb) (i : Fin N) :
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
    (aux_integrableOn_boxMu_fibres_g hℓ hV hA hVeq hAc hFm hC hΦm hΦb i i).2
  have hInt : ∀ j : Fin N, MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      (Work.UBBInputs8.boxQInd V A i Φ x) * fib (x i)
        * (Work.UBBInputs8.boxPInd V A j (Work.UBBInputs8.boxPInd V A i Φ) x))
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume :=
    fun j => (aux_integrableOn_boxMu_fibres_g hℓ hV hA hVeq hAc hFm hC hΦm hΦb i j).1
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
  have hpt := aux_boxMuLine_pointwise_g (μ := μ) hℓ hV hA hVeq hAc i fib Φ
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

end Work.BoseFixB1.SectorAux
