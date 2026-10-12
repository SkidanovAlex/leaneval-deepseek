import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.boxPairQCount_le_flat_mul_excited
import Submission.Work.BoseFixB1S.mfRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## 1. The a.e. collapse of the box-indicator sum

`mfSupp` says that `Φ` vanishes a.e. where a coordinate leaves `A`, so each of the `n` slot
summands of the indicator sum is the full state norm. -/
theorem boxSupp_indicator_sum {N : ℕ} {ℓ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {Φ : Submission.BoseGases.X N → ℝ}
    (hSupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) :
    (∑ i : Fin N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
      = (N : ℝ) * ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
  have hterm : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2)
        = ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [hSupp] with x hx
    by_cases hmem : x i ∈ A
    · rw [Set.indicator_of_mem hmem, one_mul]
    · have hΦ : Φ x = 0 := by
        by_contra hc
        exact hmem (hx hc i)
      rw [Set.indicator_of_notMem hmem]
      simp [hΦ]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-! ## 2. The general count split `S + Q = N·‖Φ‖²` for box-supported states -/

theorem boxCountSplitGen {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hSupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) :
    boxFlatCount volA ℓ A Φ + boxQCount volA ℓ A Φ
      = (N : ℝ) * ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 := by
  have hstep : (∑ i : Fin N,
        ((∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
          + ∫ x in Submission.BoseGases.abox N ℓ,
              (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2))
      = ∑ i : Fin N,
          ∫ x in Submission.BoseGases.abox N ℓ,
            A.indicator (fun _ => (1 : ℝ)) (x i) * (Φ x) ^ 2 :=
    Finset.sum_congr rfl (fun i _ => boxPInd_sq_add_boxQInd_sq hℓ hA hvolA hAc i hΦc)
  rw [boxFlatCount, boxQCount, ← Finset.sum_add_distrib, hstep, boxSupp_indicator_sum hSupp]

/-! ## 3. The general (un-normalised) inequality -/

theorem boxPQ_pair_le {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hSupp : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
      Φ x ≠ 0 → ∀ i : Fin N, x i ∈ A) :
    (∑ p ∈ Submission.BoseGases.pairSet N,
        ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1
            (Work.UBBInputs8.boxQInd volA A p.2 Φ) x) ^ 2)
      ≤ boxFlatCount volA ℓ A Φ * boxQCount volA ℓ A Φ
          / (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) := by
  have hpair := boxPairQCount_eq (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc hΦc
  have hjen := boxFlatSqJensen (N := N) (ℓ := ℓ) (volA := volA) hℓ hvol hA hvolA hAc hΦc
  have hsplit := boxCountSplitGen (N := N) (ℓ := ℓ) (volA := volA) hℓ hA hvolA hAc hΦc hSupp
  have hTnn : 0 ≤ boxPairCount volA ℓ A Φ := by
    rw [boxPairCount]
    refine Finset.sum_nonneg fun p _ => ?_
    exact integral_nonneg fun x =>
      sq_nonneg (Work.UBBInputs8.boxPInd volA A p.1
        (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
  have hInn : 0 ≤ ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg (Φ x)
  rcases lt_or_eq_of_le hInn with hIpos | hI0'
  · have hQ : boxQCount volA ℓ A Φ
        = (N : ℝ) * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
          - boxFlatCount volA ℓ A Φ := by
      linarith [hsplit]
    refine (le_div_iff₀ hIpos).mpr ?_
    have h1 := mul_le_mul_of_nonneg_right hpair hInn
    rw [hQ]
    nlinarith [h1, hjen]
  · have hI0 : (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 0 := hI0'.symm
    have hS0 : boxFlatCount volA ℓ A Φ = 0 := by
      rw [hI0] at hjen
      nlinarith [hjen, sq_nonneg (boxFlatCount volA ℓ A Φ)]
    have hgoal : boxFlatCount volA ℓ A Φ * boxQCount volA ℓ A Φ
        / (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) = 0 := by
      rw [hI0, hS0, zero_mul, zero_div]
    rw [hgoal]
    have h1 := hpair
    rw [hS0] at h1
    nlinarith [h1, hTnn]

/-! ## 4. The row at FS's sliding box -/

theorem mfN0NQ_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hΦc : Continuous Φ) (hsupp : Work.BoseFixB1S.mfSupp v μ n Φ u) :
    Work.BoseFixB1S.mfN0NQ v μ n Φ u
      ≤ Work.BoseFixB1S.mfS v μ n Φ u * Work.BoseFixB1S.mfQ v μ n Φ u
          / Work.BoseFixB1S.mfI v μ n Φ := by
  have hMnn : 0 ≤ mfV v μ u := by
    rw [mfV, Work.SmallBoxSliding.boxMass_eq_measureReal]
    exact MeasureTheory.measureReal_nonneg
  rcases lt_or_eq_of_le hMnn with hMpos | hMzero
  · -- non-degenerate box mass: the general inequality at `A = B(u)`
    have hA : MeasurableSet (boxA v μ u) :=
      Work.SmallBoxSliding.measurableSet_dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
    have hvolA : mfV v μ u = (MeasureTheory.volume (boxA v μ u)).toReal := by
      rw [mfV, boxA, Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
    have hAc : boxA v μ u ⊆ Submission.BoseGases.acube
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) := fun x hx =>
      ((Submission.BoseGases.mem_dlBox_iff (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x).mp hx).1
    exact boxPQ_pair_le (N := n) (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (volA := mfV v μ u) (A := boxA v μ u) hℓ hMpos hA hvolA hAc hΦc hsupp
  · -- degenerate box mass `|B(u)| = 0`: `Pᵢ ≡ 0` because `boxPInd` divides by the volume
    have hz : mfV v μ u = 0 := hMzero.symm
    have hP0 : ∀ (i : Fin n) (f : Submission.BoseGases.X n → ℝ)
        (x : Submission.BoseGases.X n),
        Work.UBBInputs8.boxPInd (mfV v μ u) (boxA v μ u) i f x = 0 := by
      intro i f x
      simp only [Work.UBBInputs8.boxPInd, hz, div_zero, zero_mul]
    have hL0 : mfN0NQ v μ n Φ u = 0 := by
      simp only [mfN0NQ]
      simp [hP0]
    have hS0 : mfS v μ n Φ u = 0 := by
      simp only [mfS, boxFlatCount]
      simp [hP0]
    rw [hL0, hS0, zero_mul, zero_div]

end

end Work.BoseFixB1S
