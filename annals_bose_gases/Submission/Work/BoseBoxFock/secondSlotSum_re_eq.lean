import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.PB3Aux
import Submission.Work.BoseBoxFock.pinQk_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.secondSlotSum_re_eq`

The **second slot sum** of the block-III term of the `Q₂` row, at the constant weight
(`K1exp v μ N (fun _ => 1)`), is the sum of the slot-`j` frame forms:

    Σ_j ∫ₓ∫_y conj(Θ x)·K1exp(1)(x j) y·Θ(x[j↦y]) = Σ_j frameSlotForm v μ N j Θ

with `Θ = boxRestrictC (ellH v μ) Φ`.

The proof has three ingredients, none of them analytic:

* the kernel expansion `K1exp_one_eq` (`K1exp(1) = Σ_k pinQ_k ⊗ conj pinQ_k`, from
  `pinQ_kernel_expansion` at the constant weight);
* the finite-sum / iterated-integral exchange (`Lab N = Fin 3 → ZMod (2N+1)` is finite);
* the identification of the second slot integral `∫_y conj(pinQ_k y)·Θ(x[j↦y])`, i.e. the fact
  that the `y`-integral of the expanded (slot-separated) kernel reproduces the frame form after the
  `x`-integral is restricted to the box.

All integrability inputs are supplied by `pinQk_fibre.integrable_slotPair` (`Θ` is bounded with
support in the box, `pinQ_k` is bounded with support of finite measure) and by a direct
bounded-with-finite-measure-support argument for the `y`-integral.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The slot kernel of the expanded second slot sum -/

/-- The `k`-th summand of the expanded second slot sum: the two slots paired against the pinned mode
`pinQ v μ N k`, with the `y`-dependence confined to the second factor. -/
noncomputable def slotF {n N : ℕ} (v : E3 → ℝ) (μ : ℝ) (j : Fin n) (Θ : Xn n → ℂ) :
    Lab N → Xn n → E3 → ℂ :=
  fun k x y => (starRingEnd ℂ) (Θ x) *
    (pinQ v μ N k (x j) * ((starRingEnd ℂ) (pinQ v μ N k y) * Θ (Function.update x j y)))

/-! ## 2. The `y`-integrability of the slot kernel

`y ↦ conj(pinQ_k y)·Θ(x[j↦y])` is bounded (by `‖pinQ_k‖·‖Θ‖`) and supported in the support of
`pinQ_k`, which has finite measure. -/

lemma integrable_pinQ_conj_mul_update {n N : ℕ} (v : E3 → ℝ) (μ : ℝ) (j : Fin n)
    (k : Lab N) (x : Xn n) {Θ : Xn n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ z, ‖Θ z‖ ≤ C) :
    Integrable (fun y : E3 => (starRingEnd ℂ) (pinQ v μ N k y) * Θ (Function.update x j y))
      (volume : Measure E3) := by
  obtain ⟨Cw, hCw0, hCw⟩ := pinQ_bdd v μ N k
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hCΘ0 : 0 ≤ max CΘ 0 := le_max_right _ _
  have hCΘ' : ∀ z, ‖Θ z‖ ≤ max CΘ 0 := fun z => (hCΘ z).trans (le_max_left _ _)
  set s : Set E3 := Function.support (pinQ v μ N k) with hsdef
  have hsmeas : MeasurableSet s := by
    have h : s = (pinQ v μ N k) ⁻¹' ({0}ᶜ : Set ℂ) := rfl
    rw [h]
    exact (pinQ_measurable v μ N k) isOpen_compl_singleton.measurableSet
  have hsfin : volume s ≠ ⊤ := pinQ_support_measure_ne_top v μ N k
  have hind : Integrable (fun y : E3 => (Cw * max CΘ 0) * s.indicator (fun _ => (1 : ℝ)) y)
      (volume : Measure E3) :=
    (((integrable_indicator_iff hsmeas).mpr
      (integrableOn_const (s := s) (C := (1 : ℝ)) hsfin (by norm_num))).const_mul _)
  refine Integrable.mono' hind ?_ ?_
  · exact ((Complex.continuous_conj.measurable.comp (pinQ_measurable v μ N k)).mul
      (hΘm.comp (by fun_prop))).aestronglyMeasurable
  · filter_upwards with y
    by_cases hy : pinQ v μ N k y = 0
    · have hys : y ∉ s := by simpa only [hsdef, Function.mem_support, ne_eq, not_not] using hy
      rw [hy, map_zero, zero_mul, norm_zero, Set.indicator_of_notMem hys, mul_zero]
    · have hys : y ∈ s := by simpa only [hsdef, Function.mem_support, ne_eq] using hy
      rw [Set.indicator_of_mem hys, mul_one, norm_mul, starRingEnd_apply, norm_star]
      exact mul_le_mul (hCw y) (hCΘ' _) (norm_nonneg _) hCw0

/-- The `y`-integral of the slot kernel is integrable in `y` (for every configuration `x`). -/
lemma slotF_integrable_y {n N : ℕ} (v : E3 → ℝ) (μ : ℝ) (j : Fin n) (Θ : Xn n → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ z, ‖Θ z‖ ≤ C) (k : Lab N) (x : Xn n) :
    Integrable (fun y : E3 => slotF v μ j Θ k x y) (volume : Measure E3) := by
  simp only [slotF]
  exact ((integrable_pinQ_conj_mul_update v μ j k x hΘm hΘb).const_mul
    (pinQ v μ N k (x j))).const_mul ((starRingEnd ℂ) (Θ x))

/-! ## 3. The exchange of the finite label sum with the iterated integral -/

/-- **Finite sums commute with the iterated integral**: for a finite label set, if each summand is
integrable in `y` for every `x` and the `y`-integral is integrable in `x`, then the iterated
integral of the sum is the sum of the iterated integrals. -/
lemma integral_finset_sum_iterated {n N : ℕ} (F : Lab N → Xn n → E3 → ℂ)
    (hFy : ∀ k x, Integrable (fun y : E3 => F k x y) (volume : Measure E3))
    (hFx : ∀ k, Integrable (fun x : Xn n => ∫ y : E3, F k x y) (volume : Measure (Xn n))) :
    (∫ x : Xn n, ∫ y : E3, ∑ k : Lab N, F k x y)
      = ∑ k : Lab N, ∫ x : Xn n, ∫ y : E3, F k x y := by
  calc (∫ x : Xn n, ∫ y : E3, ∑ k : Lab N, F k x y)
      = ∫ x : Xn n, ∑ k : Lab N, ∫ y : E3, F k x y := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        exact integral_finsetSum Finset.univ (fun k _ => hFy k x)
    _ = ∑ k : Lab N, ∫ x : Xn n, ∫ y : E3, F k x y :=
        integral_finsetSum Finset.univ (fun k _ => hFx k)

/-! ## 4. The second slot integral -/

/-- **The `y`-integral of the slot kernel is the frame coefficient**: the second slot integral of
the expanded kernel `∫_y conj(pinQ_k y)·Θ(x[j↦y])` factors out of the first slot. -/
lemma secondSlotInner_eq {n N : ℕ} (v : E3 → ℝ) (μ : ℝ) (j : Fin n) (Θ : Xn n → ℂ)
    (k : Lab N) (x : Xn n) :
    (∫ y : E3, slotF v μ j Θ k x y)
      = (starRingEnd ℂ) (Θ x) * (pinQ v μ N k (x j) *
          ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (Function.update x j u)) := by
  simp only [slotF]
  rw [integral_const_mul, integral_const_mul]

/-- **The first-slot integrability of the frame coefficient**: the `x`-integral of the frame
coefficient is integrable (`integrable_slotPair`). -/
lemma slotF_integrable_x {n N : ℕ} {v : E3 → ℝ} {μ : ℝ} {j : Fin n} {Θ : Xn n → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ z, ‖Θ z‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    ∀ k : Lab N, Integrable (fun x : Xn n => ∫ y : E3, slotF v μ j Θ k x y)
      (volume : Measure (Xn n)) := by
  intro k
  have h : (fun x : Xn n => ∫ y : E3, slotF v μ j Θ k x y)
      = fun x : Xn n => (starRingEnd ℂ) (Θ x) * (pinQ v μ N k (x j) *
          ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Θ (Function.update x j u)) :=
    funext (fun x => secondSlotInner_eq v μ j Θ k x)
  rw [h]
  exact integrable_slotPair j (ellH_pos v μ) (pinQ_measurable v μ N k) (pinQ_bdd v μ N k)
    (pinQ_support_measure_ne_top v μ N k) hΘm hΘb hΘs hΘm hΘb

/-! ## 5. The kernel expansion of the sum -/

/-- **The kernel expansion of the slot sum**: `Σ_k slotF k x y = conj(Θ x)·K1exp(1)(x j) y·Θ(x[j↦y])`
(`K1exp_one_eq` plus multilinearity). -/
lemma slotF_sum_eq {n N : ℕ} (v : E3 → ℝ) (μ : ℝ) (j : Fin n) (Θ : Xn n → ℂ) (x : Xn n)
    (y : E3) :
    (∑ k : Lab N, slotF v μ j Θ k x y)
      = (starRingEnd ℂ) (Θ x) * K1exp v μ N (fun _ : Lab N => (1 : ℝ)) (x j) y
          * Θ (Function.update x j y) := by
  rw [K1exp_one_eq]
  simp only [slotF]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ## 6. The slot identity -/

/-- **The second slot sum is the frame slot form** (one slot). -/
lemma secondSlotSum_re_eq_aux {n N : ℕ} {v : E3 → ℝ} {μ : ℝ} {j : Fin n} {Θ : Xn n → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ z, ‖Θ z‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    (∫ x : Xn n, ∫ y : E3, (starRingEnd ℂ) (Θ x) * K1exp v μ N (fun _ : Lab N => (1 : ℝ))
        (x j) y * Θ (Function.update x j y)).re
      = frameSlotForm v μ N j Θ := by
  have hFy : ∀ (k : Lab N) (x : Xn n), Integrable (fun y : E3 => slotF v μ j Θ k x y)
      (volume : Measure E3) :=
    fun k x => slotF_integrable_y v μ j Θ hΘm hΘb k x
  have hFx : ∀ k : Lab N, Integrable (fun x : Xn n => ∫ y : E3, slotF v μ j Θ k x y)
      (volume : Measure (Xn n)) := slotF_integrable_x hΘm hΘb hΘs
  have hsum_eq : (∫ x : Xn n, ∫ y : E3, (starRingEnd ℂ) (Θ x) * K1exp v μ N
        (fun _ : Lab N => (1 : ℝ)) (x j) y * Θ (Function.update x j y))
      = ∫ x : Xn n, ∫ y : E3, ∑ k : Lab N, slotF v μ j Θ k x y := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    exact (slotF_sum_eq v μ j Θ x y).symm
  have hset : ∀ k : Lab N,
      (∫ x in Submission.BoseGases.abox n (ellH v μ), (starRingEnd ℂ) (Θ x) *
          (pinQ v μ N k (x j) * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) *
            Θ (Function.update x j u)))
        = ∫ x : Xn n, ∫ y : E3, slotF v μ j Θ k x y := by
    intro k
    have hz : ∀ x : Xn n, x ∉ Submission.BoseGases.abox n (ellH v μ) →
        (starRingEnd ℂ) (Θ x) * (pinQ v μ N k (x j) * ∫ u : E3,
            (starRingEnd ℂ) (pinQ v μ N k u) * Θ (Function.update x j u)) = 0 := by
      intro x hx
      have hΘx : Θ x = 0 := Function.notMem_support.mp (fun h => hx (hΘs h))
      rw [hΘx, map_zero, zero_mul]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (secondSlotInner_eq v μ j Θ k x).symm))
  rw [hsum_eq, integral_finset_sum_iterated (slotF v μ j Θ) hFy hFx, frameSlotForm,
    Finset.sum_congr rfl (fun k _ => hset k)]

/-! ## 7. The target -/

theorem secondSlotSum_re_eq {n N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))} :
    (∑ j : Fin n, ∫ x : Submission.BoseGases.X n, ∫ y : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
            (Φ : Submission.BoseGases.X n → ℝ) x)
          * Work.BoseBoxFock.K1exp v μ N (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ)) (x j) y
          * Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ) (Function.update x j y)).re
      = ∑ j : Fin n, Work.BoseBoxFock.frameSlotForm v μ N j
          (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
            (Φ : Submission.BoseGases.X n → ℝ)) := by
  have hΘm : Measurable (boxRestrictC (ellH v μ) (Φ : Xn n → ℝ)) :=
    boxRestrictC_measurable' _ Φ.contDiff.continuous
  have hΘb : ∃ C : ℝ, ∀ z, ‖boxRestrictC (ellH v μ) (Φ : Xn n → ℝ) z‖ ≤ C := by
    obtain ⟨C, _, hC⟩ := boxRestrictC_bound' (ellH_pos v μ) Φ.contDiff.continuous
    exact ⟨C, hC⟩
  have hΘs : Function.support (boxRestrictC (ellH v μ) (Φ : Xn n → ℝ))
      ⊆ Submission.BoseGases.abox n (ellH v μ) := boxRestrictC_support' _ _
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact secondSlotSum_re_eq_aux (v := v) (μ := μ) (j := j)
    (Θ := boxRestrictC (ellH v μ) (Φ : Xn n → ℝ)) hΘm hΘb hΘs

end Work.BoseBoxFock
