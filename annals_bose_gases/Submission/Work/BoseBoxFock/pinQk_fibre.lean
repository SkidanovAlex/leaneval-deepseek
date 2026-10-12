import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PB3FibreQ
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pinQk_fibre`

The **fibre (slice) form of the slot-`j` pinned-mode pairing**: for a single localised mode
`w = pinQ v μ N k` (the pinned representative `(√ℓ³)⁻¹Q(e^{ik·}χ_Λ)`, `ℓ = ellH v μ`) and two
bounded measurable states `Θ`, `Ψ` supported in the box `abox n ℓ`,

    ∫ x, conj (Θ x) · (w (x j) · ∫ u, conj (w u)·Ψ (x[j ↦ u]))
      = ∫ x', conj (∫ u, conj (w u)·Θ (x'[j ↦ u])) · (∫ u, conj (w u)·Ψ (x'[j ↦ u])).

This is the rank-one case of the block-III fibre identity `Work.BoseBoxFock.fibre_part1` at the
kernel `w = pinQ v μ N k`, whose only analytic input is the integrability of the pairing
integrand; here that integrability is *proved* (the pinned mode is bounded with support in the
compact box `boxL ℓ`, the states are bounded with support in the finite-measure box `abox n ℓ`), so
the statement carries no integrability hypothesis.

`sorry`-free.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 1. The support of the pinned mode -/

/-- **The pinned mode is supported in the box `boxL (ellH v μ)`**: `pinQ v μ N k` is a multiple of
`qVec ℓ (kmomLab ℓ N k)` (`ℓ = ellH v μ`) and `qVec = modeVec − χ̂(ℓk)·θ_Λ` is supported in the box
(`support_qVec_subset`). -/
lemma pinQ_support_subset (v : E3 → ℝ) (μ : ℝ) (N : ℕ) (k : Lab N) :
    Function.support (pinQ v μ N k) ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
  intro z hz
  refine support_qVec_subset (ellH_pos v μ) (kmomLab (ellH v μ) N k) ?_
  intro h0
  exact hz (by simp only [pinQ]; rw [h0, mul_zero])

/-- **The support of the pinned mode has finite measure** (`boxL ℓ` has volume `ℓ³`). -/
lemma pinQ_support_measure_ne_top (v : E3 → ℝ) (μ : ℝ) (N : ℕ) (k : Lab N) :
    volume (Function.support (pinQ v μ N k)) ≠ ⊤ := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hbox : volume (Work.BoseK15.corpusBox.boxL (ellH v μ)) ≠ ⊤ := by
    rw [Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hbox (measure_mono (pinQ_support_subset v μ N k))

/-! ## 2. Integrability of the slot pairing integrand -/

/-- **Integrability of the slot-`j` rank-one pairing integrand.**  If `w` is a bounded measurable
one-body kernel with `σ`-finite support and `Θ`, `Ψ` are bounded measurable `n`-body states with `Θ`
supported in the box `abox n ℓ` (a finite-measure set), then

    x ↦ conj (Θ x) · (w (x j) · ∫ u, conj (w u)·Ψ (x[j ↦ u]))

is integrable.  The inner integral is bounded uniformly in `x` by the `L¹`-majorant
`Cw·CΨ·1_{supp w}`, and the whole integrand is bounded and vanishes off `abox n ℓ`. -/
lemma integrable_slotPair {n : ℕ} (j : Fin n) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {w : E3 → ℂ} {Θ Ψ : Xn n → ℂ}
    (hw : Measurable w) (hwb : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖w z‖ ≤ C)
    (hws : volume (Function.support w) ≠ ⊤)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    (hΨm : Measurable Ψ) (hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C) :
    Integrable (fun x : Xn n => (starRingEnd ℂ) (Θ x)
        * (w (x j) * ∫ u : E3, (starRingEnd ℂ) (w u) * Ψ (Function.update x j u)))
      (volume : Measure (Xn n)) := by
  classical
  obtain ⟨Cw, hCw0, hCw⟩ := hwb
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  obtain ⟨CΨ, hCΨ⟩ := hΨb
  have habmeas : MeasurableSet (Submission.BoseGases.abox n ℓ) :=
    (Submission.BoseGases.abox_compact n hℓ).isClosed.measurableSet
  have habfin : volume (Submission.BoseGases.abox n ℓ) ≠ ⊤ :=
    (Submission.BoseGases.abox_compact n hℓ).measure_ne_top
  have hsuppmeas : MeasurableSet (Function.support w) := by
    have h : Function.support w = w ⁻¹' ({0}ᶜ : Set ℂ) := rfl
    rw [h]
    exact hw (isOpen_compl_singleton.measurableSet)
  have hCΘ'0 : 0 ≤ max CΘ 0 := le_max_right _ _
  have hCΨ'0 : 0 ≤ max CΨ 0 := le_max_right _ _
  have hCΘ' : ∀ x, ‖Θ x‖ ≤ max CΘ 0 := fun x => le_trans (hCΘ x) (le_max_left _ _)
  have hCΨ' : ∀ x, ‖Ψ x‖ ≤ max CΨ 0 := fun x => le_trans (hCΨ x) (le_max_left _ _)
  have hGind : Integrable ((Function.support w).indicator (fun _ : E3 => (1:ℝ))) volume :=
    (integrable_indicator_iff hsuppmeas).mpr
      (integrableOn_const (s := Function.support w) (C := (1:ℝ)) hws (by norm_num))
  set G : E3 → ℝ := fun u => (Cw * max CΨ 0) * (Function.support w).indicator (fun _ => (1:ℝ)) u
    with hGdef
  have hGint : Integrable G volume := by
    rw [hGdef]; exact hGind.const_mul (Cw * max CΨ 0)
  have hGnn : ∀ u, 0 ≤ G u := by
    intro u
    rw [hGdef]
    exact mul_nonneg (mul_nonneg hCw0 hCΨ'0)
      (Set.indicator_nonneg (fun a _ => zero_le_one) u)
  have hinner : ∀ x : Xn n,
      ‖∫ u : E3, (starRingEnd ℂ) (w u) * Ψ (Function.update x j u)‖ ≤ ∫ u : E3, G u := by
    intro x
    refine norm_integral_le_of_norm_le hGint (Filter.Eventually.of_forall fun u => ?_)
    by_cases hu : w u = 0
    · rw [hu, map_zero, zero_mul, norm_zero]
      exact hGnn u
    · have hu' : u ∈ Function.support w := hu
      have hG : G u = Cw * max CΨ 0 := by
        simp only [hGdef, Set.indicator_of_mem hu', mul_one]
      rw [hG, norm_mul, starRingEnd_apply, norm_star]
      exact mul_le_mul (hCw u) (hCΨ' (Function.update x j u)) (norm_nonneg _) hCw0
  have hInt0 : 0 ≤ ∫ u : E3, G u := integral_nonneg (fun u => hGnn u)
  set M : ℝ := max CΘ 0 * (Cw * ∫ u : E3, G u) with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg hCΘ'0 (mul_nonneg hCw0 hInt0)
  have houter : ∀ x : Xn n,
      ‖(starRingEnd ℂ) (Θ x) * (w (x j)
        * ∫ u : E3, (starRingEnd ℂ) (w u) * Ψ (Function.update x j u))‖ ≤ M := by
    intro x
    rw [norm_mul, norm_mul, starRingEnd_apply, norm_star]
    rw [hMdef]
    refine mul_le_mul (hCΘ' x) ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCΘ'0
    exact mul_le_mul (hCw (x j)) (hinner x) (norm_nonneg _) hCw0
  have hzero : ∀ x : Xn n, x ∉ Submission.BoseGases.abox n ℓ →
      (starRingEnd ℂ) (Θ x) * (w (x j)
        * ∫ u : E3, (starRingEnd ℂ) (w u) * Ψ (Function.update x j u)) = 0 := by
    intro x hx
    have hΘx : Θ x = 0 := by
      by_contra h
      exact hx (hΘs h)
    rw [hΘx, map_zero, zero_mul]
  have hHind : Integrable (fun x : Xn n =>
      M * (Submission.BoseGases.abox n ℓ).indicator (fun _ => (1:ℝ)) x) volume := by
    have h := ((integrable_indicator_iff habmeas).mpr
      (integrableOn_const (s := Submission.BoseGases.abox n ℓ) (C := (1:ℝ)) habfin
        (by norm_num))).const_mul M
    simpa only using h
  have hmeas : AEStronglyMeasurable (fun x : Xn n => (starRingEnd ℂ) (Θ x)
      * (w (x j) * ∫ u : E3, (starRingEnd ℂ) (w u) * Ψ (Function.update x j u)))
      (volume : Measure (Xn n)) := by
    have hΘsm : StronglyMeasurable (fun x : Xn n => (starRingEnd ℂ) (Θ x)) :=
      Complex.continuous_conj.measurable.stronglyMeasurable.comp_measurable hΘm
    have hwsm : StronglyMeasurable (fun x : Xn n => w (x j)) :=
      (hw.stronglyMeasurable).comp_measurable (measurable_pi_apply j)
    have hFsm : StronglyMeasurable (fun x : Xn n =>
        ∫ u : E3, (starRingEnd ℂ) (w u) * Ψ (Function.update x j u)) := by
      refine StronglyMeasurable.integral_prod_right ?_
      exact Measurable.stronglyMeasurable
        ((Complex.continuous_conj.measurable.comp (hw.comp measurable_snd)).mul
          (hΨm.comp (continuous_update (A := fun _ : Fin n => E3) j).measurable))
    exact (hΘsm.mul (hwsm.mul hFsm)).aestronglyMeasurable
  refine Integrable.mono' hHind hmeas (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hx, mul_one]
    exact houter x
  · rw [hzero x hx, norm_zero, Set.indicator_of_notMem hx, mul_zero]

/-! ## 3. The fibre identity for the pinned mode -/

theorem pinQk_fibre {n N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (j : Fin n)
    (k : Work.BoseBoxFock.Lab N)
    {Θ Ψ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ))
    (hΨm : Measurable Ψ) (hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C)
    (hΨs : Function.support Ψ ⊆ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) :
    (∫ x : Fin n → EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (Θ x)
        * (Work.BoseBoxFock.pinQ v μ N k (x j)
            * ∫ u : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
                * Ψ (Function.update x j u)))
      = ∫ x' : {k : Fin n // k ≠ j} → EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (∫ u : EuclideanSpace ℝ (Fin 3),
              (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
                * Θ (Work.BoseBoxFock.insertCoord j u x'))
            * (∫ u : EuclideanSpace ℝ (Fin 3),
                (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
                  * Ψ (Work.BoseBoxFock.insertCoord j u x')) := by
  refine fibre_part1 (Ψ := Θ) (Ξ := Ψ) (w := pinQ v μ N k) j ?_
  exact integrable_slotPair j (ellH_pos v μ) (pinQ_measurable v μ N k) (pinQ_bdd v μ N k)
    (pinQ_support_measure_ne_top v μ N k) hΘm hΘb hΘs hΨm hΨb

end Work.BoseBoxFock
