import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MB

open MeasureTheory

set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Analytic inputs of the linearity of the one-slot projection

Two elementary facts about the integrand `w ↦ PV e (x i) w * Φ (Function.update x i w)` of
`slotProj1 e i Φ x`, for *weak* modes (measurable, everywhere bounded, supported in the corpus box
`boxL ℓ`):

* the kernel `w ↦ PV e (x i) w` is measurable (`PV_weak_measurable_snd`);
* hence the whole integrand is integrable whenever the state `Φ` is measurable and everywhere
  bounded (`integrable_PV_mul_update`): it is measurable, everywhere bounded by the product of the
  kernel bound `K = PV_weak_bound` and the state bound, and it vanishes off the finite-measure box
  `boxL ℓ` (the kernel does, `PV_eq_zero_of_notMem_boxL`). -/

/-- The projection kernel `PV e a ·` is measurable in its second argument for measurable modes. -/
theorem PV_weak_measurable_snd {m : ℕ} {e : Fin m → E3 → ℂ} (hmeas : ∀ l, Measurable (e l))
    (a : E3) : Measurable (fun w : E3 => Work.BoseBoxFock.PV e a w) := by
  have hfun : (fun w : E3 => Work.BoseBoxFock.PV e a w)
      = fun w : E3 => ∑ l : Fin m, e l a * star (e l w) := rfl
  rw [hfun]
  exact Finset.measurable_sum Finset.univ fun l _ =>
    measurable_const.mul (Complex.continuous_conj.measurable.comp (hmeas l))

/-- **Integrability of the one-slot integrand.**  For weak modes and a measurable, everywhere
bounded state `Φ`, the integrand `w ↦ PV e (x i) w * Φ (Function.update x i w)` is integrable. -/
theorem integrable_PV_mul_update {m N : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Φ : (Fin N → E3) → ℂ} (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (i : Fin N) (x : Fin N → E3) :
    Integrable (fun w : E3 => Work.BoseBoxFock.PV e (x i) w * Φ (Function.update x i w))
      volume := by
  obtain ⟨K, hK0, hK⟩ := PV_weak_bound hbdd
  obtain ⟨C, hC⟩ := hΦb
  refine integrable_of_bdd_of_support
    (S := Work.BoseK15.corpusBox.boxL ℓ)
    (Work.BoseK15.corpusBox.boxL_measurableSet ℓ)
    (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
    (C := K * max C 0) ?_ ?_ ?_
  · exact ((PV_weak_measurable_snd hmeas (x i)).mul
      (hΦm.comp (measurable_update (f := x) (a := i)))).aestronglyMeasurable
  · intro w
    rw [norm_mul]
    exact mul_le_mul (hK (x i) w) ((hC _).trans (le_max_left C 0)) (norm_nonneg _) hK0
  · intro w hw
    rw [Work.BoseBoxFock.PV_eq_zero_of_notMem_boxL hsupp hw, zero_mul]

/-- **Linearity of the one-slot projection `slotProj1 e i` in its state argument, for weak
(measurable, everywhere bounded, box supported) modes.**

The modes `e l` are only measurable, everywhere bounded and supported in
`Work.BoseK15.corpusBox.boxL ℓ`; the states `Θ k` are measurable and everywhere bounded.

Mirror of `Work.BoseBoxFock.slotProj1_finset_sum` (`Submission/Work/BoseBoxFock/slotProj1_slotExact_eq_zero.lean`),
which needs `Continuous`/`HasCompactSupport` modes.  The only analytic input is: for fixed `x` and
`i`, the integrand `w ↦ PV e (x i) w * Θ k (update x i w)` is measurable, everywhere bounded by
`K * C` and supported in `boxL ℓ` (finite measure), hence integrable; then
`MeasureTheory.integral_finsetSum` and `MeasureTheory.integral_smul` give the identity pointwise.
Available: `Work.MB.PV_weak_*`, `Work.MB.etaOf_weak_*`, `Work.MB.integrable_of_bdd_of_support`,
`Work.MB.PV_weak_le_indicator`, `Work.BoseBoxFock.PV_eq_zero_of_notMem_boxL`. -/
theorem slotProj1_linear_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    (∀ (i : Fin n) {κ : Type} [DecidableEq κ] (s : Finset κ) (c : κ → ℂ)
        (Θ : κ → (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ),
        (∀ k, Measurable (Θ k)) → (∀ k, ∃ C, ∀ x, ‖Θ k x‖ ≤ C) →
        Work.BoseBoxFock.slotProj1 e i (fun x => ∑ k ∈ s, c k • Θ k x)
          = fun x => ∑ k ∈ s, c k • Work.BoseBoxFock.slotProj1 e i (Θ k) x) ∧
    (∀ (i : Fin n) (F G : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ), Measurable F →
        (∃ C, ∀ x, ‖F x‖ ≤ C) → Measurable G → (∃ C, ∀ x, ‖G x‖ ≤ C) →
        Work.BoseBoxFock.slotProj1 e i (fun x => F x - G x)
          = fun x => Work.BoseBoxFock.slotProj1 e i F x - Work.BoseBoxFock.slotProj1 e i G x) := by
  constructor
  · intro i κ _ s c Θ hΘm hΘb
    funext x
    have hInt : ∀ k ∈ s, Integrable (fun w : E3 =>
        c k • (Work.BoseBoxFock.PV e (x i) w * Θ k (Function.update x i w))) volume :=
      fun k _ => (integrable_PV_mul_update hmeas hbdd hsupp (hΘm k) (hΘb k) i x).const_mul (c k)
    have hpt : ∀ w : E3, Work.BoseBoxFock.PV e (x i) w *
          (∑ k ∈ s, c k • Θ k (Function.update x i w))
        = ∑ k ∈ s, c k • (Work.BoseBoxFock.PV e (x i) w * Θ k (Function.update x i w)) := by
      intro w
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, smul_eq_mul]
      ring
    rw [Work.BoseBoxFock.slotProj1]
    trans ∫ w : E3, ∑ k ∈ s, c k •
        (Work.BoseBoxFock.PV e (x i) w * Θ k (Function.update x i w))
    · exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    trans ∑ k ∈ s, ∫ w : E3, c k •
        (Work.BoseBoxFock.PV e (x i) w * Θ k (Function.update x i w))
    · exact integral_finsetSum _ hInt
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_smul, Work.BoseBoxFock.slotProj1]
  · intro i F G hFm hFb hGm hGb
    funext x
    have hIntF : Integrable (fun w : E3 =>
        Work.BoseBoxFock.PV e (x i) w * F (Function.update x i w)) volume :=
      integrable_PV_mul_update hmeas hbdd hsupp hFm hFb i x
    have hIntG : Integrable (fun w : E3 =>
        Work.BoseBoxFock.PV e (x i) w * G (Function.update x i w)) volume :=
      integrable_PV_mul_update hmeas hbdd hsupp hGm hGb i x
    have hpt : ∀ w : E3, Work.BoseBoxFock.PV e (x i) w *
          (F (Function.update x i w) - G (Function.update x i w))
        = Work.BoseBoxFock.PV e (x i) w * F (Function.update x i w)
          - Work.BoseBoxFock.PV e (x i) w * G (Function.update x i w) := fun w => by ring
    rw [Work.BoseBoxFock.slotProj1]
    trans ∫ w : E3, (Work.BoseBoxFock.PV e (x i) w * F (Function.update x i w)
        - Work.BoseBoxFock.PV e (x i) w * G (Function.update x i w))
    · exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    · rw [integral_sub hIntF hIntG]
      rfl

end Work.MB
