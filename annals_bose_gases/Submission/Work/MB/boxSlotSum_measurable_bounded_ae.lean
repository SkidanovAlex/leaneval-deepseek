import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.boxSlotSum_measurable_bounded
import Submission.Work.BoseBoxFock.modesOfHonestModes_ae
import Submission.Work.BoseBoxFock.slotExact_ae_bounded_of_bounded
import Submission.Work.MB.SlotWeakBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.boxSlotSum_measurable_bounded_ae` — the slot sum at the weak (honest) mode bundle

The strong regularity statement `Work.BoseBoxFock.boxSlotSum_measurable_bounded` assumes the modes
`e l` are **continuous with compact support**.  Those hypotheses are unsatisfiable for the honest
modes of the box ↔ model bridge (`FINDING_continuous_hypotheses_UNSATISFIABLE.md`: the condensate
mode is a.e. the box indicator `thetaFun ℓ`, which has no continuous representative), so every
consumer of the slot calculus must be re-run under the weak bundle

* `hmeas : ∀ l, Measurable (e l)`,
* `hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C` (everywhere bounded),
* `hsupp : ∀ l, Function.support (e l) ⊆ boxL ℓ` (supported in the corpus box),

with a state `Θ` which is only measurable and everywhere bounded.  This file proves that
`boxSlotSum e T Θ` is then **measurable** and **everywhere bounded**, i.e. the weak twin of the
strong theorem, with *everywhere* (not merely a.e.) conclusions so that the identities built on
top of it are identities of functions.

The proof is the pointwise argument of the strong version, with the support hypothesis replacing
compact support.  A single slot is

    `(boxSlotOf e w v j Θ) x = η_w(x_j) · ∫_z conj (η_v z) · Θ (x[j ↦ z])`,

with `η_w = Σ_l w_l e_l` the superposed mode.  Then:

* `η_w` is measurable (`etaOf_weak_measurable`), bounded (`etaOf_weak_bound`) and supported in the
  box (`etaOf_weak_support`) — all three at the weak hypotheses;
* the `z`-integrand is *jointly* measurable on `(Fin d → E3) × E3` (`measurable_update_pair`), so
  `Measurable.stronglyMeasurable` and `StronglyMeasurable.integral_prod_right'` give the
  measurability of the partial integral, hence of the slot;
* the `z`-integrand vanishes as soon as `z ∉ boxL ℓ` (a factor `η_v z` dies), so the integral is
  bounded by `(sup ‖η_v‖) · (sup ‖Θ‖) · vol (boxL ℓ)`, uniformly in `x`; `boxL ℓ` is compact,
  hence of finite measure, and the majorant `Bv * C * 1_{boxL ℓ}` is integrable
  (`Work.MB.integrable_of_bdd_of_support`/`integrable_indicator_iff`).

The slot sum `boxSlotSum e T Θ = Σ_j Σ_l Σ_l' (T e_{l'})_l • boxSlotOf e e_l e_{l'} j Θ` is then a
finite sum of scalars times slots, closed under measurability and under the `ℓ¹` bound
`Finset.sum_le_sum`/`norm_sum_le`.
-/

namespace Work.MB

noncomputable section

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **A single slot preserves measurability and everywhere boundedness, at the weak mode
bundle.**  The modes are only measurable, everywhere bounded and supported in `boxL ℓ` (no
`Continuous`, no `HasCompactSupport`); the state is measurable and everywhere bounded.  Then
`boxSlotOf e w v j Θ` is measurable and everywhere bounded. -/
theorem boxSlotOf_measurable_bounded_weak {m d : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (w v : Fin m → ℝ) (j : Fin d) (Θ : (Fin d → E3) → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    Measurable (Work.BoseDict.boxSlotOf e w v j Θ) ∧
      ∃ C, ∀ x, ‖Work.BoseDict.boxSlotOf e w v j Θ x‖ ≤ C := by
  have hw : Measurable (Work.BoseDict.etaOf e w) := etaOf_weak_measurable hmeas w
  have hv : Measurable (Work.BoseDict.etaOf e v) := etaOf_weak_measurable hmeas v
  obtain ⟨Bw, hBwnn, hBw⟩ := etaOf_weak_bound hbdE w
  obtain ⟨Bv, hBvnn, hBv⟩ := etaOf_weak_bound hbdE v
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hupd : Measurable (fun p : (Fin d → E3) × E3 => Function.update p.1 j p.2) :=
    Work.BoseBoxFock.measurable_update_pair j
  have hjoint : Measurable (fun p : (Fin d → E3) × E3 =>
      (starRingEnd ℂ) (Work.BoseDict.etaOf e v p.2) * Θ (Function.update p.1 j p.2)) :=
    (Complex.continuous_conj.measurable.comp (hv.comp measurable_snd)).mul (hΘm.comp hupd)
  have hres : StronglyMeasurable (fun x : Fin d → E3 =>
      ∫ z : E3, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) * Θ (Function.update x j z)) :=
    hjoint.stronglyMeasurable.integral_prod_right'
  refine ⟨?_, ?_⟩
  · exact (hw.comp (measurable_pi_apply j)).mul hres.measurable
  · refine ⟨Bw * (Bv * max CΘ 0 * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal), fun x => ?_⟩
    have hSmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
      Work.BoseK15.corpusBox.boxL_measurableSet ℓ
    have hSfin : (volume : Measure E3) (Work.BoseK15.corpusBox.boxL ℓ) ≠ ⊤ :=
      (Work.BoseK15.corpusBox.boxL_compact ℓ).measure_lt_top.ne
    have hfx : ∀ z : E3, ‖(starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
        Θ (Function.update x j z)‖ ≤ Bv * max CΘ 0 := by
      intro z
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hBv z) ((hCΘ _).trans (le_max_left _ _)) (norm_nonneg _) hBvnn
    have hpt : ∀ z : E3, ‖(starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
        Θ (Function.update x j z)‖
        ≤ Bv * max CΘ 0 * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) z := by
      intro z
      by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ
      · rw [Set.indicator_of_mem hz, mul_one]; exact hfx z
      · rw [Set.indicator_of_notMem hz, mul_zero]
        have hzero : Work.BoseDict.etaOf e v z = 0 := by
          by_contra hne
          exact hz (etaOf_weak_support hsupp v (Function.mem_support.mpr hne))
        rw [hzero, map_zero, zero_mul, norm_zero]
    have hmaj : Integrable (fun z : E3 =>
        Bv * max CΘ 0 * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) z)
        (volume : Measure E3) :=
      ((integrable_indicator_iff hSmeas).mpr (integrableOn_const hSfin)).const_mul _
    have hbnd : ‖∫ z : E3, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
        Θ (Function.update x j z)‖
        ≤ Bv * max CΘ 0 * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal := by
      calc ‖∫ z : E3, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
              Θ (Function.update x j z)‖
          ≤ ∫ z : E3, ‖(starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
              Θ (Function.update x j z)‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ z : E3, Bv * max CΘ 0 *
              (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) z :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _) hmaj
              (Filter.Eventually.of_forall hpt)
        _ = Bv * max CΘ 0 * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal := by
            rw [MeasureTheory.integral_const_mul,
              MeasureTheory.integral_indicator_const (1 : ℝ)
                (Work.BoseK15.corpusBox.boxL_measurableSet ℓ),
              MeasureTheory.Measure.real, smul_eq_mul, mul_one]
    calc ‖Work.BoseDict.boxSlotOf e w v j Θ x‖
        = ‖Work.BoseDict.etaOf e w (x j)‖ *
            ‖∫ z : E3, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
              Θ (Function.update x j z)‖ := by
          rw [Work.BoseDict.boxSlotOf, norm_mul]
      _ ≤ Bw * ‖∫ z : E3, (starRingEnd ℂ) (Work.BoseDict.etaOf e v z) *
              Θ (Function.update x j z)‖ := mul_le_mul_of_nonneg_right (hBw _) (norm_nonneg _)
      _ ≤ Bw * (Bv * max CΘ 0 * (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal) :=
          mul_le_mul_of_nonneg_left hbnd hBwnn

theorem boxSlotSum_measurable_bounded_ae {m d : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (Θ : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ) (hΘm : Measurable Θ)
    (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) :
    Measurable (Work.BoseDict.boxSlotSum e T Θ) ∧
      ∃ C, ∀ x, ‖Work.BoseDict.boxSlotSum e T Θ x‖ ≤ C := by
  classical
  have hfun : Work.BoseDict.boxSlotSum e T Θ
      = fun x => ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m,
          T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x := by
    funext x
    simp only [Work.BoseDict.boxSlotSum, Finset.sum_apply, Pi.smul_apply]
  have hterm : ∀ (j : Fin d) (l l' : Fin m),
      Measurable (fun x : Fin d → E3 => T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x) ∧
      ∃ B, ∀ x : Fin d → E3, ‖T (Work.BoseB4.evec m l') l •
          Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ ≤ B := by
    intro j l l'
    obtain ⟨hm, hb⟩ := boxSlotOf_measurable_bounded_weak hmeas hbdE hsupp
      (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ hΘm hΘb
    refine ⟨hm.const_smul (T (Work.BoseB4.evec m l') l), ?_⟩
    obtain ⟨B, hB⟩ := hb
    refine ⟨‖T (Work.BoseB4.evec m l') l‖ * max B 0, fun x => ?_⟩
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((hB x).trans (le_max_left _ _)) (norm_nonneg _)
  choose B hB using fun (j : Fin d) (l l' : Fin m) => (hterm j l l').2
  rw [hfun]
  refine ⟨?_, ⟨∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m, max (B j l l') 0, fun x => ?_⟩⟩
  · refine Finset.measurable_sum _ (fun j _ =>
      Finset.measurable_sum _ (fun l _ =>
        Finset.measurable_sum _ (fun l' _ => (hterm j l l').1)))
  · calc ‖∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m,
          T (Work.BoseB4.evec m l') l •
            Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖
        ≤ ∑ j : Fin d, ‖∑ l : Fin m, ∑ l' : Fin m,
            T (Work.BoseB4.evec m l') l •
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j : Fin d, ∑ l : Fin m, ‖∑ l' : Fin m,
            T (Work.BoseB4.evec m l') l •
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ :=
          Finset.sum_le_sum (fun j _ => norm_sum_le _ _)
      _ ≤ ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m,
            ‖T (Work.BoseB4.evec m l') l •
              Work.BoseDict.boxSlotOf e (Work.BoseB4.evec m l) (Work.BoseB4.evec m l') j Θ x‖ :=
          Finset.sum_le_sum (fun j _ =>
            Finset.sum_le_sum (fun l _ => norm_sum_le _ _))
      _ ≤ ∑ j : Fin d, ∑ l : Fin m, ∑ l' : Fin m, max (B j l l') 0 :=
          Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ =>
            Finset.sum_le_sum (fun l' _ =>
              (hB j l l' x).trans (le_max_left _ _))))

end

end Work.MB
