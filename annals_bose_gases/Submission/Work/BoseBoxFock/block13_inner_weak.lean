import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.B13Aux
import Submission.Work.BoseBoxFock.pairRowGDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.block13_inner_weak` — the measurable/bounded slot calculus of the
block I/III `u`-integral

For a pair of slots `p : Fin n × Fin n` with `p.1 ≠ p.2`, a state `Θ` on the `n`-particle
configuration space and one-particle factors `A`, `B` on `ℝ³`, consider the "inner" integral

    I (z) = ∫ u, star (Θ z.1) · A (z.1 p.1) · star (B u) · Θ (z.1[p.1 ↦ z.2][p.2 ↦ u]),

as a function of `z = (x, y) : Xn n × ℝ³` — the `y`-slot of the pair is free and integrated into
the *second* slot `p.2`.  This module proves the three structural facts about `I` that the
measurable/bounded ("weak") slot calculus needs:

* `I` is **measurable** when `Θ`, `A`, `B` are (a Bochner integral, in `u`, of a jointly
  measurable integrand; `Measurable.integral_prod_right'` needs no integrability);
* `I` is **bounded on all of `Xn n × ℝ³`** by an explicit constant, the point being that the
  `u`-integrand can only be nonzero when `u ∈ boxL ℓ` (the slot `p.2` of the updated
  configuration is `u`, and `Θ` is supported in `boxPow n ℓ`), so the unbounded domain `ℝ³`
  contributes only `volume.real (boxL ℓ) < ∞`;
* `I` **vanishes off the box** `boxPow n ℓ × boxL ℓ`: either the configuration `z.1` is outside
  the box (so `Θ z.1 = 0`) or the inserted value `z.2` is outside `boxL ℓ`, and then the slot
  `p.1` of the updated configuration is `z.2` (`p.1 ≠ p.2`), so the state factor vanishes.

Auxiliary general-purpose lemmas proved here:

* `norm_integral_le_of_indicator_bound` — the elementary bound `‖∫ f‖ ≤ M · volume.real s` from
  the pointwise bound `‖f u‖ ≤ M · 1_s u` and `volume s < ∞`;
* `measurable_block13Integrand` — joint measurability of the integrand of `I`.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Two general-purpose lemmas -/

/-- **The indicator bound for the Bochner integral.**  If `‖f u‖ ≤ M · 1_s u` pointwise, `M ≥ 0`
and `s` has finite measure, then `‖∫ u, f u‖ ≤ M · volume.real s`.  (No integrability hypothesis
on `f` is needed: it is dominated by the integrable function `M · 1_s`.) -/
theorem norm_integral_le_of_indicator_bound {s : Set E3} (hs : MeasurableSet s)
    (hfin : (volume : Measure E3) s ≠ ⊤) {M : ℝ} (hM : 0 ≤ M) {f : E3 → ℂ}
    (hf : ∀ u, ‖f u‖ ≤ M * s.indicator (fun _ => (1 : ℝ)) u) :
    ‖∫ u, f u‖ ≤ M * (volume : Measure E3).real s := by
  have hInt : Integrable (fun u : E3 => M * s.indicator (fun _ => (1 : ℝ)) u) :=
    Integrable.const_mul (IntegrableOn.integrable_indicator
      (integrableOn_const (μ := (volume : Measure E3)) (C := (1 : ℝ)) hfin (by simp)) hs) _
  have h2 : ∫ u : E3, ‖f u‖ ≤ ∫ u : E3, M * s.indicator (fun _ => (1 : ℝ)) u :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _) hInt
      (Filter.Eventually.of_forall hf)
  have h3 : ∫ u : E3, M * s.indicator (fun _ => (1 : ℝ)) u
      = M * (volume : Measure E3).real s := by
    rw [integral_const_mul, integral_indicator_const (e := (1 : ℝ)) hs]
    simp [smul_eq_mul]
  have h1 := norm_integral_le_integral_norm (μ := (volume : Measure E3)) f
  rw [h3] at h2
  linarith

/-- **Joint measurability of the `block13` integrand** (the pointwise integrand of `I`), as a
function of the configuration `z.1`, the free value `z.2` in slot `p.1` and the integration
variable `u` in slot `p.2`. -/
theorem measurable_block13Integrand {n : ℕ} (p : Fin n × Fin n)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : E3 → ℂ}
    (hΘm : Measurable Θ) (hAm : Measurable A) (hBm : Measurable B) :
    Measurable (fun q : (Work.BoseDict.Xn n × E3) × E3 =>
      star (Θ q.1.1) * A (q.1.1 p.1) * star (B q.2)
        * Θ (Function.update (Function.update q.1.1 p.1 q.1.2) p.2 q.2)) := by
  have h1 : Measurable (fun q : (Work.BoseDict.Xn n × E3) × E3 => star (Θ q.1.1)) :=
    continuous_star.measurable.comp (hΘm.comp (by fun_prop))
  have h2 : Measurable (fun q : (Work.BoseDict.Xn n × E3) × E3 => A (q.1.1 p.1)) :=
    hAm.comp (by fun_prop)
  have h3 : Measurable (fun q : (Work.BoseDict.Xn n × E3) × E3 => star (B q.2)) :=
    continuous_star.measurable.comp (hBm.comp (by fun_prop))
  have h4 : Measurable (fun q : (Work.BoseDict.Xn n × E3) × E3 =>
      Θ (Function.update (Function.update q.1.1 p.1 q.1.2) p.2 q.2)) :=
    hΘm.comp (by fun_prop)
  exact ((h1.mul h2).mul h3).mul h4

/-! ## 2. The three structural facts -/

theorem block13_inner_weak {n : ℕ} {ℓ : ℝ} (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ : Work.BoseDict.Xn n → ℂ} {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hAm : Measurable A) (hAb : ∃ C : ℝ, ∀ x, ‖A x‖ ≤ C)
    (hBm : Measurable B) (hBb : ∃ C : ℝ, ∀ x, ‖B x‖ ≤ C) :
    Measurable (fun z : Work.BoseDict.Xn n × EuclideanSpace ℝ (Fin 3) =>
        ∫ u : EuclideanSpace ℝ (Fin 3), star (Θ z.1) * A (z.1 p.1) * star (B u)
          * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u))
    ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ z : Work.BoseDict.Xn n × EuclideanSpace ℝ (Fin 3),
        ‖∫ u : EuclideanSpace ℝ (Fin 3), star (Θ z.1) * A (z.1 p.1) * star (B u)
          * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)‖ ≤ C)
    ∧ (∀ z : Work.BoseDict.Xn n × EuclideanSpace ℝ (Fin 3),
        z ∉ Set.prod (Work.MB.boxPow n ℓ) (Work.BoseK15.corpusBox.boxL ℓ) →
        (∫ u : EuclideanSpace ℝ (Fin 3), star (Θ z.1) * A (z.1 p.1) * star (B u)
          * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)) = 0) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- ### Measurability: the `u`-integral of a jointly measurable integrand
    have hFm : Measurable (fun q : (Work.BoseDict.Xn n × E3) × E3 =>
        star (Θ q.1.1) * A (q.1.1 p.1) * star (B q.2)
          * Θ (Function.update (Function.update q.1.1 p.1 q.1.2) p.2 q.2)) :=
      measurable_block13Integrand p hΘm hAm hBm
    have h := hFm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3))
    simpa using h.measurable
  · -- ### Boundedness: the integrand is supported in the box `boxL ℓ` in `u`
    obtain ⟨cΘ, hcΘ⟩ := hΘb
    obtain ⟨cA, hcA⟩ := hAb
    obtain ⟨cB, hcB⟩ := hBb
    refine ⟨max cΘ 0 * max cA 0 * max cB 0 * max cΘ 0
      * (volume : Measure E3).real (Work.BoseK15.corpusBox.boxL ℓ), ?_, ?_⟩
    · have h4 : 0 ≤ (volume : Measure E3).real (Work.BoseK15.corpusBox.boxL ℓ) := by
        rw [Measure.real_def]; exact ENNReal.toReal_nonneg
      positivity
    · intro z
      have hsmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
        Work.BoseB4.BoxData.boxL_measurableSet _ ℓ
      have hsfin : (volume : Measure E3) (Work.BoseK15.corpusBox.boxL ℓ) ≠ ⊤ := by
        have h := IsCompact.measure_lt_top (μ := (volume : Measure E3))
          (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ)
        exact ne_of_lt h
      refine norm_integral_le_of_indicator_bound hsmeas hsfin
        (M := max cΘ 0 * max cA 0 * max cB 0 * max cΘ 0) (by positivity)
        (f := fun u : E3 => star (Θ z.1) * A (z.1 p.1) * star (B u)
          * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)) ?_
      intro u
      by_cases hu : u ∈ Work.BoseK15.corpusBox.boxL ℓ
      · rw [Set.indicator_of_mem hu, mul_one]
        have hΘz : ‖Θ z.1‖ ≤ max cΘ 0 := le_trans (hcΘ _) (le_max_left _ _)
        have hAz : ‖A (z.1 p.1)‖ ≤ max cA 0 := le_trans (hcA _) (le_max_left _ _)
        have hBu : ‖B u‖ ≤ max cB 0 := le_trans (hcB _) (le_max_left _ _)
        have hTu : ‖Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)‖ ≤ max cΘ 0 :=
          le_trans (hcΘ _) (le_max_left _ _)
        simp only [norm_mul, norm_star]
        gcongr
      · -- outside the box the state factor vanishes: the slot `p.2` of the update is `u`
        have hupd : (Function.update (Function.update z.1 p.1 z.2) p.2 u) p.2 = u :=
          Function.update_self ..
        have hΘu : Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u) = 0 := by
          refine Function.notMem_support.mp (fun hc => ?_)
          have hmem := (Set.mem_univ_pi.mp (hΘs hc)) p.2
          rw [hupd] at hmem
          exact hu hmem
        rw [Set.indicator_of_notMem hu, mul_zero, hΘu]
        simp
  · -- ### Vanishing off the box
    intro z hz
    have hz' : ¬ (z.1 ∈ Work.MB.boxPow n ℓ ∧
        z.2 ∈ Work.BoseK15.corpusBox.boxL ℓ) := fun hc => hz (Set.mem_prod.mpr hc)
    have hzero : (fun u : E3 => star (Θ z.1) * A (z.1 p.1) * star (B u)
        * Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u)) = fun _ => (0 : ℂ) := by
      funext u
      rcases not_and_or.mp hz' with h1 | h2
      · -- the configuration `z.1` is outside the box
        have hΘz : Θ z.1 = 0 := Function.notMem_support.mp (fun hc => h1 (hΘs hc))
        simp [hΘz]
      · -- the inserted value `z.2` is outside the box: it occupies the slot `p.1`
        have hupd : (Function.update (Function.update z.1 p.1 z.2) p.2 u) p.1 = z.2 := by
          rw [Function.update_of_ne hp, Function.update_self]
        have hΘu : Θ (Function.update (Function.update z.1 p.1 z.2) p.2 u) = 0 := by
          refine Function.notMem_support.mp (fun hc => h2 ?_)
          have hmem := (Set.mem_univ_pi.mp (hΘs hc)) p.1
          rwa [hupd] at hmem
        simp [hΘu]
    rw [hzero]
    simp

end Work.BoseBoxFock
