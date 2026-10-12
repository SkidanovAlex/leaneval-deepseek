import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.BoseBoxFock.PCFU.frameSmear
import Submission.Work.BoseBoxFock.PCFU.lowKer_regular
import Submission.Work.BoseFixB3.Split.lowSlotBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.lowSlot_aQ_aP_measurable_bounded`

Measurability and uniform boundedness of the slot-`j` low-momentum fibre
`lowSlot fc κ ℓ j (aQ ℓ j (aP ℓ i Θ))` for a state `Θ` which is only assumed
**measurable and globally bounded**.

The state `aQ ℓ j (aP ℓ i Θ)` is *not* continuous in general (it is a slot mean of a merely
measurable state), so the corpus's `Work.BoseFixB3.Split.lowSlotStronglyMeasurable` (which needs
`Continuous Ψ`) does not apply.  Two independent ingredients are used.

* *Measurability.*  `PCFU.lowSlot_eq_lowKer` represents the fibre as the convolution
  `x ↦ ∫_z Κ(x_j − z)·1_{Λ(ℓ)}(z)·Ψ(x[j↦z]) dz` with the **continuous** kernel
  `Κ = PCFU.lowKer fc κ` (`PCFU.lowKer_regular`).  The joint integrand
  `(x,z) ↦ Κ(x_j−z)·1_{Λ(ℓ)}(z)·Ψ(x[j↦z])` is jointly (strongly) measurable — the only place `Ψ`
  is used is the composition with `Function.update`, which is continuous hence measurable — so
  `MeasureTheory.StronglyMeasurable.integral_prod_right` gives strong measurability of the
  `z`-integral, i.e. of the fibre.  (No integrability is needed: the Bochner integral is total.)
* *Boundedness.*  For `|Ψ| ≤ M` **globally** (not only on the box — the box cut-off in `lowMult`
  is only in the integration slot `z`, while the other slots of `x` are unrestricted), the
  `p`-integrand of `lowMult` is supported in `‖p‖ ≤ 2κ` and dominated by `M·ℓ³`
  (`Work.BoseFixB3.Split.integral_indicator_norm_le` +
  `Work.BoseFixB3.Split.lowMult_abs_le`), giving the uniform bound
  `(2π)^{-3}·M·ℓ³·vol(B(0,2κ))` on **all** of `Ωⁿ`.

The weak (measurable, globally bounded) slot algebra `aP_measurable`, `aQ_measurable`,
`aP_abs_le`, `aQ_abs_le` used to instantiate the general statement is
`Work.BoseBoxFock.Weak` (`Submission/Work/BoseBoxFock/weakAux.lean`).
-/

namespace Work.BoseBoxFock.PCFU

noncomputable section

open MeasureTheory

set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Measurability and uniform boundedness of the slot-`j` low-momentum fibre**, for a
measurable state `Ψ` that is *globally* bounded by `M ≥ 0`. -/
private theorem lowSlot_measurable_bounded_of_bounded {n : ℕ} {fc : Work.BoseBoxFix.LowCut}
    {κ ℓ M : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ) (hM : 0 ≤ M) {j : Fin n}
    {ψ : Submission.BoseGases.X n → ℝ} (hψm : Measurable ψ) (hψb : ∀ x, |ψ x| ≤ M) :
    Measurable (fun y : Submission.BoseGases.X n => Work.BoseBoxFix.lowSlot fc κ ℓ j ψ y)
    ∧ ∃ D : ℝ, 0 ≤ D ∧ ∀ y : Submission.BoseGases.X n,
        |Work.BoseBoxFix.lowSlot fc κ ℓ j ψ y| ≤ D := by
  refine ⟨?_, ?_⟩
  · -- the position-space kernel form: `lowSlot = ∫_z Κ(x_j − z)·1_{Λ(ℓ)}(z)·Ψ(x[j↦z])`
    have hcont : StronglyMeasurable (fun w : Submission.BoseGases.X n × E3 =>
        Work.BoseBoxFock.PCFU.lowKer fc κ (w.1 j - w.2)) :=
      ((Work.BoseBoxFock.PCFU.lowKer_regular fc hκ).1.comp
        (by fun_prop : Continuous fun w : Submission.BoseGases.X n × E3 =>
          w.1 j - w.2)).stronglyMeasurable
    have hmeas : StronglyMeasurable (fun w : Submission.BoseGases.X n × E3 =>
        (Submission.BoseGases.acube ℓ).indicator
          (fun z : E3 => ψ (Function.update w.1 j z)) w.2) := by
      classical
      have hset : MeasurableSet
          {w : Submission.BoseGases.X n × E3 | w.2 ∈ Submission.BoseGases.acube ℓ} :=
        (Submission.BoseGases.acube_measurable ℓ).preimage measurable_snd
      have hif : Measurable (fun w : Submission.BoseGases.X n × E3 =>
          if w.2 ∈ Submission.BoseGases.acube ℓ then ψ (Function.update w.1 j w.2)
          else (0 : ℝ)) :=
        Measurable.ite hset (hψm.comp (by fun_prop : Measurable fun w :
          Submission.BoseGases.X n × E3 => Function.update w.1 j w.2)) measurable_const
      rw [show (fun w : Submission.BoseGases.X n × E3 =>
            (Submission.BoseGases.acube ℓ).indicator
              (fun z : E3 => ψ (Function.update w.1 j z)) w.2)
          = fun w : Submission.BoseGases.X n × E3 =>
              if w.2 ∈ Submission.BoseGases.acube ℓ then ψ (Function.update w.1 j w.2)
              else (0 : ℝ) from by
        funext w; rw [Set.indicator_apply]]
      exact hif.stronglyMeasurable
    have hjoint : StronglyMeasurable (Function.uncurry (fun (x : Submission.BoseGases.X n)
        (z : E3) => Work.BoseBoxFock.PCFU.lowKer fc κ (x j - z) *
          (Submission.BoseGases.acube ℓ).indicator
            (fun z : E3 => ψ (Function.update x j z)) z)) :=
      hcont.mul hmeas
    have hint := hjoint.integral_prod_right (ν := (volume : Measure E3))
    have hEq : (fun y : Submission.BoseGases.X n => Work.BoseBoxFix.lowSlot fc κ ℓ j ψ y) =
        fun x : Submission.BoseGases.X n => ∫ z : E3,
          Work.BoseBoxFock.PCFU.lowKer fc κ (x j - z) *
            (Submission.BoseGases.acube ℓ).indicator
              (fun z : E3 => ψ (Function.update x j z)) z := by
      funext x
      exact Work.BoseBoxFock.PCFU.lowSlot_eq_lowKer hκ hℓ j x
        (hψm.comp (by fun_prop)).aestronglyMeasurable (fun z _ => hψb _) hM
    rw [hEq]
    exact hint.measurable
  · -- the momentum bound: the state is bounded by `M`, so the box-localised fibre has
    -- `L¹`-mass at most `M·ℓ³`, and the `p`-cut-off lives in the ball `‖p‖ ≤ 2κ`
    refine ⟨((2 * Real.pi) ^ 3)⁻¹ * (M * ℓ ^ 3) *
        (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal, ?_, ?_⟩
    · have h1 : (0 : ℝ) < ((2 * Real.pi) ^ 3)⁻¹ := by positivity
      have h2 : 0 ≤ M * ℓ ^ 3 := mul_nonneg hM (pow_nonneg hℓ.le 3)
      have h3 : 0 ≤ (MeasureTheory.volume (Metric.closedBall (0 : E3) (2 * κ))).toReal :=
        ENNReal.toReal_nonneg
      exact mul_nonneg (mul_nonneg h1.le h2) h3
    · intro y
      have hfib : ∫ z : E3, ‖(((Submission.BoseGases.acube ℓ).indicator
          (fun z : E3 => ψ (Function.update y j z)) z : ℝ) : ℂ)‖ ≤ M * ℓ ^ 3 :=
        Work.BoseFixB3.Split.integral_indicator_norm_le hℓ hM (fun z _ => hψb _)
      have h := Work.BoseFixB3.Split.lowMult_abs_le (fc := fc) (κ := κ) (ℓ := ℓ)
        (D := M * ℓ ^ 3) hκ (mul_nonneg hM (pow_nonneg hℓ.le 3)) hfib (y j)
      simpa [Work.BoseBoxFix.lowSlot] using h

theorem lowSlot_aQ_aP_measurable_bounded {n : ℕ} {fc : Work.BoseBoxFix.LowCut} {μ ℓ κ Cθ : ℝ}
    (hℓ : 0 < ℓ) (hκ : 0 < κ) (hCθ : 0 ≤ Cθ) {i j : Fin n} {Θ : Submission.BoseGases.X n → ℝ}
    (hΘm : Measurable Θ) (hΘb : ∀ x, |Θ x| ≤ Cθ) :
    Measurable (fun y : Submission.BoseGases.X n => Work.BoseBoxFix.lowSlot fc κ ℓ j
        (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) y)
    ∧ ∃ D : ℝ, 0 ≤ D ∧ ∀ y : Submission.BoseGases.X n,
        |Work.BoseBoxFix.lowSlot fc κ ℓ j
          (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) y| ≤ D := by
  have hψm : Measurable (Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)) :=
    Work.BoseBoxFock.Weak.aQ_measurable j (Work.BoseBoxFock.Weak.aP_measurable i hΘm)
  have hψb : ∀ x, |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) x| ≤ 2 * Cθ :=
    Work.BoseBoxFock.Weak.aQ_abs_le hℓ j hCθ (Work.BoseBoxFock.Weak.aP_abs_le hℓ i hCθ hΘb)
  exact lowSlot_measurable_bounded_of_bounded hκ hℓ (by linarith) hψm hψb

end

end Work.BoseBoxFock.PCFU
