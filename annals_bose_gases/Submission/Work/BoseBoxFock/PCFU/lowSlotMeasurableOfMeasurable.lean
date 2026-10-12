import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PCFU.dictBricks
import Submission.Work.BoseFixB3.Split.lowSlotStronglyMeasurable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

noncomputable section

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-! ## Measurability of the slot-`j` low-momentum lift for a *measurable* state

`Work.BoseBoxFix.lowSlot fc κ ℓ j ψ x` is the Fourier multiplier `f(‖p‖/κ)` applied slotwise, an
iterated integral

    lowSlot fc κ ℓ j ψ x
      = ((2π)³)⁻¹ · (∫_p e^{i⟪p,x_j⟫} · f(‖p‖/κ) · kinFT(1_{acube ℓ}·ψ∘update x j ⋅) p).re

(`Submission.Work.BoseBoxFix.Defs`).  Every ingredient is measurable in `x` as soon as `ψ` is: the
`p`-dependent prefactor is *continuous* in `x`, and the state enters only through the joint
measurability of `((x,p),z) ↦ 1_{acube ℓ}(z)·ψ((update x j z))`, which is `Measurable ψ` composed
with the measurable `update` map.  Fubini-type measurability of the Bochner integral `∫_p`
(`MeasureTheory.StronglyMeasurable.integral_prod_right`) requires **no** integrability, since the
Bochner integral is total.

(The continuous-state version `Work.BoseFixB3.Split.lowSlotStronglyMeasurable` is the same proof
with `Continuous ψ`; here measurability suffices.) -/

/-- The `p`-convention Fourier kernel `y ↦ e^{-i⟪p,y⟫}`, as a two-variable function. -/
private def fkern (p y : E3) : ℂ := Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))

private lemma kinFT_eq_fkern (f : E3 → ℂ) (p : E3) :
    Submission.BoseGases.kinFT f p = ∫ y : E3, fkern p y * f y := rfl

private lemma measurable_fkern : Measurable (fun p : E3 × E3 => fkern p.1 p.2) := by
  have hinner : Continuous (fun p : E3 × E3 => inner ℝ p.1 p.2) := continuous_inner
  exact Complex.continuous_exp.measurable.comp
    (continuous_neg.comp (continuous_const.mul (Complex.continuous_ofReal.comp hinner))).measurable

/-- The Fourier transform of a jointly strongly measurable family is strongly measurable
(unconditional: no integrability is needed, the Bochner integral is total). -/
private lemma stronglyMeasurable_kinFT_of {α : Type*} [MeasurableSpace α] {G : α → E3 → ℂ}
    (hG : StronglyMeasurable (fun a : α × E3 => G a.1 a.2)) :
    StronglyMeasurable (fun w : α × E3 =>
      Submission.BoseGases.kinFT (fun z : E3 => G w.1 z) w.2) := by
  have hfun : (fun w : α × E3 => Submission.BoseGases.kinFT (fun z : E3 => G w.1 z) w.2)
      = fun w : α × E3 => ∫ y : E3, fkern w.2 y * G w.1 y := by
    funext w
    exact kinFT_eq_fkern _ _
  rw [hfun]
  refine MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := (MeasureTheory.volume : MeasureTheory.Measure E3))
    (f := fun w : (α × E3) × E3 => fkern w.1.2 w.2 * G w.1.1 w.2) ?_
  exact ((measurable_fkern.comp
      (Measurable.prodMk measurable_fst.snd measurable_snd)).stronglyMeasurable).mul
    (hG.comp_measurable (Measurable.prodMk measurable_fst.fst measurable_snd))

/-- `(x,z) ↦ update x j z` is measurable. -/
private lemma measurable_update {n : ℕ} (j : Fin n) :
    Measurable (fun w : Submission.BoseGases.X n × E3 => Function.update w.1 j w.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hij : i = j
  · have h2 : (fun w : Submission.BoseGases.X n × E3 => Function.update w.1 j w.2 i)
        = fun w => w.2 := by
      funext w
      rw [Function.update_apply, if_pos hij]
    rw [h2]
    exact measurable_snd
  · have h2 : (fun w : Submission.BoseGases.X n × E3 => Function.update w.1 j w.2 i)
        = fun w => w.1 i := by
      funext w
      rw [Function.update_apply, if_neg hij]
    rw [h2]
    exact (measurable_pi_apply i).comp measurable_fst

/-- `((x,p),z) ↦ 1_{acube ℓ}(z)·ψ(update x j z)` is jointly measurable — the only place where the
state is used, and where `Continuous ψ` may be relaxed to `Measurable ψ`. -/
private lemma measurable_indicator_fibre {n : ℕ} (j : Fin n) (ℓ : ℝ)
    {ψ : Submission.BoseGases.X n → ℝ} (hψ : Measurable ψ) :
    Measurable (fun w : Submission.BoseGases.X n × E3 =>
      (((Submission.BoseGases.acube ℓ).indicator
        (fun z : E3 => ψ (Function.update w.1 j z)) w.2 : ℝ) : ℂ)) := by
  classical
  have hset : MeasurableSet
      {w : Submission.BoseGases.X n × E3 | w.2 ∈ Submission.BoseGases.acube ℓ} :=
    (Submission.BoseGases.acube_measurable ℓ).preimage measurable_snd
  have hif : Measurable (fun w : Submission.BoseGases.X n × E3 =>
      if w.2 ∈ Submission.BoseGases.acube ℓ then ψ (Function.update w.1 j w.2) else (0 : ℝ)) :=
    Measurable.ite hset (hψ.comp (measurable_update j)) measurable_const
  have heq : (fun w : Submission.BoseGases.X n × E3 =>
        (((Submission.BoseGases.acube ℓ).indicator
          (fun z : E3 => ψ (Function.update w.1 j z)) w.2 : ℝ) : ℂ))
      = fun w => ((if w.2 ∈ Submission.BoseGases.acube ℓ then ψ (Function.update w.1 j w.2)
          else (0 : ℝ) : ℝ) : ℂ) := by
    funext w
    rw [Set.indicator_apply]
  rw [heq]
  exact Complex.continuous_ofReal.measurable.comp hif

/-- The joint `(x,p)`-integrand of `lowMult` (before the outer `p`-integral). -/
private def slotIntegrand {n : ℕ} (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (j : Fin n)
    (Ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) (p : E3) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ p (x j) : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
    Submission.BoseGases.kinFT (fun z : E3 =>
      (((Submission.BoseGases.acube ℓ).indicator
        (fun z : E3 => Ψ (Function.update x j z)) z : ℝ) : ℂ)) p

private lemma re_ofReal_mul (c : ℝ) (z : ℂ) : c * z.re = (c * z).re := by simp

/-- **Measurability of the slot-`j` low-momentum lift for a measurable state.** -/
theorem lowSlotMeasurableOfMeasurable {n : ℕ} (fc : Work.BoseBoxFix.LowCut) {κ ℓ : ℝ}
    (j : Fin n) {ψ : Submission.BoseGases.X n → ℝ} (hψm : Measurable ψ) :
    Measurable (fun x : Submission.BoseGases.X n => Work.BoseBoxFix.lowSlot fc κ ℓ j ψ x) := by
  -- joint strong measurability of the `(x,p)`-integrand
  have hjoint : StronglyMeasurable (fun w : Submission.BoseGases.X n × E3 =>
      slotIntegrand fc κ ℓ j ψ w.1 w.2) := by
    have hA : StronglyMeasurable (fun w : Submission.BoseGases.X n × E3 =>
        Complex.exp (Complex.I * (inner ℝ w.2 (w.1 j) : ℂ))) := by
      have hcont : Continuous (fun w : Submission.BoseGases.X n × E3 => inner ℝ w.2 (w.1 j)) :=
        continuous_inner.comp (continuous_snd.prodMk ((continuous_apply j).comp continuous_fst))
      exact (Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp hcont))).measurable.stronglyMeasurable
    have hB : StronglyMeasurable (fun w : Submission.BoseGases.X n × E3 =>
        ((fc.f (‖w.2‖ / κ) : ℝ) : ℂ)) := by
      have hcont : Continuous (fun w : Submission.BoseGases.X n × E3 => fc.f (‖w.2‖ / κ)) :=
        fc.smooth.continuous.comp ((continuous_norm.comp continuous_snd).div_const κ)
      exact (Complex.continuous_ofReal.comp hcont).measurable.stronglyMeasurable
    have hC : StronglyMeasurable (fun w : Submission.BoseGases.X n × E3 =>
        Submission.BoseGases.kinFT (fun z : E3 =>
          (((Submission.BoseGases.acube ℓ).indicator
            (fun z : E3 => ψ (Function.update w.1 j z)) z : ℝ) : ℂ)) w.2) :=
      stronglyMeasurable_kinFT_of (α := Submission.BoseGases.X n)
        (G := fun a z => (((Submission.BoseGases.acube ℓ).indicator
          (fun z : E3 => ψ (Function.update a j z)) z : ℝ) : ℂ))
        (measurable_indicator_fibre j ℓ hψm).stronglyMeasurable
    convert (hA.mul hB).mul hC using 1
    · funext w
      rfl
  -- the inner `z`-integral is already consumed by `hjoint`; integrate in `p`
  have hint : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
      ∫ p : E3, slotIntegrand fc κ ℓ j ψ x p) :=
    hjoint.integral_prod_right (ν := MeasureTheory.volume)
  have h1 : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
      (∫ p : E3, slotIntegrand fc κ ℓ j ψ x p).re) :=
    Complex.continuous_re.comp_stronglyMeasurable hint
  have h2 : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
      (((2 * Real.pi) ^ 3)⁻¹ : ℝ) * (∫ p : E3, slotIntegrand fc κ ℓ j ψ x p).re) :=
    h1.const_mul _
  have hgoal : (fun x : Submission.BoseGases.X n =>
        (((2 * Real.pi) ^ 3)⁻¹ : ℝ) * (∫ p : E3, slotIntegrand fc κ ℓ j ψ x p).re)
      = fun x : Submission.BoseGases.X n => Work.BoseBoxFix.lowSlot fc κ ℓ j ψ x := by
    funext x
    rw [Work.BoseBoxFix.lowSlot, Work.BoseBoxFix.lowMult]
    simp only [slotIntegrand, ← re_ofReal_mul]
  rw [← hgoal]
  exact h2.measurable

end

end Work.BoseBoxFock.PCFU
