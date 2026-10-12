import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.Steps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.Split

noncomputable section

open MeasureTheory

open Submission.BoseGases

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! `lowSlot` is a twice-iterated integral (`∫_p` of `kinFT` of the slot-`j` fibre, itself `∫_z`),
so this is two applications of `MeasureTheory.StronglyMeasurable.integral_prod_right` (which needs
only joint strong measurability, NOT integrability): `((x,p),z) ↦ e^{-i⟨p,z⟩}·1_{acube ℓ}(z)·Ψ(update x j z)`
is jointly measurable, hence so is `(x,p) ↦ kinFT(...) p`, hence so is `x ↦ ∫_p ...`.

The two `∫`'s are `slotIntegrand` below: the joint `(x,p)`-integrand of `lowMult` (before the outer
`p`-integral), which is a product of three jointly strongly measurable factors:

* `A : (x,p) ↦ e^{i⟪p,x_j⟫}` — continuous;
* `B : (x,p) ↦ f(‖p‖/κ)` — continuous (only depends on `p`; `fc.smooth`);
* `C : (x,p) ↦ kinFT(1_{Λ}·fibre(x)) p` — obtained from the joint measurability of
  `((x,p),z) ↦ 1_{acube ℓ}(z)·Ψ(update x j z)` (`measurable_indicator_fibre`) via
  `StronglyMeasurable.integral_prod_right'`.

Then one more `integral_prod_right` (curried form) integrates in `p`, `.re` is continuous, and the
constant `(2π)⁻³` is a `const_mul`. -/

/-- The `p`-convention Fourier kernel `y ↦ e^{-i⟪p,y⟫}`, as a two-variable function. -/
private def fkern (p y : ℝ³) : ℂ := Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))

private lemma kinFT_eq_fkern (f : ℝ³ → ℂ) (p : ℝ³) :
    Submission.BoseGases.kinFT f p = ∫ y : ℝ³, fkern p y * f y := rfl

private lemma measurable_fkern : Measurable (fun p : ℝ³ × ℝ³ => fkern p.1 p.2) := by
  have hinner : Continuous (fun p : ℝ³ × ℝ³ => inner ℝ p.1 p.2) := continuous_inner
  exact Complex.continuous_exp.measurable.comp
    (continuous_neg.comp (continuous_const.mul (Complex.continuous_ofReal.comp hinner))).measurable

/-- The Fourier transform of a jointly strongly measurable family is strongly measurable
(unconditional: no integrability is needed, the Bochner integral is total). -/
private lemma stronglyMeasurable_kinFT_of {α : Type*} [MeasurableSpace α] {G : α → ℝ³ → ℂ}
    (hG : StronglyMeasurable (fun a : α × ℝ³ => G a.1 a.2)) :
    StronglyMeasurable (fun w : α × ℝ³ =>
      Submission.BoseGases.kinFT (fun z : ℝ³ => G w.1 z) w.2) := by
  have hfun : (fun w : α × ℝ³ => Submission.BoseGases.kinFT (fun z : ℝ³ => G w.1 z) w.2)
      = fun w : α × ℝ³ => ∫ y : ℝ³, fkern w.2 y * G w.1 y := by
    funext w
    exact kinFT_eq_fkern _ _
  rw [hfun]
  refine MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ³))
    (f := fun w : (α × ℝ³) × ℝ³ => fkern w.1.2 w.2 * G w.1.1 w.2) ?_
  exact ((measurable_fkern.comp
      (Measurable.prodMk measurable_fst.snd measurable_snd)).stronglyMeasurable).mul
    (hG.comp_measurable (Measurable.prodMk measurable_fst.fst measurable_snd))

/-- `(x,z) ↦ update x j z` is measurable. -/
private lemma measurable_update {n : ℕ} (j : Fin n) :
    Measurable (fun w : Submission.BoseGases.X n × ℝ³ => Function.update w.1 j w.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases hij : i = j
  · have h2 : (fun w : Submission.BoseGases.X n × ℝ³ => Function.update w.1 j w.2 i)
        = fun w => w.2 := by
      funext w
      rw [Function.update_apply, if_pos hij]
    rw [h2]
    exact measurable_snd
  · have h2 : (fun w : Submission.BoseGases.X n × ℝ³ => Function.update w.1 j w.2 i)
        = fun w => w.1 i := by
      funext w
      rw [Function.update_apply, if_neg hij]
    rw [h2]
    exact (measurable_pi_apply i).comp measurable_fst

/-- `((x,p),z) ↦ 1_{acube ℓ}(z)·Ψ(update x j z)` is jointly measurable. -/
private lemma measurable_indicator_fibre {n : ℕ} (j : Fin n) (ℓ : ℝ)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ) :
    Measurable (fun w : Submission.BoseGases.X n × ℝ³ =>
      (((Submission.BoseGases.acube ℓ).indicator (fun z : ℝ³ => Ψ (Function.update w.1 j z)) w.2 : ℝ) : ℂ)) := by
  classical
  have hset : MeasurableSet {w : Submission.BoseGases.X n × ℝ³ | w.2 ∈ Submission.BoseGases.acube ℓ} :=
    (Submission.BoseGases.acube_measurable ℓ).preimage measurable_snd
  have hif : Measurable (fun w : Submission.BoseGases.X n × ℝ³ =>
      if w.2 ∈ Submission.BoseGases.acube ℓ then Ψ (Function.update w.1 j w.2) else (0 : ℝ)) :=
    Measurable.ite hset (hΨ.measurable.comp (measurable_update j)) measurable_const
  have heq : (fun w : Submission.BoseGases.X n × ℝ³ =>
        (((Submission.BoseGases.acube ℓ).indicator (fun z : ℝ³ => Ψ (Function.update w.1 j z)) w.2 : ℝ) : ℂ))
      = fun w => ((if w.2 ∈ Submission.BoseGases.acube ℓ then Ψ (Function.update w.1 j w.2)
          else (0 : ℝ) : ℝ) : ℂ) := by
    funext w
    rw [Set.indicator_apply]
  rw [heq]
  exact Complex.continuous_ofReal.measurable.comp hif

/-- The joint `(x,p)`-integrand of `lowMult` (before the outer `p`-integral). -/
private def slotIntegrand {n : ℕ} (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (j : Fin n)
    (Ψ : Submission.BoseGases.X n → ℝ) (x : Submission.BoseGases.X n) (p : ℝ³) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ p (x j) : ℂ)) * ((fc.f (‖p‖ / κ) : ℝ) : ℂ) *
    Submission.BoseGases.kinFT (fun z : ℝ³ =>
      (((Submission.BoseGases.acube ℓ).indicator (fun z : ℝ³ => Ψ (Function.update x j z)) z : ℝ) : ℂ)) p

private lemma re_ofReal_mul (c : ℝ) (z : ℂ) : c * z.re = (c * z).re := by simp

theorem lowSlotStronglyMeasurable {fc : Work.BoseBoxFix.LowCut} {κ ℓ : ℝ}
    {n : ℕ} (j : Fin n) {Ψ : Submission.BoseGases.X n → ℝ} (hΨ : Continuous Ψ) :
    MeasureTheory.StronglyMeasurable
      (fun x : Submission.BoseGases.X n => Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x) := by
  -- joint strong measurability of the `(x,p)`-integrand
  have hjoint : StronglyMeasurable (fun w : Submission.BoseGases.X n × ℝ³ =>
      slotIntegrand fc κ ℓ j Ψ w.1 w.2) := by
    have hA : StronglyMeasurable (fun w : Submission.BoseGases.X n × ℝ³ =>
        Complex.exp (Complex.I * (inner ℝ w.2 (w.1 j) : ℂ))) := by
      have hcont : Continuous (fun w : Submission.BoseGases.X n × ℝ³ => inner ℝ w.2 (w.1 j)) :=
        continuous_inner.comp (continuous_snd.prodMk ((continuous_apply j).comp continuous_fst))
      exact (Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp hcont))).measurable.stronglyMeasurable
    have hB : StronglyMeasurable (fun w : Submission.BoseGases.X n × ℝ³ =>
        ((fc.f (‖w.2‖ / κ) : ℝ) : ℂ)) := by
      have hcont : Continuous (fun w : Submission.BoseGases.X n × ℝ³ => fc.f (‖w.2‖ / κ)) :=
        fc.smooth.continuous.comp ((continuous_norm.comp continuous_snd).div_const κ)
      exact (Complex.continuous_ofReal.comp hcont).measurable.stronglyMeasurable
    have hC : StronglyMeasurable (fun w : Submission.BoseGases.X n × ℝ³ =>
        Submission.BoseGases.kinFT (fun z : ℝ³ =>
          (((Submission.BoseGases.acube ℓ).indicator
            (fun z : ℝ³ => Ψ (Function.update w.1 j z)) z : ℝ) : ℂ)) w.2) :=
      stronglyMeasurable_kinFT_of (α := Submission.BoseGases.X n)
        (G := fun a z => (((Submission.BoseGases.acube ℓ).indicator
          (fun z : ℝ³ => Ψ (Function.update a j z)) z : ℝ) : ℂ))
        (measurable_indicator_fibre j ℓ hΨ).stronglyMeasurable
    convert (hA.mul hB).mul hC using 1
    · funext w
      rfl
  -- the inner `z`-integral is already consumed by `hjoint`; integrate in `p`
  have hint : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
      ∫ p : ℝ³, slotIntegrand fc κ ℓ j Ψ x p) :=
    hjoint.integral_prod_right (ν := MeasureTheory.volume)
  have h1 : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
      (∫ p : ℝ³, slotIntegrand fc κ ℓ j Ψ x p).re) :=
    Complex.continuous_re.comp_stronglyMeasurable hint
  have h2 : StronglyMeasurable (fun x : Submission.BoseGases.X n =>
      (((2 * Real.pi) ^ 3)⁻¹ : ℝ) * (∫ p : ℝ³, slotIntegrand fc κ ℓ j Ψ x p).re) :=
    h1.const_mul _
  have hgoal : (fun x : Submission.BoseGases.X n =>
        (((2 * Real.pi) ^ 3)⁻¹ : ℝ) * (∫ p : ℝ³, slotIntegrand fc κ ℓ j Ψ x p).re)
      = fun x : Submission.BoseGases.X n => Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x := by
    funext x
    rw [Work.BoseBoxFix.lowSlot, Work.BoseBoxFix.lowMult]
    simp only [slotIntegrand, ← re_ofReal_mul]
  rw [← hgoal]
  exact h2

end

end Work.BoseFixB3.Split
