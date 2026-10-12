import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB3.Conv.stronglyMeasurable_lowMult
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.measurable_lowMult_family`

For a jointly continuous `G : ℝ³ → ℝ³ → ℝ` and a fixed evaluation point `x₀`, the map
`y ↦ Work.BoseBoxFix.lowMult fc κ ℓ (G y) x₀` is measurable.

`lowMult` is a momentum integral, so this is (exactly as in
`Work.BoseFixB3.Conv.stronglyMeasurable_lowMult`, but with a family parameter) two
applications of `MeasureTheory.StronglyMeasurable.integral_prod_right`:

* `(y,p) ↦ kinFT(1_{acube ℓ}·(G y)) p` is the `z`-integral of the jointly measurable kernel
  `((y,p),z) ↦ e^{-i⟪p,z⟫}·1_{acube ℓ}(z)·G y z`, hence jointly strongly measurable;
* multiplying by the continuous factors `(y,p) ↦ e^{i⟪p,x₀⟫}` and `(y,p) ↦ f(‖p‖/κ)` and
  integrating in `p` gives strong measurability of `y ↦ ∫_p ...`, hence of its real part
  times the constant `(2π)⁻³`, which is `lowMult`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.CS.Pieces

set_option maxHeartbeats 800000

/-- The `p`-convention Fourier kernel `y ↦ e^{-i⟪p,y⟫}`. -/
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

private lemma re_ofReal_mul (c : ℝ) (z : ℂ) : c * z.re = (c * z).re := by simp

/-- The joint `(y,p)`-integrand of `lowMult` for the family `y ↦ G y` (before the outer
`p`-integral). -/
private def famIntegrand (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ) (x₀ : ℝ³)
    (H : ℝ³ → ℝ³ → ℝ) (y p : ℝ³) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ p x₀ : ℂ)) * Complex.ofReal (fc.f (‖p‖ / κ)) *
    Submission.BoseGases.kinFT (fun z : ℝ³ =>
      Complex.ofReal ((Submission.BoseGases.acube ℓ).indicator (fun z : ℝ³ => H y z) z)) p

theorem measurable_lowMult_family (fc : Work.BoseBoxFix.LowCut) (κ ℓ : ℝ)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hG : Continuous (Function.uncurry G)) (x₀ : EuclideanSpace ℝ (Fin 3)) :
    Measurable (fun y : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseBoxFix.lowMult fc κ ℓ (fun z => G y z) x₀) := by
  have hGm : Measurable (fun w : ℝ³ × ℝ³ => G w.1 w.2) := hG.measurable
  -- the box-restricted family `(y,z) ↦ 1_{acube ℓ}(z)·G y z` is jointly measurable
  have hInd : Measurable (fun w : ℝ³ × ℝ³ =>
      Complex.ofReal ((Submission.BoseGases.acube ℓ).indicator (fun z : ℝ³ => G w.1 z) w.2)) := by
    classical
    have hset : MeasurableSet
        {w : ℝ³ × ℝ³ | w.2 ∈ Submission.BoseGases.acube ℓ} :=
      (Submission.BoseGases.acube_measurable ℓ).preimage measurable_snd
    have hif : Measurable (fun w : ℝ³ × ℝ³ =>
        if w.2 ∈ Submission.BoseGases.acube ℓ then G w.1 w.2 else (0 : ℝ)) :=
      Measurable.ite hset hGm measurable_const
    have heq : (fun w : ℝ³ × ℝ³ =>
          Complex.ofReal ((Submission.BoseGases.acube ℓ).indicator (fun z : ℝ³ => G w.1 z) w.2))
        = fun w : ℝ³ × ℝ³ =>
          Complex.ofReal (if w.2 ∈ Submission.BoseGases.acube ℓ then G w.1 w.2 else (0 : ℝ)) := by
      funext w
      rw [Set.indicator_apply]
    rw [heq]
    exact Complex.continuous_ofReal.measurable.comp hif
  -- strong measurability of the `(y,p)`-integrand
  have hC : StronglyMeasurable (fun w : ℝ³ × ℝ³ =>
      Submission.BoseGases.kinFT (fun z : ℝ³ =>
        Complex.ofReal ((Submission.BoseGases.acube ℓ).indicator
          (fun z : ℝ³ => G w.1 z) z)) w.2) :=
    stronglyMeasurable_kinFT_of (α := ℝ³)
      (G := fun a z => Complex.ofReal ((Submission.BoseGases.acube ℓ).indicator
        (fun z : ℝ³ => G a z) z)) hInd.stronglyMeasurable
  have hA : StronglyMeasurable (fun w : ℝ³ × ℝ³ =>
      Complex.exp (Complex.I * (inner ℝ w.2 x₀ : ℂ))) := by
    have hcont : Continuous (fun w : ℝ³ × ℝ³ => inner ℝ w.2 x₀) :=
      continuous_inner.comp (continuous_snd.prodMk continuous_const)
    exact (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hcont))).measurable.stronglyMeasurable
  have hB : StronglyMeasurable (fun w : ℝ³ × ℝ³ => Complex.ofReal (fc.f (‖w.2‖ / κ))) := by
    have hcont : Continuous (fun w : ℝ³ × ℝ³ => fc.f (‖w.2‖ / κ)) :=
      fc.smooth.continuous.comp ((continuous_norm.comp continuous_snd).div_const κ)
    exact (Complex.continuous_ofReal.comp hcont).measurable.stronglyMeasurable
  have hjoint : StronglyMeasurable (fun w : ℝ³ × ℝ³ => famIntegrand fc κ ℓ x₀ G w.1 w.2) := by
    convert (hA.mul hB).mul hC using 1
    funext w
    rfl
  -- integrate in the momentum variable `p`
  have hint : StronglyMeasurable (fun y : ℝ³ => ∫ p : ℝ³, famIntegrand fc κ ℓ x₀ G y p) :=
    hjoint.integral_prod_right (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ³))
  have h1 : StronglyMeasurable (fun y : ℝ³ =>
      (∫ p : ℝ³, famIntegrand fc κ ℓ x₀ G y p).re) :=
    Complex.continuous_re.comp_stronglyMeasurable hint
  have h2 : StronglyMeasurable (fun y : ℝ³ =>
      (((2 * Real.pi) ^ 3)⁻¹ : ℝ) * (∫ p : ℝ³, famIntegrand fc κ ℓ x₀ G y p).re) :=
    h1.const_mul _
  have hgoal : (fun y : ℝ³ =>
        (((2 * Real.pi) ^ 3)⁻¹ : ℝ) * (∫ p : ℝ³, famIntegrand fc κ ℓ x₀ G y p).re)
      = fun y : ℝ³ => Work.BoseBoxFix.lowMult fc κ ℓ (fun z => G y z) x₀ := by
    funext y
    rw [Work.BoseBoxFix.lowMult]
    simp only [famIntegrand, ← re_ofReal_mul]
  rw [← hgoal]
  exact h2.measurable

end Work.BoseFixB3.CS.Pieces
