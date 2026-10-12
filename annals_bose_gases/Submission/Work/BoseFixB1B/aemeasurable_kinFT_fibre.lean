import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Submission.Work.SmallBoxBridge.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.aemeasurable_kinFT_fibre`

Fibre measurability of the windowed kinetic word: for an a.e.-measurable `Φ` on the
`(n+1)`-particle configuration space and a continuous window `χ`, the function

`r ↦ ‖kinFT (z ↦ χ z · Φ (kcInsN n i (z, r))) p‖²`

is a.e.-strongly-measurable on `X n` with respect to `volume`.

The argument is purely measure-theoretic:

* the insertion `kcInsN n i : ℝ³ × X n → X (n+1)` is measure-preserving
  (`kc_mp_insN`), so `Φ ∘ kcInsN n i` is a.e.-measurable on the product measure
  (`AEMeasurable.comp_measurable` along the measured pullback);
* multiplying by the continuous (hence measurable) factor `χ(z)·e^{−i⟪p,z⟫}` keeps
  a.e.-strong measurability on the product;
* swapping the two variables (`Measure.prod_swap`) and applying Fubini for the
  Bochner integral (`AEStronglyMeasurable.integral_prod_right'`, which needs no
  integrability hypothesis) makes the parametrised integral a.e.-strongly-measurable
  in `r`;
* composing with the continuous map `x ↦ ‖x‖²` concludes.
-/

namespace Work.BoseFixB1B

open MeasureTheory
open Submission.BoseGases

theorem aemeasurable_kinFT_fibre {n : ℕ} {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : Continuous χ)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦm : AEMeasurable Φ (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (n + 1))))
    (i : Fin (n + 1)) (p : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.AEStronglyMeasurable (fun r : Submission.BoseGases.X n =>
        ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) =>
          (χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)) p‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) := by
  have hmap : Measure.map (⇑(Submission.BoseGases.kcInsN n i))
      (volume : Measure (Submission.BoseGases.kcE3 × Submission.BoseGases.X n))
      = (volume : Measure (Submission.BoseGases.X (n + 1))) :=
    (Submission.BoseGases.kc_mp_insN n i).map_eq
  have hΦm' : AEMeasurable Φ (Measure.map (⇑(Submission.BoseGases.kcInsN n i))
      (volume : Measure (Submission.BoseGases.kcE3 × Submission.BoseGases.X n))) := by
    rw [hmap]; exact hΦm
  have hj : AEMeasurable (fun q : Submission.BoseGases.kcE3 × Submission.BoseGases.X n =>
      Φ (Submission.BoseGases.kcInsN n i q))
      (volume : Measure (Submission.BoseGases.kcE3 × Submission.BoseGases.X n)) :=
    AEMeasurable.comp_measurable (f := ⇑(Submission.BoseGases.kcInsN n i)) hΦm'
      (Submission.BoseGases.kcInsN n i).measurable
  have hG : AEStronglyMeasurable (fun q : Submission.BoseGases.kcE3 × Submission.BoseGases.X n =>
      (χ q.1 : ℂ) * (Φ (Submission.BoseGases.kcInsN n i q) : ℂ))
      (volume : Measure (Submission.BoseGases.kcE3 × Submission.BoseGases.X n)) :=
    (((hχ.measurable.comp measurable_fst).aemeasurable.complex_ofReal).mul
      hj.complex_ofReal).aestronglyMeasurable
  have hexp : AEStronglyMeasurable (fun q : Submission.BoseGases.kcE3 × Submission.BoseGases.X n =>
      Complex.exp (-(Complex.I * (inner ℝ p q.1 : ℂ))))
      (volume : Measure (Submission.BoseGases.kcE3 × Submission.BoseGases.X n)) :=
    (Complex.continuous_exp.measurable.comp (by fun_prop)).aestronglyMeasurable
  have hF : AEStronglyMeasurable (fun q : Submission.BoseGases.kcE3 × Submission.BoseGases.X n =>
      Complex.exp (-(Complex.I * (inner ℝ p q.1 : ℂ))) *
        ((χ q.1 : ℂ) * (Φ (Submission.BoseGases.kcInsN n i q) : ℂ)))
      (volume : Measure (Submission.BoseGases.kcE3 × Submission.BoseGases.X n)) :=
    hexp.mul hG
  have hFmap : AEStronglyMeasurable (fun q : Submission.BoseGases.kcE3 × Submission.BoseGases.X n =>
      Complex.exp (-(Complex.I * (inner ℝ p q.1 : ℂ))) *
        ((χ q.1 : ℂ) * (Φ (Submission.BoseGases.kcInsN n i q) : ℂ)))
      (Measure.map Prod.swap ((volume : Measure (Submission.BoseGases.X n)).prod
        (volume : Measure (Submission.BoseGases.kcE3)))) := by
    rw [Measure.prod_swap]; exact hF
  have hFs : AEStronglyMeasurable (fun q : Submission.BoseGases.X n × Submission.BoseGases.kcE3 =>
      Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ))) *
        ((χ q.2 : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (q.2, q.1)) : ℂ)))
      ((volume : Measure (Submission.BoseGases.X n)).prod
        (volume : Measure (Submission.BoseGases.kcE3))) :=
    AEStronglyMeasurable.comp_measurable (f := Prod.swap)
      (μ := (volume : Measure (Submission.BoseGases.X n)).prod
        (volume : Measure (Submission.BoseGases.kcE3)))
      hFmap measurable_swap
  have hI : AEStronglyMeasurable (fun r : Submission.BoseGases.X n =>
      ∫ z : Submission.BoseGases.kcE3,
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          ((χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)))
      (volume : Measure (Submission.BoseGases.X n)) :=
    hFs.integral_prod_right'
  have hsq : AEStronglyMeasurable (fun r : Submission.BoseGases.X n =>
      ‖(∫ z : Submission.BoseGases.kcE3,
        Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          ((χ z : ℂ) * (Φ (Submission.BoseGases.kcInsN n i (z, r)) : ℂ)))‖ ^ 2)
      (volume : Measure (Submission.BoseGases.X n)) :=
    (continuous_norm.pow 2).comp_aestronglyMeasurable hI
  simpa [Submission.BoseGases.kinFT] using hsq

end Work.BoseFixB1B
