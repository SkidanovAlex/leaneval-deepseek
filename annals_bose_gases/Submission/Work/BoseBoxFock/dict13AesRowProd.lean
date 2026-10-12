import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.dict13Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Submission.BoseGases.X

/-!
# `Work.BoseBoxFock.dict13AesRowProd` — a.e. strong measurability of the `rowProd` integrand

The block-`I` dictionary `dict13_L1` integrates the `rowProd` integrand of the `Q M Q` kernel
`qmqKernel ℓ e` over the product measure `(volume ↾ abox n ℓ) × volume × volume`.  The present
lemma records the (routine, but indispensable) measurability input: for **measurable** `Θ, A, B`
and a **measurable** real pair kernel `e`, the integrand is `AEStronglyMeasurable`.

In fact it is *strongly* measurable, hence measurable, so the a.e. statement is free: the proof
below establishes `Measurable (rowProd Θ A B (qmqKernel ℓ e) p)` and concludes with
`Measurable.aestronglyMeasurable`.  No support or integrability hypothesis on `Θ` is needed: the
only non-elementary ingredient is measurability of the two one-slot box averages appearing in
`qmqKernel`, which is `StronglyMeasurable.integral_prod_right` / `integral_prod_left` (these need
no integrability hypothesis — the Bochner integral is total).
-/

/-- Measurability of the `Q M Q` kernel `(w,y) ↦ qmqKernel ℓ e w y` at a measurable real pair
kernel `e`.  The three correction rows are Bochner integrals over the cube `acube ℓ`; they are
measurable by `StronglyMeasurable.integral_prod_right`/`_left`. -/
theorem qmqKernel_measurable {ℓ : ℝ} {e : E3 → E3 → ℝ}
    (hm : Measurable (Function.uncurry e)) :
    Measurable (fun q : E3 × E3 => qmqKernel ℓ e q.1 q.2) := by
  have h1 : Measurable (fun q : E3 × E3 => ((e q.1 q.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp hm
  have h2 : Measurable (fun q : E3 × E3 =>
      ∫ y' in Submission.BoseGases.acube ℓ, ((e q.1 y' : ℝ) : ℂ)) := by
    have hsw : StronglyMeasurable (Function.uncurry (fun w y' : E3 => ((e w y' : ℝ) : ℂ))) :=
      (Complex.continuous_ofReal.measurable.comp hm).stronglyMeasurable
    exact ((hsw.integral_prod_right
      (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))).measurable).comp
      measurable_fst
  have h3 : Measurable (fun q : E3 × E3 =>
      ∫ w' in Submission.BoseGases.acube ℓ, ((e w' q.2 : ℝ) : ℂ)) := by
    have hsw : StronglyMeasurable (Function.uncurry (fun w' y : E3 => ((e w' y : ℝ) : ℂ))) :=
      (Complex.continuous_ofReal.measurable.comp hm).stronglyMeasurable
    exact ((hsw.integral_prod_left
      (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))).measurable).comp
      measurable_snd
  have h4 : Measurable (fun _ : E3 × E3 =>
      ∫ w' in Submission.BoseGases.acube ℓ,
        ∫ y' in Submission.BoseGases.acube ℓ, ((e w' y' : ℝ) : ℂ)) := measurable_const
  have hunfold : (fun q : E3 × E3 => qmqKernel ℓ e q.1 q.2) = fun q : E3 × E3 =>
      ((e q.1 q.2 : ℝ) : ℂ)
        - ((ℓ ^ 3)⁻¹ : ℝ) * (∫ y' in Submission.BoseGases.acube ℓ, ((e q.1 y' : ℝ) : ℂ))
        - ((ℓ ^ 3)⁻¹ : ℝ) * (∫ w' in Submission.BoseGases.acube ℓ, ((e w' q.2 : ℝ) : ℂ))
        + (((ℓ ^ 3)⁻¹ : ℝ) ^ 2) * (∫ w' in Submission.BoseGases.acube ℓ,
            ∫ y' in Submission.BoseGases.acube ℓ, ((e w' y' : ℝ) : ℂ)) := by
    funext q
    rw [qmqKernel, qmqRowB, qmqRowC, qmqRowD]
  rw [hunfold]
  exact ((h1.sub (measurable_const.mul h2)).sub (measurable_const.mul h3)).add
    (measurable_const.mul h4)

/-- Measurability of the `rowProd` integrand of the `Q M Q` kernel. -/
theorem rowProd_qmqKernel_measurable {n : ℕ} {ℓ : ℝ} {Θ : Xn n → ℂ} {A B : E3 → ℂ}
    {p : Fin n × Fin n} {e : E3 → E3 → ℝ}
    (hΘm : Measurable Θ) (hAm : Measurable A) (hBm : Measurable B)
    (hm : Measurable (Function.uncurry e)) :
    Measurable (rowProd Θ A B (qmqKernel ℓ e) p) := by
  change Measurable (fun z : Xn n × (E3 × E3) =>
      star (Θ z.1) * A (z.1 p.1) * qmqKernel ℓ e (z.1 p.2) z.2.1 * star (B z.2.2)
        * Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2))
  have hK : Measurable (fun q : E3 × E3 => qmqKernel ℓ e q.1 q.2) := qmqKernel_measurable hm
  have hmap : Measurable (fun z : Xn n × (E3 × E3) => (z.1 p.2, z.2.1)) := by
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_pi_apply p.2).comp measurable_fst
    · exact measurable_fst.comp measurable_snd
  have hk : Measurable (fun z : Xn n × (E3 × E3) => qmqKernel ℓ e (z.1 p.2) z.2.1) :=
    hK.comp hmap
  have hs1 : Measurable (fun z : Xn n × (E3 × E3) => star (Θ z.1)) :=
    (continuous_star.measurable.comp hΘm).comp measurable_fst
  have ha : Measurable (fun z : Xn n × (E3 × E3) => A (z.1 p.1)) :=
    hAm.comp ((measurable_pi_apply p.1).comp measurable_fst)
  have hb : Measurable (fun z : Xn n × (E3 × E3) => star (B z.2.2)) :=
    (continuous_star.measurable.comp hBm).comp (measurable_snd.comp measurable_snd)
  have hupd : Continuous (fun z : Xn n × (E3 × E3) =>
      Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2) :=
    (continuous_update p.2).comp
      (((continuous_update p.1).comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd))
  have hth : Measurable (fun z : Xn n × (E3 × E3) =>
      Θ (Function.update (Function.update z.1 p.1 z.2.1) p.2 z.2.2)) :=
    hΘm.comp hupd.measurable
  exact (((hs1.mul ha).mul hk).mul hb).mul hth

theorem dict13AesRowProd {n : ℕ} {ℓ : ℝ} {Θ : Submission.BoseGases.X n → ℂ}
    {A B : EuclideanSpace ℝ (Fin 3) → ℂ} {p : Fin n × Fin n}
    {e : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hΘm : Measurable Θ) (hAm : Measurable A) (hBm : Measurable B)
    (hm : Measurable (Function.uncurry e)) :
    AEStronglyMeasurable (Work.BoseBoxFock.rowProd Θ A B (Work.BoseBoxFock.qmqKernel ℓ e) p)
      (((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3))))) := by
  exact (rowProd_qmqKernel_measurable hΘm hAm hBm hm).aestronglyMeasurable

end Work.BoseBoxFock
