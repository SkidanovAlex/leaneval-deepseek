import Mathlib.Analysis.Convolution
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- The plane wave `x ↦ e^{-i⟪p,x⟫}`, i.e. the kernel of the (unnormalised) Fourier transform
appearing in `kinFT_conv_pair`. -/
noncomputable def pw (p x : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp (-(Complex.I * (inner ℝ p x : ℂ)))

/-- The plane wave is a character of the additive group. -/
lemma pw_add (p x y : EuclideanSpace ℝ (Fin 3)) : pw p (x + y) = pw p x * pw p y := by
  simp only [pw, ← Complex.exp_add]
  congr 1
  rw [inner_add_right]
  push_cast
  ring

/-- The plane wave has unit modulus. -/
lemma norm_pw (p x : EuclideanSpace ℝ (Fin 3)) : ‖pw p x‖ = 1 := by
  simp only [pw]
  rw [show -(Complex.I * (inner ℝ p x : ℂ)) = ((-(inner ℝ p x) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The plane wave is continuous. -/
lemma continuous_pw (p : EuclideanSpace ℝ (Fin 3)) : Continuous (pw p) := by
  unfold pw
  fun_prop

lemma aestronglyMeasurable_pw (p : EuclideanSpace ℝ (Fin 3)) :
    AEStronglyMeasurable (pw p) volume :=
  (continuous_pw p).aestronglyMeasurable

/-- Multiplication by the (bounded, measurable) plane wave preserves integrability. -/
lemma integrable_mul_pw {f : EuclideanSpace ℝ (Fin 3) → ℂ} (hf : Integrable f volume)
    (p : EuclideanSpace ℝ (Fin 3)) : Integrable (fun x => f x * pw p x) volume :=
  hf.mul_bdd (aestronglyMeasurable_pw p) (Filter.Eventually.of_forall fun x => by rw [norm_pw])

/-- The mixed integrand `(x,u) ↦ W x · h (u - x) · e^{-i⟪p,u⟫}` appearing in the Fubini step of
`kinFT_conv_pair` is integrable on the product measure.  This is the standard statement that the
convolution integrand of two `L¹` functions is integrable (`Integrable.convolution_integrand`),
transposed by the measure preserving coordinate swap. -/
lemma integrable_conv_pair_integrand {W h : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : Integrable W) (hh : Integrable h) (p : EuclideanSpace ℝ (Fin 3)) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ((W z.1 * h (z.2 - z.1) : ℝ) : ℂ) * pw p z.2) (volume.prod volume) := by
  have hbase : Integrable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (W z.2 : ℂ) * (h (z.1 - z.2) : ℂ)) (volume.prod volume) :=
    Integrable.convolution_integrand (L := ContinuousLinearMap.mul ℂ ℂ)
      (f := fun x : EuclideanSpace ℝ (Fin 3) => (W x : ℂ))
      (g := fun x : EuclideanSpace ℝ (Fin 3) => (h x : ℂ)) hW.ofReal hh.ofReal
  have hmp : MeasurePreserving
      (Prod.swap : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) →
        EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))
      (volume.prod volume) (volume.prod volume) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  have hbase2 : Integrable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (W z.1 : ℂ) * (h (z.2 - z.1) : ℂ)) (volume.prod volume) :=
    (hmp.integrable_comp hbase.aestronglyMeasurable).mpr hbase
  have hbase3 : Integrable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ((W z.1 : ℂ) * (h (z.2 - z.1) : ℂ)) * pw p z.2) (volume.prod volume) :=
    hbase2.mul_bdd ((continuous_pw p).comp continuous_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [norm_pw])
  exact hbase3.congr (Filter.Eventually.of_forall fun z => by simp only [Complex.ofReal_mul])

theorem kinFT_conv_pair {W h : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (hh : MeasureTheory.Integrable h) (p : EuclideanSpace ℝ (Fin 3)) :
    (∫ x : EuclideanSpace ℝ (Fin 3), (W x : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p x : ℂ))))
      * (∫ y : EuclideanSpace ℝ (Fin 3), (h y : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))))
    = ∫ u : EuclideanSpace ℝ (Fin 3),
        (((∫ x : EuclideanSpace ℝ (Fin 3), W x * h (u - x) : ℝ)) : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ p u : ℂ))) := by
  change (∫ x : EuclideanSpace ℝ (Fin 3), (W x : ℂ) * pw p x)
      * (∫ y : EuclideanSpace ℝ (Fin 3), (h y : ℂ) * pw p y)
    = ∫ u : EuclideanSpace ℝ (Fin 3),
        (((∫ x : EuclideanSpace ℝ (Fin 3), W x * h (u - x) : ℝ)) : ℂ) * pw p u
  -- Step 1: pull the product of integrals inside as a product integral.
  have hprod : Integrable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ((W z.1 : ℂ) * pw p z.1) * ((h z.2 : ℂ) * pw p z.2)) (volume.prod volume) :=
    (integrable_mul_pw hW.ofReal p).mul_prod (integrable_mul_pw hh.ofReal p)
  have hprod' : Integrable (fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ((W z.1 * h z.2 : ℝ) : ℂ) * pw p (z.1 + z.2)) (volume.prod volume) :=
    hprod.congr (Filter.Eventually.of_forall fun z => by
      simp only [Complex.ofReal_mul, pw_add]; ring)
  have hstep1 : (∫ x : EuclideanSpace ℝ (Fin 3), (W x : ℂ) * pw p x)
      * (∫ y : EuclideanSpace ℝ (Fin 3), (h y : ℂ) * pw p y)
      = ∫ z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3),
          ((W z.1 * h z.2 : ℝ) : ℂ) * pw p (z.1 + z.2) ∂(volume.prod volume) := by
    rw [← MeasureTheory.integral_prod_mul
      (f := fun x : EuclideanSpace ℝ (Fin 3) => (W x : ℂ) * pw p x)
      (g := fun y : EuclideanSpace ℝ (Fin 3) => (h y : ℂ) * pw p y)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      simp only [Complex.ofReal_mul, pw_add]; ring)
  rw [hstep1]
  -- Step 2: Fubini, and substitute `u = x + y` in the inner integral.
  rw [MeasureTheory.integral_prod
    (f := fun z : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      ((W z.1 * h z.2 : ℝ) : ℂ) * pw p (z.1 + z.2)) hprod']
  trans ∫ x : EuclideanSpace ℝ (Fin 3), ∫ u : EuclideanSpace ℝ (Fin 3),
      ((W x * h (u - x) : ℝ) : ℂ) * pw p u ∂volume ∂volume
  · apply integral_congr_ae
    filter_upwards with x
    have h := MeasureTheory.integral_add_left_eq_self (μ := volume)
      (fun w : EuclideanSpace ℝ (Fin 3) => ((W x * h (w - x) : ℝ) : ℂ) * pw p w) x
    simpa [add_sub_cancel_left] using h
  -- Step 3: Fubini again, and pull out the constant `pw p u`.
  rw [MeasureTheory.integral_integral_swap (f := fun x u : EuclideanSpace ℝ (Fin 3) =>
        ((W x * h (u - x) : ℝ) : ℂ) * pw p u)
      (integrable_conv_pair_integrand hW hh p)]
  apply integral_congr_ae
  filter_upwards with u
  rw [MeasureTheory.integral_mul_const]
  congr 1
  exact integral_ofReal

end Work.BoseBoxFock
