import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

/-- **The fibre sandwich at the box projection** (FS's `P_{B,i}` with the box indicator,
`Work.UBBInputs8.boxPInd`): multiplying a `P_i`-fixed state by a fibre weight `w₁(y_i)` and
projecting back in the same slot multiplies it by the box average of the fibre mass

  `boxM1 ℓ A w₁ / volA = (volA⁻¹ ∫_A w1Fibre ℓ w₁)`.

This is a purely formal identity: after unfolding `boxPInd` the factor `w₁(y_i)` becomes an
independent variable `z` of the `A`-integral, the inner integral `∫_A Ψ(update x i z')` is
independent of `z` (by `Function.update_idem`), and inside `A` the box indicator is `1`, so the
`z`-integral collapses to `boxM1` times that constant. -/
theorem fibreSandwichB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfib : MeasureTheory.IntegrableOn (Submission.BoseGases.w1Fibre ℓ w₁) A MeasureTheory.volume)
    (i : Fin N) {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ)
    {CΨ : ℝ} (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ CΨ) :
    (fun x => Work.UBBInputs8.boxPInd volA A i
        (fun y => Submission.BoseGases.w1Fibre ℓ w₁ (y i)
          * (Work.UBBInputs8.boxPInd volA A i Ψ) y) x)
      = fun x => (Work.BoseFixB1S.boxM1 ℓ A w₁ / volA)
          * Work.UBBInputs8.boxPInd volA A i Ψ x := by
  funext x
  -- unfold both projections and normalise the two `Function.update`s
  simp only [Work.UBBInputs8.boxPInd, Work.BoseFixB1S.boxM1, Function.update_idem,
    Function.update_apply, if_true]
  -- the inner integral `∫_A Ψ(update x i z')` does not depend on the integration variable `z`,
  -- and on `A` the box indicator is `1`
  have hK : (∫ z in A, Submission.BoseGases.w1Fibre ℓ w₁ z *
        ((1 / volA * ∫ z' in A, Ψ (Function.update x i z')) * A.indicator (fun _ => 1) z))
      = (∫ z in A, Submission.BoseGases.w1Fibre ℓ w₁ z)
        * (1 / volA * ∫ z' in A, Ψ (Function.update x i z')) := by
    rw [show (∫ z in A, Submission.BoseGases.w1Fibre ℓ w₁ z *
          ((1 / volA * ∫ z' in A, Ψ (Function.update x i z')) * A.indicator (fun _ => 1) z))
        = ∫ z in A, (Submission.BoseGases.w1Fibre ℓ w₁ z * A.indicator (fun _ => 1) z)
            * (1 / volA * ∫ z' in A, Ψ (Function.update x i z')) from
      MeasureTheory.setIntegral_congr_fun hA (fun z _ => by ring)]
    rw [MeasureTheory.integral_mul_const]
    congr 1
    exact MeasureTheory.setIntegral_congr_fun hA (fun z hz => by simp [Set.indicator_of_mem hz])
  rw [hK]
  ring

end Work.BoseFixB1S
