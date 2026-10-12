import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.KinRowQuant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The box `θ`-integral of a state supported in the box.**  For `ψ` smooth with
`tsupport ψ ⊆ boxL ℓ` the sharp box indicator `θ_Λ = 1_{boxL ℓ}` may be replaced
by the domain of integration: the complex pairing `∫ θ_Λ · ψ` is the set integral
`∫_{boxL ℓ} ψ` (a real number).  (`θ_Λ` lives in `ℂ`, so the constant
`hatChi (ℓ • k)` and the value `ψ z` are both coerced to `ℂ`.) -/
lemma thetaFun_mul_psi_integral {ℓ : ℝ} {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hψsupp : tsupport ψ ⊆ Work.BoseK15.corpusBox.boxL ℓ) (k : EuclideanSpace ℝ (Fin 3)) :
    ∫ z, ((Work.BoseK15.corpusBox.hatChi (ℓ • k) : ℝ) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun ℓ z * (ψ z : ℂ)
      = ((Work.BoseK15.corpusBox.hatChi (ℓ • k)
          * ∫ z in Work.BoseK15.corpusBox.boxL ℓ, ψ z : ℝ) : ℂ) := by
  -- `θ_Λ` is exactly the indicator of the box, so the integrand is the constant
  -- `χ̂(ℓk)` against the indicator of `ψ` on the box.
  set c : ℝ := Work.BoseK15.corpusBox.hatChi (ℓ • k) with hc
  have hsmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet _ ℓ
  have hpt : ∀ z, ((c : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z * (ψ z : ℂ)
      = (c : ℂ) * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun z => (ψ z : ℂ)) z := by
    intro z
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [if_pos hz, Set.indicator_of_mem hz]; ring
    · rw [if_neg hz, Set.indicator_of_notMem hz]; ring
  calc ∫ z, ((c : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ z * (ψ z : ℂ)
      = ∫ z, (c : ℂ) * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun z => (ψ z : ℂ)) z :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (c : ℂ) * ∫ z, (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun z => (ψ z : ℂ)) z :=
        MeasureTheory.integral_const_mul (c : ℂ) _
    _ = (c : ℂ) * ∫ z in Work.BoseK15.corpusBox.boxL ℓ, (ψ z : ℂ) := by
        rw [MeasureTheory.integral_indicator hsmeas]
    _ = (c : ℂ) * ((∫ z in Work.BoseK15.corpusBox.boxL ℓ, ψ z : ℝ) : ℂ) := by
        congr 1
        exact integral_ofReal
    _ = ((c * ∫ z in Work.BoseK15.corpusBox.boxL ℓ, ψ z : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul]

end Work.BoseBoxFock
