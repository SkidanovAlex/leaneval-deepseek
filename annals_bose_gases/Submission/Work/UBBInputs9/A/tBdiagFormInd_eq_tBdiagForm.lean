import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs9.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm`

The round-8 FS-faithful `p`-diagonal kinetic form `Work.UBBInputs8.tBdiagFormInd` is built from
FS's own mean-free projection `Q_B = 1_B − P_B` (`Work.UBBInputs8.boxQInd`), while the corpus's
`Work.SmallBoxTBWord.tBdiagForm` uses the indicator-free projection `boxQ = id − P_B`.  The two
projections differ by exactly the box indicator,

    `boxQInd volA A i Φ = 1_A(x_i) · boxQ volA A i Φ`,

and the windowed-exponential amplitude `tBamp χ p · i x` only sees the values of its argument on
`{z | x_{i←z}}` multiplied by `χ z`.  Hence, **as soon as `χ` is supported in `A`** (the actual
situation in the sliding application: `tsupport (chiB ℓ d u) ⊆ dlBox ℓ d u`), the indicator
factors out and the two words coincide:

    `tBdiagFormInd a A volA χ F Ψ = tBdiagForm a A volA χ F Ψ`.

This is what makes the FS-faithful repair of the kinetic clause usable in the corpus's own
word calculus.  No measurability, no integrability and no support condition on `F`/`Ψ` is needed:
the two integrands are equal *pointwise*.
-/

namespace Work.UBBInputs9.A

open MeasureTheory
open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The FS-faithful mean-free projection carries the box indicator:
`boxQInd volA A i Φ = 1_A(x_i) · boxQ volA A i Φ`. -/
lemma boxQInd_eq_indicator_mul_boxQ {volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {N : ℕ}
    (i : Fin N) (Φ : X N → ℝ) :
    Work.UBBInputs8.boxQInd volA A i Φ
      = fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i)
          * Work.SmallBoxTBWord.boxQ volA A i Φ x := by
  funext x
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Work.SmallBoxTBWord.boxQ,
    Work.SmallBoxTBWord.boxP]
  ring

/-- A slot indicator in front of the amplitude's argument is invisible to the amplitude, provided
the window vanishes off the indicator set.  (Pointwise in the `p`-variable and in `x`.) -/
lemma tBamp_indicator_mul {A : Set (EuclideanSpace ℝ (Fin 3))}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ A → χ z = 0)
    {N : ℕ} (p : EuclideanSpace ℝ (Fin 3)) (g : X N → ℝ) (i : Fin N) (x : X N) :
    Work.SmallBoxTBWord.tBamp χ p (fun y => A.indicator (fun _ => (1 : ℝ)) (y i) * g y) i x
      = Work.SmallBoxTBWord.tBamp χ p g i x := by
  unfold Work.SmallBoxTBWord.tBamp
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [Function.update_self]
  have hca : (χ z : ℂ) * ((A.indicator (fun _ => (1 : ℝ)) z : ℝ) : ℂ) = (χ z : ℂ) := by
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz]; simp
    · rw [Set.indicator_of_notMem hz]; simp [hχ z hz]
  have hcast : (χ z : ℂ) * ((A.indicator (fun _ => (1 : ℝ)) z * g (Function.update x i z) : ℝ) : ℂ)
      = (χ z : ℂ) * (g (Function.update x i z) : ℂ) := by
    rw [Complex.ofReal_mul, ← mul_assoc, hca]
  calc (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
        * ((A.indicator (fun _ => (1 : ℝ)) z * g (Function.update x i z) : ℝ) : ℂ)
      = Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * ((χ z : ℂ)
            * ((A.indicator (fun _ => (1 : ℝ)) z * g (Function.update x i z) : ℝ) : ℂ)) := by
        ring
    _ = Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * ((χ z : ℂ) * (g (Function.update x i z) : ℂ)) := by rw [hcast]
    _ = (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * (g (Function.update x i z) : ℂ) := by ring

/-- The two projections give the same amplitude when the window is supported in the box. -/
lemma tBamp_boxQInd {volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ A → χ z = 0)
    {N : ℕ} (Ψ : X N → ℝ) (i : Fin N) (p : EuclideanSpace ℝ (Fin 3)) (x : X N) :
    Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x
      = Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x := by
  rw [boxQInd_eq_indicator_mul_boxQ]
  exact tBamp_indicator_mul hχ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x

theorem tBdiagFormInd_eq_tBdiagForm {a : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {volA : ℝ}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (F : ℝ → ℝ) {N : ℕ} (Ψ : Submission.BoseGases.X N → ℝ)
    (hχ : ∀ z : EuclideanSpace ℝ (Fin 3), z ∉ A → χ z = 0) :
    Work.UBBInputs8.tBdiagFormInd a A volA χ F Ψ = Work.SmallBoxTBWord.tBdiagForm a A volA χ F Ψ := by
  unfold Work.UBBInputs8.tBdiagFormInd Work.SmallBoxTBWord.tBdiagForm
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  congr 1
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [tBamp_boxQInd hχ]

end Work.UBBInputs9.A
