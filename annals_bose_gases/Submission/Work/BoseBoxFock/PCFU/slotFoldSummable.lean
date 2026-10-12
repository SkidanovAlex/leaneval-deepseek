import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.summable_kinFT_kappaL
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.slotFoldSummable`

The summability of the lattice sum appearing in the `w − y`-fold of the `χχ` periodised kernel
(the companion of `Work.BoseBoxFock.PCFU.slotFold`):

    Σ_n Ŵ(κ_n) Ψ̂(−κ_n)      with `κ_n = kappaL ℓ n`,

for an `L¹` weight `W` and a smooth compactly supported `Ψ`.

## Mathematics

Only two ingredients are needed:

* `‖kinFT u p‖ ≤ ∫‖u‖` for **every** `u` (the modulus of the exponential is `1`), so
  `‖Ŵ(κ_n)‖ ≤ ∫‖W‖` is *bounded* — no decay of `Ŵ` is available (nor needed), since `W` is only
  `L¹`;
* the *decay* of the second factor: for smooth compactly supported `Ψ`,
  `Summable (fun n => ‖kinFT Ψ (κ_n)‖)` — this is the corpus lemma
  `Work.BoseBoxFock.L1Tails.summable_kinFT_kappaL` (`‖p‖⁴‖kinFT Ψ p‖ ≤ ∫‖D⁴Ψ‖`), which we
  transport from `κ_n` to `−κ_n` by the reindexing bijection `n ↦ −n` of the lattice
  (`kappaL ℓ (−n) = −kappaL ℓ n`).

The product is then dominated by the summable sequence `(∫‖W‖)·‖kinFT Ψ (−κ_n)‖`, and
`Summable.of_norm` concludes for the `ℂ`-valued summand.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real

namespace Work.BoseBoxFock.PCFU

set_option linter.unusedVariables false

/-- The trivial bound on the `p`-convention Fourier transform: since
`‖e^{−i⟪p,y⟫}‖ = 1`, one has `‖kinFT u p‖ ≤ ∫‖u‖`.  (No hypothesis on `u`.) -/
private lemma norm_kinFT_le_integral_norm (u : EuclideanSpace ℝ (Fin 3) → ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖Submission.BoseGases.kinFT u p‖ ≤ ∫ x, ‖u x‖ := by
  calc ‖Submission.BoseGases.kinFT u p‖
      = ‖∫ y, Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * u y‖ := rfl
    _ ≤ ∫ y, ‖Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * u y‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ y, ‖u y‖ := by
        refine MeasureTheory.integral_congr_ae ?_
        filter_upwards with y
        rw [norm_mul, Complex.norm_exp]
        have hre : (-(Complex.I * (inner ℝ p y : ℂ))).re = 0 := by
          simp [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.I_im]
        rw [hre, Real.exp_zero, one_mul]

/-- **`ℓ¹`-summability of the lattice fold summand.**  For an `L¹` weight `W` and a smooth
compactly supported `Ψ`, the sequence `n ↦ Ŵ(κ_n)·Ψ̂(−κ_n)` is summable: the first factor is
bounded by `∫‖W‖` and the second decays like `‖κ_n‖^{-4}`
(`Work.BoseBoxFock.L1Tails.summable_kinFT_kappaL`). -/
theorem slotFoldSummable {ℓ : ℝ} (hℓ : 0 < ℓ)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    {Ψ : EuclideanSpace ℝ (Fin 3) → ℂ} (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨs : HasCompactSupport Ψ) :
    Summable (fun n : Fin 3 → ℤ =>
      Submission.BoseGases.kinFT (fun v => ((W v : ℝ) : ℂ)) (Work.BoseBoxFock.kappaL ℓ n)
        * Submission.BoseGases.kinFT Ψ (-(Work.BoseBoxFock.kappaL ℓ n))) := by
  -- the decaying factor, at the lattice momenta
  have hbase : Summable (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT Ψ (Work.BoseBoxFock.kappaL ℓ n)‖) :=
    Work.BoseBoxFock.L1Tails.summable_kinFT_kappaL hℓ hΨ hΨs
  -- transport it to the negated momenta `−κ_n = κ_{−n}`
  have hfe : (fun n : Fin 3 → ℤ =>
        ‖Submission.BoseGases.kinFT Ψ (-(Work.BoseBoxFock.kappaL ℓ n))‖)
      = (fun m : Fin 3 → ℤ =>
        ‖Submission.BoseGases.kinFT Ψ (Work.BoseBoxFock.kappaL ℓ m)‖)
        ∘ (fun n : Fin 3 → ℤ => -n) := by
    funext n
    simp only [Function.comp_apply]
    rw [Work.BoseBoxFock.L1Tails.kappaL_neg]
  have hneg : Summable (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT Ψ (-(Work.BoseBoxFock.kappaL ℓ n))‖) := by
    rw [hfe]
    exact hbase.comp_injective neg_injective
  -- the bounded factor, with the coercion bookkeeping
  have hWval : (∫ x : EuclideanSpace ℝ (Fin 3), ‖((W x : ℝ) : ℂ)‖) = ∫ x, ‖W x‖ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    simp
  have hbound : ∀ n : Fin 3 → ℤ,
      ‖Submission.BoseGases.kinFT (fun v => ((W v : ℝ) : ℂ)) (Work.BoseBoxFock.kappaL ℓ n)
        * Submission.BoseGases.kinFT Ψ (-(Work.BoseBoxFock.kappaL ℓ n))‖
      ≤ (∫ x : EuclideanSpace ℝ (Fin 3), ‖W x‖) *
        ‖Submission.BoseGases.kinFT Ψ (-(Work.BoseBoxFock.kappaL ℓ n))‖ := by
    intro n
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ‖Submission.BoseGases.kinFT (fun v => ((W v : ℝ) : ℂ))
            (Work.BoseBoxFock.kappaL ℓ n)‖
        ≤ ∫ x, ‖((W x : ℝ) : ℂ)‖ := norm_kinFT_le_integral_norm _ _
      _ = ∫ x, ‖W x‖ := hWval
  -- assemble
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound ?_
  exact hneg.mul_left _

end Work.BoseBoxFock.PCFU
