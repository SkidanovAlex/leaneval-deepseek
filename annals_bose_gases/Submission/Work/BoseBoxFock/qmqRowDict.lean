import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.qmqDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.qmqRowDict` — the summation of the two dictionary identities

The two per-pair dictionary identities of the `Q₂` row (`dict13_L1` for block I and `dictII_L1` for
block II) sum over `p ∈ pairSet n` and over the three `rowShape`'s to give the *row-level* statement

    (rowPairSubC (ℓ³)⁻¹ Θ A (qmqKernel ℓ k₁) (qmqKernel ℓ k₂)).re = q1WordK ℓ k₁ Ψ + q4WordK ℓ k₂ Ψ

at `Θ = boxRestrictC ℓ Ψ` and `A = c·θ_Λ`.  This module performs that summation: it is pure
`Finset`/`Complex.re` bookkeeping — no analysis — and it is stated with the two per-pair identities
as hypotheses, so that it is independent of the modules proving them.

The `re`-bookkeeping facts used are `re_finset_sum` (`(Σ z).re = Σ z.re`), `smul_re'`
(`(a • z).re = a * z.re`) and `add_re'` (`(z₁+z₂).re = z₁.re + z₂.re`).

Everything here is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option linter.unusedVariables false

/-- The real part of a finite sum of complex numbers. -/
theorem re_finset_sum {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    (∑ i ∈ s, z i).re = ∑ i ∈ s, (z i).re := by
  simpa [Complex.reCLM_apply] using map_sum Complex.reCLM z s

/-- The real part of a real multiple. -/
theorem smul_re' (a : ℝ) (z : ℂ) : ((a : ℝ) • z).re = a * z.re := by simp

/-- The real part of a sum. -/
theorem add_re' (z₁ z₂ : ℂ) : (z₁ + z₂).re = z₁.re + z₂.re := Complex.add_re _ _

/-- **The row-level summation of the two dictionary identities.**

Given the block-I identity `h13` and the block-II identity `hII` at the kernels `qmqKernel ℓ k₁`,
`qmqKernel ℓ k₂`, the whole block-`I/II` part of the row (at `Θ = boxRestrictC ℓ Ψ`,
`A = c·θ_Λ`, normalisation `(ℓ³)⁻¹` and the `½` of the Bogoliubov block) equals the two words
`q1WordK ℓ k₁ Ψ + q4WordK ℓ k₂ Ψ`. -/
theorem rowPairSubC_re_qmqKernel {n : ℕ} {ℓ : ℝ} {Ψ : Submission.BoseGases.X n → ℝ}
    {c : ℂ} {k₁ k₂ : E3 → E3 → ℝ}
    (h13 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ((ℓ ^ 3)⁻¹ : ℝ) *
          (rowShape13 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
            (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
            (qmqKernel ℓ k₁) p).re
        = ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Ψ) x
              * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
              * k₁ (x p.1) (x p.2))
    (hII : ∀ p ∈ Submission.BoseGases.pairSet n,
      (1 / 2) * ((ℓ ^ 3)⁻¹ : ℝ) *
          ((rowShape21 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (qmqKernel ℓ k₂) p).re
            + (rowShape23 (boxRestrictC ℓ Ψ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
                (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
                (qmqKernel ℓ k₂) p).re)
        = ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Ψ) x
              * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
              * k₂ (x p.1) (x p.2)) :
    (rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Ψ)
        (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
        (qmqKernel ℓ k₁) (qmqKernel ℓ k₂)).re
      = q1WordK ℓ k₁ Ψ + q4WordK ℓ k₂ Ψ := by
  set Θ : Xn n → ℂ := boxRestrictC ℓ Ψ with hΘ
  set A : E3 → ℂ := fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y with hA
  set S : Finset (Fin n × Fin n) := Submission.BoseGases.pairSet n with hS
  have h13sum : (rowSum13 Θ A A (qmqKernel ℓ k₁)).re
      = ∑ p ∈ S, (rowShape13 Θ A A (qmqKernel ℓ k₁) p).re := by
    rw [rowSum13]
    exact re_finset_sum _ _
  have h21sum : (rowSum21 Θ A (qmqKernel ℓ k₂)).re
      = ∑ p ∈ S, (rowShape21 Θ A (qmqKernel ℓ k₂) p).re := by
    rw [rowSum21]
    exact re_finset_sum _ _
  have h23sum : (rowSum23 Θ A A (qmqKernel ℓ k₂)).re
      = ∑ p ∈ S, (rowShape23 Θ A A (qmqKernel ℓ k₂) p).re := by
    rw [rowSum23]
    exact re_finset_sum _ _
  -- the `re` of the row is the two real blocks
  have hsplit : (rowPairSubC ((ℓ ^ 3)⁻¹) Θ A (qmqKernel ℓ k₁) (qmqKernel ℓ k₂)).re
      = ((ℓ ^ 3)⁻¹ : ℝ) * (rowSum13 Θ A A (qmqKernel ℓ k₁)).re
        + ((1 / 2) * ((ℓ ^ 3)⁻¹ : ℝ))
          * ((rowSum21 Θ A (qmqKernel ℓ k₂)).re
            + (rowSum23 Θ A A (qmqKernel ℓ k₂)).re) := by
    simp only [rowPairSubC, Complex.add_re, smul_re']
  -- block I
  have hA1 : ((ℓ ^ 3)⁻¹ : ℝ) * (rowSum13 Θ A A (qmqKernel ℓ k₁)).re
      = ∑ p ∈ S,
          ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Ψ) x
              * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
              * k₁ (x p.1) (x p.2) := by
    rw [h13sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => h13 p (by simpa [hS] using hp))
  -- block II
  have hA2 : ((1 / 2) * ((ℓ ^ 3)⁻¹ : ℝ))
        * ((rowSum21 Θ A (qmqKernel ℓ k₂)).re
          + (rowSum23 Θ A A (qmqKernel ℓ k₂)).re)
      = ∑ p ∈ S,
          ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Ψ) x
              * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
              * k₂ (x p.1) (x p.2) := by
    rw [h21sum, h23sum]
    rw [show ((1 / 2) * ((ℓ ^ 3)⁻¹ : ℝ))
          * ((∑ p ∈ S, (rowShape21 Θ A (qmqKernel ℓ k₂) p).re)
            + (∑ p ∈ S, (rowShape23 Θ A A (qmqKernel ℓ k₂) p).re))
        = ∑ p ∈ S, ((1 / 2) * ((ℓ ^ 3)⁻¹ : ℝ))
            * ((rowShape21 Θ A (qmqKernel ℓ k₂) p).re
              + (rowShape23 Θ A A (qmqKernel ℓ k₂) p).re) from by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun p _ => by ring)]
    exact Finset.sum_congr rfl (fun p hp => hII p (by simpa [hS] using hp))
  have hq1 : q1WordK ℓ k₁ Ψ
      = ∑ p ∈ S,
          ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Ψ) x
              * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
              * k₁ (x p.1) (x p.2) := by
    rw [hS]; rfl
  have hq4 : q4WordK ℓ k₂ Ψ
      = ∑ p ∈ S,
          ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Ψ) x
              * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Ψ) x
              * k₂ (x p.1) (x p.2) := by
    rw [hS]; rfl
  rw [hsplit, hA1, hA2, hq1, hq4]

end Work.BoseBoxFock
