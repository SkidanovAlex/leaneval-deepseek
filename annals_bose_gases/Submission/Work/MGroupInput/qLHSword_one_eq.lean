import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.MGroupInput.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.MGroupInput

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Integrals over the one-particle centred box of a function of the single
coordinate `x 0` equal integrals over the centred cube.

(`abox 1 s` is the preimage of `acube s` under the measure-preserving
equivalence `oneEval : X 1 ≃ᵐ ℝ³` given by evaluation at the unique index of
`Fin 1`.) -/
lemma integral_abox_one (s : ℝ) (g : ℝ³ → ℝ) :
    (∫ x in Submission.BoseGases.abox 1 s, g (x 0))
      = ∫ z in Submission.BoseGases.acube s, g z := by
  have habox : Submission.BoseGases.abox 1 s
      = Submission.BoseGases.oneEval ⁻¹' (Submission.BoseGases.acube s) := by
    ext x
    simp [Submission.BoseGases.abox, Submission.BoseGases.acube, Submission.BoseGases.oneEval]
  rw [habox]
  have hmp := Submission.BoseGases.oneEval_measurePreserving.restrict_preimage_emb
      Submission.BoseGases.oneEval.measurableEmbedding (Submission.BoseGases.acube s)
  have h := hmp.integral_comp Submission.BoseGases.oneEval.measurableEmbedding
      (fun z : ℝ³ => g z)
  simpa [Submission.BoseGases.oneEval_apply] using h

/-- **The one-particle `qLHSword`.**  At `N = 1` the potential splitting
`qLHSword` loses its two-body term (`pairSet 1 = ∅`) and keeps only the
chemical-potential term; on the all-condensate state `Φ ≡ 1` the surviving
one-body sum is `w1Fibre s w1 (x 0)`, and the integral over the one-particle
box `abox 1 s` collapses (via the measure-preserving equivalence
`X 1 ≃ᵐ ℝ³`) to the integral of `w1Fibre s w1` over the centred cube `acube s`:

    `qLHSword (N := 1) s μ w w1 1 = - μ * ∫_Λ w1Fibre s w1`. -/
theorem qLHSword_one_eq {s μ : ℝ} (hs : 0 < s)
    (w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) :
    Submission.BoseGases.qLHSword (N := 1) s μ w w1
        (fun _ : Submission.BoseGases.X 1 => (1 : ℝ))
      = - μ * (∫ z in Submission.BoseGases.acube s, Submission.BoseGases.w1Fibre s w1 z) := by
  have hpair : Submission.BoseGases.pairSet 1 = ∅ := by decide
  have hfun : ∀ x : Submission.BoseGases.X 1,
      ((fun _ : Submission.BoseGases.X 1 => (1 : ℝ)) x) ^ 2 *
        (- μ * (∑ i : Fin 1, Submission.BoseGases.w1Fibre s w1 (x i))
          + (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet 1, w (x p.1) (x p.2)))
      = - μ * Submission.BoseGases.w1Fibre s w1 (x 0) := by
    intro x
    rw [Fin.sum_univ_one]
    have hp : (∑ p ∈ Submission.BoseGases.pairSet 1, w (x p.1) (x p.2)) = 0 := by
      rw [hpair]; simp
    rw [hp]
    ring
  rw [Submission.BoseGases.qLHSword]
  simp_rw [hfun]
  rw [integral_const_mul, integral_abox_one]

end Work.MGroupInput
