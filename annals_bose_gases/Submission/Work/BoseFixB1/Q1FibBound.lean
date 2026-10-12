import ChallengeDeps
import Submission.Work.BoseFixB1.KernelFacts
import Submission.Work.BoseFixB1.Q1FormDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false

/-- The two localised fibres are a.e. strongly measurable and uniformly bounded on `acube ℓ`. -/
theorem q1Fib_aem_bound {v : E3 → ℝ} {R0 : ℝ}
    (hv_supp : _root_.tsupport v ⊆ Metric.ball (0 : E3) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u : E3) :
    (MeasureTheory.AEStronglyMeasurable (q1Fib2 h M ℓ d u)
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ))
      ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, |q1Fib2 h M ℓ d u z| ≤ C)
    ∧ (MeasureTheory.AEStronglyMeasurable (q1Fib1 h M ℓ d u)
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ))
      ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z : E3, |q1Fib1 h M ℓ d u z| ≤ C) := by
  constructor
  · constructor
    · have hg2 : AEMeasurable (Submission.BoseGases.g2 v h) (volume : Measure E3) :=
        (Submission.BoseGases.g2_integrable hR0 hv hvrad hv_supp h).aemeasurable
      have hthis := aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u hg2
      unfold q1Fib2 Submission.BoseGases.w1Fibre
      exact hthis
    · refine ⟨|wFibC M (16 * π * _root_.BoseGases.a v)|, abs_nonneg _, ?_⟩
      intro z
      unfold q1Fib2 Submission.BoseGases.w1Fibre
      exact le_trans (wSmall2_fibre_abs_le_gen (v := v) (R := R0)
        hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z) (le_abs_self _)
  · constructor
    · have hg0 : AEMeasurable (Submission.BoseGases.g0 v h) (volume : Measure E3) :=
        (Submission.BoseGases.g0_integrable hR0 hv_supp h).aemeasurable
      have hthis := aestronglyMeasurable_wSmallPairFibre (ℓ := ℓ) (d := d) M u hg0
      unfold q1Fib1 Submission.BoseGases.wSmall1Pair Submission.BoseGases.w1Fibre
      exact hthis
    · refine ⟨|wFibC M (8 * π * _root_.BoseGases.a v)|, abs_nonneg _, ?_⟩
      intro z
      unfold q1Fib1 Submission.BoseGases.wSmall1Pair Submission.BoseGases.w1Fibre
      exact le_trans (wSmall1_fibre_abs_le_gen (v := v) (R := R0)
        hv_supp hR0 hv hvrad h hM hℓ hd hR hRχ u z) (le_abs_self _)

end Work.BoseFixB1
