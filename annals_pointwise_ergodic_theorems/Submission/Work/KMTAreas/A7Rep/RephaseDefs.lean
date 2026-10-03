/-
# Vocabulary for the residue-maximal rephasing bound

The band of the cut, and the real-frequency-support predicate used to state the
quantitative Shannon/decimation comparison for the window envelopes.
-/
import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc
import Submission.Work.Analysis.IonescuWainger.EtaCut
import Submission.Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing
import Submission.Work.Analysis.IonescuWainger.iwQl_le
import Submission.Work.Analysis.IonescuWainger.iw_height_card_le
import Submission.Work.Analysis.IonescuWainger.memLp_periodize
import Submission.Work.Analysis.IonescuWainger.multiplier_add
import Submission.Work.Analysis.IonescuWainger.multiplier_comp
import Submission.Work.Analysis.IonescuWainger.norm_iwOpSet_le
import Submission.Work.Analysis.IonescuWainger.one_div_le_norm_of_ne
import Submission.Work.Analysis.IonescuWainger.supportedInArc_periodize

namespace Work.KMTAreas.A7Rep

open MeasureTheory
open scoped BigOperators

/-- The **band of the cut**: the union of the windows `α + [-2δ,2δ]` over the exact-height
arithmetic frequencies `(ℚ/ℤ)_{l₁}`. -/
def cutBand (ρ : ℝ) (l₁ : ℕ) (δ : ℝ) : Set Work.Analysis.IonescuWainger.Circle :=
  ⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
    Work.BourgainPlan.IonescuWainger.arcSet α (2 * δ)

/-- A function `ψ : ℝ → ℂ` has **real frequency support in `S`** if it is the inverse Fourier
transform of an integrable function supported in `S`.  This is the band condition needed by the
lattice/integral Shannon comparison. -/
def HasRealFreqSupport (ψ : ℝ → ℂ) (S : Set ℝ) : Prop :=
  ∃ g : ℝ → ℂ, MeasureTheory.Integrable g ∧ (∀ ξ : ℝ, ξ ∉ S → g ξ = 0) ∧
    ∀ t : ℝ, ψ t = FourierTransformInv.fourierInv g t

end Work.KMTAreas.A7Rep
