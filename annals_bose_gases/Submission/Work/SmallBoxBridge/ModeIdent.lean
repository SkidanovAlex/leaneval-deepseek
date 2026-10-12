import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxBridge.ModeIdent.pSlotAmp_eq_rawSlotAmp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The diagonal mode form IS the `𝒯₀` form

`pDiagForm` and `T0Form` are defined with the *same* shape (sum over slots, `p`-integral outer,
`(s³)⁻¹∫_{abox}` inner); the only difference is the slot amplitude: `pSlotAmp` (the `Q_B`-projected
mode `qMode s p`) versus `rawSlotAmp` (the plain windowed exponential of the `Q_i`-projected
fibre `aQ s i Ψ`).  `SmallBoxBridge.ModeIdent.pSlotAmp_eq_rawSlotAmp` identifies them pointwise,
so the two forms are equal with no sum/integral interchange.
-/

noncomputable section

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **`pDiagForm = T0Form`**: the diagonal (one-body) mode form of the corpus mode
`qMode s p` equals the windowed-exponential Fourier form of `𝒯₀ = Σ_i Q_iχ_iF(√−Δ_i)χ_iQ_i`. -/
theorem pDiagForm_eq_T0Form {N : ℕ} {s : ℝ} (hs : 0 < s) (F : ℝ → ℝ) {Ψ : X N → ℝ}
    (hΨ : Continuous Ψ) : pDiagForm s F Ψ = T0Form s F Ψ := by
  unfold pDiagForm T0Form
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
  have key : ∀ x : X N, pSlotAmp s p Ψ i x = rawSlotAmp s p (aQ s i Ψ) i x :=
    fun x => Work.SmallBoxBridge.ModeIdent.pSlotAmp_eq_rawSlotAmp (N := N) (s := s) hs p hΨ i x
  simp only [key]
