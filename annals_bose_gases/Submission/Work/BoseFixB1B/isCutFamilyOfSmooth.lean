import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseFixB1B.sectorCountBoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.isCutFamilyOfSmooth`

From the *pointwise* existence of smooth cutoffs of the sliding box (one for each `δ > 0`, with the
derivative bound `C/δ` for a single constant `C`), produce a *family*
`γ : ℝ → E3 → ℝ` satisfying `IsCutFamily L d u C γ` — the form in which the geometric input is
consumed by the sharp extension (`Work.BoseFixB1B.sharpCountCoreAt_of_tendsto`).

The only content is that `IsCutFamily` quantifies over `δ > 0` only, so `γ` may be chosen
arbitrarily on `δ ≤ 0`; the family is built by `Classical.choose` from the pointwise statement
(`Work.BoseFixB1B.exists_smoothCutoff` supplies that statement).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The pointwise smooth-cutoff statement** — exactly the conclusion of
`Work.BoseFixB1B.exists_smoothCutoff`. -/
def SmoothCutoffPointwise (L d : ℝ) (u : E3) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∃ γ : E3 → ℝ,
    ContDiff ℝ (⊤ : ENat) γ ∧ tsupport γ ⊆ dlBox L d u ∧
    (∀ x, 0 ≤ γ x ∧ γ x ≤ 1) ∧
    (∀ x, boxMargin L d u x ≥ δ → γ x = 1) ∧
    (∀ x, ‖fderiv ℝ γ x‖ ≤ C / δ)

/-- **The cutoff family from the pointwise cutoffs.** -/
theorem exists_isCutFamily_of_smoothCutoff {L d : ℝ} {u : E3}
    (h : SmoothCutoffPointwise L d u) :
    ∃ K : ℝ, ∃ γ : ℝ → E3 → ℝ, IsCutFamily L d u K γ := by
  classical
  obtain ⟨C, hC0, hC⟩ := h
  set γ : ℝ → E3 → ℝ :=
    fun δ => if hδ : 0 < δ then Classical.choose (hC δ hδ) else 0 with hγdef
  refine ⟨C, γ, hC0, fun δ hδ => ?_⟩
  have hspec := Classical.choose_spec (hC δ hδ)
  have hval : γ δ = Classical.choose (hC δ hδ) := by
    rw [hγdef]
    simp only [dif_pos hδ]
  rw [hval]
  exact hspec

end Work.BoseFixB1B
