import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.NeuFrac.bddBelow_trialSet_of_integrableOn
import Submission.Work.BoseKinLoc.NeuFrac.lamBox_subset_ball
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_nonneg_l2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBox.q3kinNeuFracLeGapBare`

The upper half of the two-sided bound for the box Neumann-resolvent fraction `neuFrac`
(FS `eq:DefT`'s first term) applied to the mean-free part `Q_uψ`:

`neuFrac ℓ a² u (Q_uψ) ≤ gapBare ℓ u ψ = ∫_{Λ(u)} (Q_uψ)²`,   `Λ(u) = lamBox ℓ u`,

for a **merely continuous** one-body state `ψ` (no smoothness, no compact support).

## The mathematics

`neuFrac ℓ a² u ϕ` is the Dirichlet-principle `sInf`

`inf_g [ ∫_Λ ϕ² − 2a²∫_Λ ϕg + a²(Σ_k∫_Λ (∂_k g)² + a²∫_Λ g²) ]`

over globally smooth compactly supported trials `g`.  The bound is the spectral inequality
`A(A+a²)⁻¹ ≤ 1` for the box Neumann Laplacian `A = −Δ^N`, read through the Dirichlet
principle: the admissible trial `g ≡ 0` has value exactly `∫_Λ ϕ² = gapBare ℓ u ψ`, so the
infimum is at most this (`csInf_le`).

`csInf_le` requires the trial set to be **bounded below**, which
`Work.BoseKinLoc.NeuFrac.bddBelow_trialSet_of_integrableOn` supplies from
square-integrability of `ϕ² = (Q_uψ)²` **on the box only** — global integrability of `(Q_uψ)²`
is *false*, since `Q_uψ` tends to the nonzero constant `−m_u(ψ)` at infinity.

Box square-integrability for a continuous `ψ`: `Q_uψ = ψ − m_u(ψ)` is continuous
(`hψ.sub continuous_const`) and the moving box `Λ(u) = ℓu + acube ℓ` lies in the compact
closed ball `closedBall (ℓu) (2(|ℓ|+1))` (`NeuFrac.lamBox_subset_closedBall`), so
`ContinuousOn.integrableOn_compact` applies.  This is exactly the hypothesis regime of the
parent `Work.BoseKinLoc.Kinetic.neuFrac_Qfree_bounds`, whose hypotheses
(`ContDiff ℝ ⊤ ψ`, `HasCompactSupport ψ`) are never used beyond `hψ.continuous`
(compare `Work.BoseKinLoc.Word.fsT_nonneg_of_continuous`).

## Contents

* `integrableOn_Qfree_sq_of_continuous` — the box square-integrability used;
* `q3kinNeuFracLeGapBare` — the requested bound.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseBox

set_option linter.unusedVariables false

/-- **Box square-integrability of the mean-free part of a continuous state.**

`z ↦ (Q_uψ z)² = (ψ z − m_u(ψ))²` is continuous and the moving box `Λ(u)` is contained in
the compact ball `closedBall (ℓu) (2(|ℓ|+1))`, whence `(Q_uψ)² ∈ L¹(Λ(u))`.  No smoothness
or compact support of `ψ` is needed. -/
lemma integrableOn_Qfree_sq_of_continuous {ℓ : ℝ} (hℓ : 0 < ℓ)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) :
    MeasureTheory.IntegrableOn
      (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2)
      (Work.BoseKinLoc.lamBox ℓ u) := by
  have hcont : Continuous (Work.BoseKinLoc.Qfree ℓ u ψ) := hψ.sub continuous_const
  exact (ContinuousOn.integrableOn_compact (isCompact_closedBall (ℓ • u) (2 * (|ℓ| + 1)))
      (hcont.pow 2).continuousOn).mono_set
        (Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall ℓ u)

/-- **The Neumann fraction of the mean-free part is dominated by the bare mean-free box
mass.**  `neuFrac ℓ a² u (Q_uψ) ≤ gapBare ℓ u ψ`: the trial `g ≡ 0` in the Dirichlet
principle defining `neuFrac` has value `∫_{Λ(u)}(Q_uψ)² = gapBare ℓ u ψ`. -/
theorem q3kinNeuFracLeGapBare {ℓ a2 : ℝ} (hℓ : 0 < ℓ) (ha2 : 0 ≤ a2)
    (u : EuclideanSpace ℝ (Fin 3)) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : Continuous ψ) :
    Work.BoseKinLoc.neuFrac ℓ a2 u (Work.BoseKinLoc.Qfree ℓ u ψ)
      ≤ Work.BoseKinLoc.gapBare ℓ u ψ := by
  -- `(Q_uψ)²` is integrable on the moving box
  have hI : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ u)) :=
    integrableOn_Qfree_sq_of_continuous hℓ u hψ
  -- the bare box mass is by definition the box integral of `(Q_uψ)²`
  have hgap : Work.BoseKinLoc.gapBare ℓ u ψ
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (Work.BoseKinLoc.Qfree ℓ u ψ z) ^ 2 := rfl
  rw [hgap]
  unfold Work.BoseKinLoc.neuFrac
  -- `neuFrac` is the `sInf` of the trial values; the trial set is bounded below by `hI`
  refine csInf_le (Work.BoseKinLoc.NeuFrac.bddBelow_trialSet_of_integrableOn ha2 u hI) ?_
  simp only [Set.mem_ofPred_eq]
  -- the trial `g ≡ 0` is admissible and its value is the box integral of `(Q_uψ)²`
  exact ⟨fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ), contDiff_const,
    HasCompactSupport.zero, by simp⟩

end Work.BoseBox
