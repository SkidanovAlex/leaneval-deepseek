import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.NeuFrac.lamBox_subset_ball
import Submission.Work.BoseKinLoc.NeuFrac.neuFrac_nonneg_l2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.FRK

open MeasureTheory

/-- **The Neumann word `neuWord ℓ d ε_T 0 ψ` is nonnegative** for `ℓ > 0`, `d > 0`, `ε_T ≥ 0`
and a smooth state `ψ`.

`neuWord ℓ d ε_T u ψ = ½ε_T(dℓ)⁻²·neuFrac ℓ ((dℓ)⁻²) u (Q_uψ)` is a nonnegative prefactor times
the box Neumann fraction of the mean-free state `Q_uψ`.  The prefactor is nonnegative, and the
fraction is nonnegative by completing the square under the box integral
(`Work.BoseKinLoc.NeuFrac.neuFrac_nonneg_l2`): for every globally smooth compactly supported
trial `g`,

`∫_Λ φ² − 2a²∫_Λ φg + a²(Σ_k∫_Λ(∂_kg)² + a²∫_Λ g²) = ∫_Λ(φ − a²g)² + a²Σ_k∫_Λ(∂_kg)² ≥ 0`,

so every member of the defining trial set is `≥ 0`, and the set is nonempty (`g = 0`).

The only input is that `(Q_uψ)²` be integrable on the box `Λ(u)` — smoothness of `ψ` gives it,
since `Q_uψ = ψ − (constant)` is continuous and `Λ(u)` lies in a compact ball
(`Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall`). -/
theorem neuWord_nonneg_general {ℓ d eT : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (heT : 0 ≤ eT)
    (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    0 ≤ Work.BoseKinLoc.neuWord ℓ d eT 0 ψ := by
  have hdℓ : 0 < d * ℓ := mul_pos hd hℓ
  have ha2 : 0 ≤ (d * ℓ) ^ (-2 : ℤ) := zpow_nonneg hdℓ.le _
  -- `Q_uψ = ψ − (box mean)` is continuous
  have hcont : Continuous (Work.BoseKinLoc.Qfree ℓ 0 ψ) :=
    hψ.continuous.sub continuous_const
  -- hence its square is integrable on the (bounded) box
  have hI : MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => (Work.BoseKinLoc.Qfree ℓ 0 ψ z) ^ 2)
      (MeasureTheory.volume.restrict (Work.BoseKinLoc.lamBox ℓ 0)) :=
    (ContinuousOn.integrableOn_compact (isCompact_closedBall (ℓ • (0 : EuclideanSpace ℝ (Fin 3)))
        (2 * (|ℓ| + 1))) (hcont.pow 2).continuousOn).mono_set
      (Work.BoseKinLoc.NeuFrac.lamBox_subset_closedBall ℓ 0)
  -- the Neumann fraction is nonnegative
  have hn : 0 ≤ Work.BoseKinLoc.neuFrac ℓ ((d * ℓ) ^ (-2 : ℤ)) 0 (Work.BoseKinLoc.Qfree ℓ 0 ψ) :=
    Work.BoseKinLoc.NeuFrac.neuFrac_nonneg_l2 ℓ ((d * ℓ) ^ (-2 : ℤ)) ha2 0 _ hI
  -- assemble with the nonnegative prefactor `½·ε_T·(dℓ)⁻²`
  unfold Work.BoseKinLoc.neuWord
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) heT) ha2) hn

end Work.BoseBoxFock.FRK
