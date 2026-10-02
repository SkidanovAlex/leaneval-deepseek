/-
Work.MRMTCont — a ready-made approximating family for an admissible coefficient.

For an admissible `μ` bounded a.e. by `k < 1` and supported in `closedBall 0 R`, this packages

* smooth compactly supported coefficients `ν n`, bounded by the *same* `k`, supported in the
  fixed ball of radius `R + 1`, with `ν n → μ` a.e. (`mollify_admissible_of_bound_ball`);
* `C¹` homeomorphisms `F n` solving `∂̄(F n) = ν n ∂(F n)` with `F n z - z = O(1/‖z‖)`
  (`exists_contDiff_principal_of_contDiff`);
* the conclusion `F n → principal μ` locally uniformly (`tendsto_principal_of_approx`).

The uniform bounds are what makes the family usable in a diagonal argument: they do not depend on
`μ`.
-/
import Mathlib
import Submission.Work.MRMTCont.ApproxIdentity
import Submission.Work.MRMT.Found.MollifyBound
import Submission.Work.MRMT.Found.exists_contDiff_principal_of_contDiff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

open Work.MRMT

/-- A uniform approximating family for an admissible coefficient, together with the convergence
of its solutions to `principal μ`. -/
theorem exists_approx_of_admissible {μ : ℂ → ℂ} (hμ : Admissible μ) {k R : ℝ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hR0 : 0 ≤ R)
    (hsupp : Function.support μ ⊆ Metric.closedBall 0 R)
    (hb : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k) :
    ∃ (ν : ℕ → ℂ → ℂ) (F : ℕ → ℂ ≃ₜ ℂ),
      (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ν n)) ∧
      (∀ n, HasCompactSupport (ν n)) ∧
      (∀ n z, ‖ν n z‖ ≤ k) ∧
      (∀ n z, ν n z ≠ 0 → ‖z‖ ≤ R + 1) ∧
      (∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
        Tendsto (fun n => ν n z) atTop (𝓝 (μ z))) ∧
      (∀ n, ContDiff ℝ 1 (F n : ℂ → ℂ)) ∧
      (∀ n, ContDiff ℝ 1 ((F n).symm : ℂ → ℂ)) ∧
      (∀ n z, dzbar (F n : ℂ → ℂ) z = ν n z * dz (F n : ℂ → ℂ) z) ∧
      (∀ n, ∃ C R' : ℝ, ∀ z : ℂ, R' ≤ ‖z‖ → ‖F n z - z‖ ≤ C / ‖z‖) ∧
      TendstoLocallyUniformly (fun n => (F n : ℂ → ℂ)) (principal μ : ℂ → ℂ) atTop := by
  obtain ⟨ν, hν1, hν2, hν3, hν4, hν5⟩ :=
    mollify_admissible_of_bound_ball hμ hk0 hk1 hR0 hsupp hb
  choose F hF1 hF2 hF3 hF4 using fun n =>
    exists_contDiff_principal_of_contDiff (hν1 n) (hν2 n) hk1 (hν3 n)
  exact ⟨ν, F, hν1, hν2, hν3, hν4, hν5, hF1, hF2, hF3, hF4,
    tendsto_principal_of_approx hμ hk0 hk1 (by linarith) hν1 hν2 hν3 hν4 hν5 hb hF1 hF2 hF3 hF4⟩

end Work.MRMT.Found
