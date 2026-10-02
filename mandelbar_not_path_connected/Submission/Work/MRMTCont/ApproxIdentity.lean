/-
Work.MRMTCont — the key identity: *any* approximating family of an admissible coefficient gives
the principal solution.

`principalData_of_approx` produces a `PrincipalData μ` from an arbitrary approximating family
`smooth μn → μ` / `C¹` homeomorphisms `Fn` solving the Beltrami equation for `μn`.  Since any two
records for the same coefficient have the same homeomorphism (`records_agree_pd`), the limit of
the `Fn` is `principal μ`, not merely some homeomorphism with the same coefficient:

`Work.MRMT.Found.tendsto_principal_of_approx`.

This is the identity that the diagonal argument of `principal_tendsto_of_ae` runs on.
-/
import Mathlib
import Submission.Work.MRMTCont.PrincipalDataApprox
import Submission.Work.MRMT.Found.Principal
import Submission.Work.MRMT.Found.records_agree_pd

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

/-- **The key identity.**  Let `μ` be admissible, `μn` smooth compactly supported coefficients
with `‖μn n‖ ≤ k`, supported in the ball of radius `M`, converging to `μ` a.e., and let `Fn` be
`C¹` homeomorphisms solving `∂̄(Fn n) = μn n ∂(Fn n)` with the normalisation
`Fn n z - z = O(1/‖z‖)`.  Then `Fn n → principal μ` locally uniformly.

The proof: `principalData_of_approx` gives a record `d` for `μ` with `d.Fn = Fn`; by
`records_agree_pd`, `d.φ = principal μ`; and `d.tendsto_Fn` says exactly that `Fn → d.φ`
locally uniformly. -/
theorem tendsto_principal_of_approx {μ : ℂ → ℂ} {k M : ℝ} {μn : ℕ → ℂ → ℂ} {Fn : ℕ → ℂ ≃ₜ ℂ}
    (hμ : Admissible μ)
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hM0 : 0 ≤ M)
    (hμnC : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (μn n))
    (hμnS : ∀ n, HasCompactSupport (μn n))
    (hμnB : ∀ n z, ‖μn n z‖ ≤ k)
    (hμnSp : ∀ n z, μn n z ≠ 0 → ‖z‖ ≤ M)
    (hμnT : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Tendsto (fun n => μn n z) atTop (𝓝 (μ z)))
    (hμbd : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ z‖ ≤ k)
    (hFC : ∀ n, ContDiff ℝ 1 (Fn n : ℂ → ℂ))
    (hFCS : ∀ n, ContDiff ℝ 1 ((Fn n).symm : ℂ → ℂ))
    (hFB : ∀ n z, dzbar (Fn n : ℂ → ℂ) z = μn n z * dz (Fn n : ℂ → ℂ) z)
    (hFD : ∀ n, ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖Fn n z - z‖ ≤ C / ‖z‖) :
    TendstoLocallyUniformly (fun n => (Fn n : ℂ → ℂ)) (principal μ : ℂ → ℂ) atTop := by
  obtain ⟨d, hdFn⟩ :=
    principalData_of_approx hk0 hk1 hM0 hμnC hμnS hμnB hμnSp hμnT hμbd hFC hFCS hFB hFD
  have hdφ : (d.φ : ℂ → ℂ) = (principal μ : ℂ → ℂ) := by
    rw [principal_eq_principalData hμ]
    exact records_agree_pd hμ d (principalData μ hμ)
  have h := d.tendsto_Fn
  rw [hdFn, hdφ] at h
  exact h

end Work.MRMT.Found
