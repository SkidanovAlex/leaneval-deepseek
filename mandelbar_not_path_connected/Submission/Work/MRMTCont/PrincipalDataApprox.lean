/-
Work.MRMTCont — the reusable "limit layer" of the measurable Riemann mapping theorem.

`principalData_exists` (`Submission/Work/MRMT/Found/principalData_exists.lean`) proves the
existence of a `PrincipalData μ` for an admissible coefficient `μ` by mollifying `μ` and
assembling the record from `forward_limit_pd` and `inverse_limit`.  The assembly step does not
use anything about *how* the approximating family was produced: it only needs

* smooth compactly supported coefficients `μn n` bounded by a common `k < 1`, supported in a
  common ball, converging to `μ` a.e.,
* `‖μ‖ ≤ k` a.e., and
* `C¹` homeomorphisms `Fn n` solving `∂̄ (Fn n) = μn n · ∂ (Fn n)` with the normalisation
  `Fn n z - z = O(1/‖z‖)`.

This file extracts that step as `principalData_of_approx`, so that the *same* assembly can be
run on any approximating family — in particular on the diagonal family produced in
`Work.MRMT.Found.principal_tendsto_of_ae`, where the family is not a mollification.

The extraction is a pure refactor: `principalData_exists` was rewritten to call it.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.forward_limit_pd
import Submission.Work.MRMT.Found.inverse_limit

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

/-- **The limit layer of the measurable Riemann mapping theorem, on an arbitrary approximating
family.**  Given smooth compactly supported coefficients `μn` with `‖μn n‖ ≤ k < 1` supported
in the ball of radius `M`, with `μn n → μ` a.e. and `‖μ‖ ≤ k` a.e., together with `C¹`
homeomorphisms `Fn` of `ℂ` solving the Beltrami equation `∂̄(Fn n) = μn n ∂(Fn n)` and decaying
like `z + O(1/‖z‖)`, there is a `PrincipalData μ` whose approximating homeomorphisms are the
given `Fn`.

This is exactly lines 43ff of `principalData_exists`, with the mollification data taken as
hypotheses rather than constructed. -/
theorem principalData_of_approx {μ : ℂ → ℂ} {k M : ℝ} {μn : ℕ → ℂ → ℂ} {Fn : ℕ → ℂ ≃ₜ ℂ}
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
    ∃ d : PrincipalData μ, (d.Fn : ℕ → ℂ ≃ₜ ℂ) = Fn := by
  classical
  -- the forward limit: local uniform convergence, uniform decay, `L²`-limit of `∂`
  obtain ⟨φ, D, Cd, Rd, hφc, hφconv, hφdec, hFdec, hDtend⟩ :=
    forward_limit_pd hk0 hk1 hM0 hμnC hμnS hμnB hμnSp hμnT hμbd hFC hFCS hFB hFD
  -- enlarge the decay constants so that they are non-negative / at least one
  have hCd' : 0 ≤ max Cd 0 := le_max_right _ _
  have hRd' : 1 ≤ max Rd 1 := le_max_right _ _
  have hFdec' : ∀ n : ℕ, ∀ z : ℂ, max Rd 1 ≤ ‖z‖ → ‖Fn n z - z‖ ≤ max Cd 0 / ‖z‖ := by
    intro n z hz
    exact (hFdec n z (le_trans (le_max_left _ _) hz)).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (norm_nonneg z))
  have hφdec' : ∀ z : ℂ, max Rd 1 ≤ ‖z‖ → ‖φ z - z‖ ≤ max Cd 0 / ‖z‖ := by
    intro z hz
    exact (hφdec z (le_trans (le_max_left _ _) hz)).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (norm_nonneg z))
  -- the inverse limit
  obtain ⟨ψ, hψc, hψconv, hφψ, hψφ⟩ :=
    inverse_limit hk0 hk1 hM0 hCd' hRd' hμnB hμnSp hFC hFCS hFB hFdec' hφconv
  -- assemble the homeomorphism
  let Φ : ℂ ≃ₜ ℂ :=
    { toFun := φ
      invFun := ψ
      left_inv := hψφ
      right_inv := hφψ
      continuous_toFun := hφc
      continuous_invFun := hψc }
  exact ⟨
    { φ := Φ
      C := max Cd 0
      R := max Rd 1
      decay := hφdec'
      k := k
      hk := hk1
      μn := μn
      contDiff_μn := fun n => (hμnC n).of_le (by simp)
      compactSupport_μn := hμnS
      norm_μn := hμnB
      tendsto_μn := hμnT
      Fn := Fn
      contDiff_Fn := hFC
      contDiff_symm_Fn := hFCS
      beltrami_Fn := hFB
      tendsto_Fn := hφconv
      tendsto_symm_Fn := hψconv
      dz_tendsto := ⟨D, hDtend⟩ }, rfl⟩

end Work.MRMT.Found
