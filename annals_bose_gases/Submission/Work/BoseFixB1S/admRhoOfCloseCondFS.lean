import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseGateFS.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.admRhoOfCloseCondFS` — `CloseCondFS` gives the `AdmRho` window

Audit repair (session 7) for the `CloseCond → CloseCondFS` migration of the §10 gate lane:
the old helper `Work.BoseGateFS.adm_of_closeCond'` (`HonestInhab.lean`) derives the `AdmRho` window
`0 ≤ ρ ∧ E.mu/2 ≤ ρ ∧ ρ ≤ 3E.mu/2` from the *old* threshold `closeThreshold v μ = μ(dil)^{3/323}`.
The corrected threshold is `closeThresholdFS v μ = μK_ℓ⁻²/(2¹⁴π)`, for which the same conclusion
holds **with no diluteness hypothesis at all**:

    |ρ − μ| ≤ μK_ℓ⁻²/(2¹⁴π) ≤ μ/2      (K_ℓ ≥ 1 ⟸ μ(a v)³ ≤ 1),

so the migration needs only this lemma (it is the `CloseCondFS`-version of
`adm_of_closeCond'`), and no re-derivation per call site.

`#print axioms` is `[propext, Classical.choice, Quot.sound]`. -/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBoxFix Work.BoseBox

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`CloseCondFS` implies the `AdmRho` window** (the corrected-threshold version of
`Work.BoseGateFS.adm_of_closeCond'`). -/
theorem admRho_of_closeCondFS {v : E3 → ℝ} {μ ρ : ℝ} {Mode : Type*} [AddCommGroup Mode]
    [Fintype Mode] (E : Work.BoseB7.Q3Env Mode) (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ)
    (hEmu : E.mu = μ) (ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1)
    (hclose : Work.BoseBoxFock.CloseCondFS v μ ρ) : Work.BoseGateFS.AdmRho E ρ := by
  have hKl1 : 1 ≤ (paramsAt μ (_root_.BoseGases.a v)).Kl :=
    Work.BoseFixB1.one_le_Kl hμ hav ht1
  have hKlpos : 0 < (paramsAt μ (_root_.BoseGases.a v)).Kl := lt_of_lt_of_le one_pos hKl1
  have hone : (1 : ℝ) ≤ (paramsAt μ (_root_.BoseGases.a v)).Kl ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hKlinv : (paramsAt μ (_root_.BoseGases.a v)).Kl ^ (-(2 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg (le_of_lt hKlpos)]
    exact inv_le_one_of_one_le₀ hone
  have hthr : Work.BoseBoxFock.closeThresholdFS v μ ≤ μ / 2 := by
    rw [Work.BoseBoxFock.closeThresholdFS]
    have hden : (0 : ℝ) < (2 : ℝ) ^ 14 * π := by positivity
    have hnum : μ * (paramsAt μ (_root_.BoseGases.a v)).Kl ^ (-(2 : ℝ)) ≤ μ * 1 := by
      exact mul_le_mul_of_nonneg_left hKlinv hμ.le
    have h1 : μ * (paramsAt μ (_root_.BoseGases.a v)).Kl ^ (-(2 : ℝ)) / ((2 : ℝ) ^ 14 * π)
        ≤ μ * 1 / ((2 : ℝ) ^ 14 * π) := by
      exact div_le_div_of_nonneg_right hnum hden.le
    have h2 : μ * 1 / ((2 : ℝ) ^ 14 * π) ≤ μ / 2 := by
      rw [div_le_iff₀ hden, div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have hπ : (3 : ℝ) < π := Real.pi_gt_three
      have h2p : (16384 : ℝ) ≤ (2 : ℝ) ^ 14 := by norm_num
      nlinarith [hπ, hμ.le]
    linarith
  have habs : |ρ - μ| ≤ μ / 2 := le_trans hclose hthr
  obtain ⟨hlo, hhi⟩ := abs_le.mp habs
  exact ⟨by linarith, by rw [hEmu]; linarith, by rw [hEmu]; linarith⟩

end Work.BoseFixB1S
