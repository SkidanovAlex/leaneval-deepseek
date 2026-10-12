import ChallengeDeps
import Submission.Work.BoseBogFS.tauAdmParams
import Submission.Work.BoseBogFS.tauAt_bounds
import Submission.Work.BoseBogFS.tauComboBounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.tauAt_bounds_row` — the four elementary bounds of `τ = tauAt`

`τ = tauAt v μ k = tauSm eT s d ℓ k` is the smoothed kinetic symbol
`(1−ε_T)c₁²τ̃(‖k‖/c₁) + ε_T c₂²τ̃(‖k‖/c₂)` at FS's parameters, with the two thresholds
`c₁ = (2sℓ)⁻¹ = cleanLo1`, `c₂ = (2dsℓ)⁻¹ = cleanLo2` and the profile `τ̃ = tauProf` of
`Work.BoseBoxFock.exists_tauProf` (`(max 0 (r−2))² ≤ τ̃ r ≤ (max 0 (r−1))²`, `τ̃ r = 0` for `r ≤ 1`).

Since `s = (μa³)^{1/323}` and `d = (μa³)^{6/323} ≤ 1` in the admissible regime, one has
`c₂ ≥ c₁`, i.e. `cleanLoMin = c₁` and `cleanLoMax = c₂`, and `ε_T = (μa³)^{23/1292} ≤ 1/2` once
the diluteness is small enough; the threshold `ε₀` of this row is chosen to make that hold
(`Work.BoseBogFS.tauAdmParams`).  The four bounds then follow from the profile axioms by pure
real arithmetic (`Work.BoseBogFS.tauComboBounds`):

* `0 ≤ τ ≤ ‖k‖²`;
* `τ = 0` for `‖k‖ ≤ cleanLoMin` (the kinetic gap at the origin);
* `(max 0 (‖k‖ − 2·cleanLoMax))² ≤ 2τ` (the quadratic growth beyond the kink; the factor `2` is
  the loss of the `(1−ε_T) ≥ 1/2` coefficient of the first term);
* `‖k‖² − τ ≤ 4·cleanLoMax·‖k‖ + (cleanLoMax)²` (the deficit of `τ` below `‖k‖²`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option linter.unusedVariables false

theorem tauAt_bounds_row {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ k : EuclideanSpace ℝ (Fin 3),
        0 ≤ Work.BoseBogFS.tauAt v μ k ∧
        Work.BoseBogFS.tauAt v μ k ≤ ‖k‖ ^ 2 ∧
        (‖k‖ ≤ Work.BoseBogFS.cleanLoMin v μ → Work.BoseBogFS.tauAt v μ k = 0) ∧
        (max 0 (‖k‖ - 2 * Work.BoseBogFS.cleanLoMax v μ)) ^ 2 ≤ 2 * Work.BoseBogFS.tauAt v μ k ∧
        ‖k‖ ^ 2 - Work.BoseBogFS.tauAt v μ k
          ≤ 4 * Work.BoseBogFS.cleanLoMax v μ * ‖k‖ + (Work.BoseBogFS.cleanLoMax v μ) ^ 2 := by
  obtain ⟨ε₀, hε₀, hparams⟩ := Work.BoseBogFS.tauAdmParams hav
  refine ⟨ε₀, hε₀, fun μ hμ k => ?_⟩
  obtain ⟨hs0, hd0, hd1, heT0, heT1, hell⟩ := hparams μ hμ
  have hprof := Work.BoseBogFS.tauProf_facts
  -- the two thresholds, `c₁ = cleanLo1` and `c₂ = cleanLo2`
  have hc1 : 0 < (2 * (Work.BoseBox.paramsAt μ (a v)).s * Work.BoseFixR.ell v μ)⁻¹ := by positivity
  have hc2 : 0 < (2 * (Work.BoseBox.paramsAt μ (a v)).d * (Work.BoseBox.paramsAt μ (a v)).s
      * Work.BoseFixR.ell v μ)⁻¹ := by positivity
  -- `d ≤ 1` gives `c₁ ≤ c₂`
  have hc12 : (2 * (Work.BoseBox.paramsAt μ (a v)).s * Work.BoseFixR.ell v μ)⁻¹
      ≤ (2 * (Work.BoseBox.paramsAt μ (a v)).d * (Work.BoseBox.paramsAt μ (a v)).s
          * Work.BoseFixR.ell v μ)⁻¹ := by
    rw [inv_le_inv₀
      (by positivity : (0 : ℝ) < 2 * (Work.BoseBox.paramsAt μ (a v)).s * Work.BoseFixR.ell v μ)
      (by positivity : (0 : ℝ) < 2 * (Work.BoseBox.paramsAt μ (a v)).d
        * (Work.BoseBox.paramsAt μ (a v)).s * Work.BoseFixR.ell v μ)]
    have hpos : (0 : ℝ) < 2 * (Work.BoseBox.paramsAt μ (a v)).s * Work.BoseFixR.ell v μ :=
      by positivity
    have h := mul_le_mul_of_nonneg_right hd1 hpos.le
    linarith [h]
  -- the pure-real core at the two thresholds
  have hcore := Work.BoseBogFS.tauComboBounds Work.BoseBoxFock.tauProf
    hprof.2.1 hprof.2.2.1 hprof.2.2.2 heT0 heT1 hc1 hc12 (norm_nonneg k)
  have hmin : Work.BoseBogFS.cleanLoMin v μ
      = (2 * (Work.BoseBox.paramsAt μ (a v)).s * Work.BoseFixR.ell v μ)⁻¹ := by
    rw [Work.BoseBogFS.cleanLoMin]; exact min_eq_left hc12
  have hmax : Work.BoseBogFS.cleanLoMax v μ
      = (2 * (Work.BoseBox.paramsAt μ (a v)).d * (Work.BoseBox.paramsAt μ (a v)).s
          * Work.BoseFixR.ell v μ)⁻¹ := by
    rw [Work.BoseBogFS.cleanLoMax]; exact max_eq_right hc12
  -- `tauAt` unfolded at the two thresholds
  have htau : Work.BoseBogFS.tauAt v μ k
      = (1 - (Work.BoseBox.paramsAt μ (a v)).eT)
          * ((2 * (Work.BoseBox.paramsAt μ (a v)).s * Work.BoseFixR.ell v μ)⁻¹) ^ 2
          * Work.BoseBoxFock.tauProf (‖k‖ / (2 * (Work.BoseBox.paramsAt μ (a v)).s
              * Work.BoseFixR.ell v μ)⁻¹)
        + (Work.BoseBox.paramsAt μ (a v)).eT
          * ((2 * (Work.BoseBox.paramsAt μ (a v)).d * (Work.BoseBox.paramsAt μ (a v)).s
              * Work.BoseFixR.ell v μ)⁻¹) ^ 2
          * Work.BoseBoxFock.tauProf (‖k‖ / (2 * (Work.BoseBox.paramsAt μ (a v)).d
              * (Work.BoseBox.paramsAt μ (a v)).s * Work.BoseFixR.ell v μ)⁻¹) := rfl
  rw [htau, hmin, hmax]
  exact hcore

end Work.BoseBogFS
