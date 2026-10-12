import ChallengeDeps
import Submission.Work.BoseBogFS.honestFsMatchEnv
import Submission.Work.BoseBogFS.honest_W1_mass_rows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.honestMeshRows` — the honest mesh/parameter rows

The rows feeding `Work.BoseBogFS.honest_hB_raw` / `honest_hpair_raw` / `honest_hA_raw` that are
pure mesh arithmetic: `hgain` (`Work.BoseBogFS.meshInj_norm_gain` at `σ := honestSigma`), `hlow`
(its corollary), `hmis` (the mesh relation in `|·| ≤ η` form) and `hrange` (the range row of
`Work.BoseBogFS.meshInj` in terms of `honestSigma`/`honestH`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- `ellH v μ = ell v μ` when `sideAt μ (a v) > 0`. -/
theorem ellH_eq_ell (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (h : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) :
    Work.BoseBoxFock.ellH v μ = Work.BoseFixR.ell v μ := by
  rw [Work.BoseBoxFock.ellH, if_pos h, ell_eq]

/-- **The mesh gain row** `hgain` at `HonestBoxFam`. -/
theorem honest_hgain {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {μ ρ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) (hρpos : 0 < ρ)
    (e : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode
      → Work.BoseB6Est.modeIdx (honestN v μ ρ))
    (hmesh : ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode, ∀ i : Fin 3,
      (Work.BoseB6.meshD (honestN v μ ρ))
          * (|((Work.BoseBoxFock.labVec (HM μ).N k i : ℤ) : ℝ)| / honestSigma v μ ρ + 1 / 2)
        ≤ |(Work.BoseB6Est.modePos (honestN v μ ρ) (e k)) i|) :
    ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
      ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖
          + π * honestSigma v μ ρ / Work.BoseFixR.ell v μ
        ≤ Real.sqrt (ρ * _root_.BoseGases.a v)
            * Submission.BoseGases.eucNorm3
                (Work.BoseB6Est.modePos (honestN v μ ρ) (e k)) := by
  have hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := sideAt_pos_honest hμ hav
  have hℓpos : 0 < Work.BoseFixR.ell v μ := by
    rw [ell_eq]; exact hside
  have hσ0 : 0 < honestSigma v μ ρ := honestSigma_pos v μ ρ (by positivity)
  have hσ1 : honestSigma v μ ρ ≤ 1 := honestSigma_le_one v μ ρ (by positivity)
  have hrel := honestSigma_rel v μ ρ (show 0 < Work.BoseFixR.ell v μ * Real.sqrt (ρ * _root_.BoseGases.a v) by positivity)
  intro k
  have hkm : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k
      = Work.BoseBoxFock.kmomLab (Work.BoseFixR.ell v μ) (HM μ).N k := by
    simp only [Work.BoseBoxFock.HonestBoxFam, Work.BoseBoxFock.ellH, if_pos hside, ell_eq]
    rfl
  have h := meshInj_norm_gain (N := (HM μ).N) (n := honestN v μ ρ)
    (ℓ := Work.BoseFixR.ell v μ) (ρz := ρ) (a := _root_.BoseGases.a v)
    (σ := honestSigma v μ ρ) hσ0 hσ1 hrel hmesh k
  simpa only [hkm, eucNorm3_eq_norm] using h

/-- **The `hlow` row**: the mesh gain without the additive term. -/
theorem honest_hlow {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {μ ρ : ℝ}
    (hpos : 0 < honestSigma v μ ρ) (hℓpos : 0 < Work.BoseFixR.ell v μ)
    (e : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode
      → Work.BoseB6Est.modeIdx (honestN v μ ρ))
    (hgain : ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
      ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖
          + π * honestSigma v μ ρ / Work.BoseFixR.ell v μ
        ≤ Real.sqrt (ρ * _root_.BoseGases.a v)
            * Submission.BoseGases.eucNorm3
                (Work.BoseB6Est.modePos (honestN v μ ρ) (e k))) :
    ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
      ‖(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k‖
        ≤ Real.sqrt (ρ * _root_.BoseGases.a v)
            * Submission.BoseGases.eucNorm3
                (Work.BoseB6Est.modePos (honestN v μ ρ) (e k)) :=
  fun k => le_trans (le_add_of_nonneg_right (by positivity)) (hgain k)

/-- **The `hmis` row**: `|(honestN : ℝ) + 1 − ℓ√(ρ a v)| ≤ (2/(ℓ√(ρ a v)))·(ℓ√(ρ a v))`. -/
theorem honest_hmis {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ ρ : ℝ}
    (hpos : 0 < Work.BoseFixR.ell v μ * Real.sqrt (ρ * _root_.BoseGases.a v)) :
    |((honestN v μ ρ : ℕ) : ℝ) + 1 - Work.BoseFixR.ell v μ * Real.sqrt (ρ * _root_.BoseGases.a v)|
      ≤ (2 / (Work.BoseFixR.ell v μ * Real.sqrt (ρ * _root_.BoseGases.a v)))
          * (Work.BoseFixR.ell v μ * Real.sqrt (ρ * _root_.BoseGases.a v)) := by
  have hc : 1 ≤ Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * _root_.BoseGases.a v) / 2) :=
    Nat.one_le_ceil_iff.mpr (by positivity)
  have hge : Work.BoseFixR.ell v μ * Real.sqrt (ρ * _root_.BoseGases.a v)
      ≤ ((honestN v μ ρ : ℕ) : ℝ) + 1 := honestN_ge v μ ρ hc
  have hlt : ((honestN v μ ρ : ℕ) : ℝ) + 1
      < Work.BoseFixR.ell v μ * Real.sqrt (ρ * _root_.BoseGases.a v) + 2 := by
    rw [honestN_succ v μ ρ hc]
    have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤
      Work.BoseFixR.ell v μ * Real.sqrt (ρ * _root_.BoseGases.a v) / 2 by positivity)
    push_cast
    linarith
  rw [div_mul_cancel₀ 2 (ne_of_gt hpos), abs_le]
  exact ⟨by linarith, by linarith⟩

end Work.BoseBogFS
