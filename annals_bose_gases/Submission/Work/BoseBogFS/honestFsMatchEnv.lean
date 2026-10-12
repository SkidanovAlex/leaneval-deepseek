import ChallengeDeps
import Submission.Work.BoseBogFS.hB_env_of_viewFS
import Submission.Work.BoseBogFS.honestZPData
import Submission.Work.BoseBogFS.meshInj
import Submission.Work.BoseBogFS.meshInj_norm_gain
import Submission.Work.BoseBogFS.tauSm_le_fsTau
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.honestFsMatchEnv` — the honest `FsMatchEnv` (stage 1: the mesh)

`FINDING_honestZP_design.md` §1: the honest envelope datum `FsMatchEnv` at
`D μ = Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ` is assembled from

* the mesh injection `e` (`Work.BoseBogFS.meshInj`) at the mesh size `honestN` and the **exact**
  mesh scale `σ := ℓ√(ρ a v)/((honestN v μ ρ : ℝ) + 1)`, which makes `meshInj`'s relation
  `(n:ℝ)+1 = ℓ√(ρ_z a)/σ` hold *by construction*; `σ ≤ 1` is then exactly
  `ℓ√(ρ a v) ≤ 2⌈ℓ√(ρ a v)/2⌉`, and `meshInj`'s range condition becomes
  `N + 2 ≤ ℓ√(ρ a v)·⌈ℓ√(ρ a v)/2⌉` (a regime row on the honest mode data `HM`);
* the honest data `honestD` (`Work.BoseBogFS.honestZPData`);
* the rows of `FsMatchEnv`: `hρ/ha/hℓ/hz/hμ` by `rfl`, `hG0` from `chiM = 1`, and
  `hA`/`hB`/`hpair` from the proved `Work.BoseBogFS.hA_env_of_rows`,
  `Work.BoseBogFS.hB_env_of_viewFS`, `Work.BoseBogFS.hpair_env_of_viewFS`.

This module provides the mesh (`honestSigma`, `honestE`) and its two properties.
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

/-- The half-mesh range `H` of the honest injection: `gridD (honestN v μ ρ) = 2H`. -/
def honestH (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ) : ℕ :=
  2 * Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2)
    * Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2)

/-- `gridD (honestN v μ ρ) = 2·honestH`. -/
theorem honestH_grid (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ)
    (h : 0 < Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v)) :
    (Work.BoseB6.gridD (honestN v μ ρ) : ℝ) = 2 * (honestH v μ ρ : ℝ) := by
  have hc : 1 ≤ Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2) :=
    Nat.one_le_ceil_iff.mpr (by positivity)
  have hidx := honestN_odd v μ ρ hc
  rw [Work.BoseB6.gridD, hidx, honestH]
  push_cast
  ring

/-- The **honest mesh scale** `σ := ℓ√(ρ a v)/((n:ℝ)+1)` with `n = honestN v μ ρ`.  It is the
unique value making `meshInj`'s relation `(n:ℝ)+1 = ℓ√(ρ_z a)/σ` hold, and it lies in `(0,1]`
because `(n:ℝ)+1 = 2⌈ℓ√(ρ a v)/2⌉ ≥ ℓ√(ρ a v)`. -/
def honestSigma (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ) : ℝ :=
  Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / (((honestN v μ ρ : ℕ) : ℝ) + 1)

/-- `ℓ√(ρ a v) ≤ (honestN : ℝ) + 1`. -/
theorem honestN_ge (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ)
    (hc : 1 ≤ Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2)) :
    Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) ≤ ((honestN v μ ρ : ℕ) : ℝ) + 1 := by
  rw [honestN_succ v μ ρ hc]
  have h := Nat.le_ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2)
  linarith

/-- The honest mesh scale is positive. -/
theorem honestSigma_pos (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ)
    (h : 0 < Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v)) :
    0 < honestSigma v μ ρ := by
  rw [honestSigma]
  positivity

/-- The honest mesh scale is at most `1`. -/
theorem honestSigma_le_one (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ)
    (h : 0 < Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v)) :
    honestSigma v μ ρ ≤ 1 := by
  have hc : 1 ≤ Nat.ceil (Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / 2) :=
    Nat.one_le_ceil_iff.mpr (by positivity)
  rw [honestSigma, div_le_one (by positivity)]
  exact honestN_ge v μ ρ hc

/-- `0 < ℓ√(ρ a v)` from `0 < honestSigma`. -/
theorem honestPos (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ)
    (hσ0 : 0 < honestSigma v μ ρ) :
    0 < Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) := by
  have h1 : (0 : ℝ) < ((honestN v μ ρ : ℕ) : ℝ) + 1 := by positivity
  have h2 : 0 < Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v)
      / (((honestN v μ ρ : ℕ) : ℝ) + 1) := by
    rwa [honestSigma] at hσ0
  rcases (div_pos_iff.mp h2) with ⟨ha, _⟩ | ⟨ha, hb⟩
  · exact ha
  · exact absurd hb (not_lt.mpr h1.le)

/-- The mesh relation `meshInj_norm_gain` needs, *by construction*. -/
theorem honestSigma_rel (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ)
    (h : 0 < Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v)) :
    ((honestN v μ ρ : ℕ) : ℝ) + 1
      = Work.BoseFixR.ell v μ * Real.sqrt (ρ * a v) / honestSigma v μ ρ := by
  rw [honestSigma, div_div_eq_mul_div, eq_div_iff (ne_of_gt h)]
  ring

/-- **The honest injection.** -/
def honestE (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ) (N : ℕ)
    (hσ0 : 0 < honestSigma v μ ρ) (hσ1 : honestSigma v μ ρ ≤ 1)
    (hrange : (N : ℝ) + 2 ≤ honestSigma v μ ρ * (honestH v μ ρ : ℝ)) :
    Work.BoseBoxFock.Lab N → Work.BoseB6Est.modeIdx (honestN v μ ρ) :=
  (meshInj (N := N) (n := honestN v μ ρ) (H := honestH v μ ρ)
    hσ0 hσ1 (honestH_grid v μ ρ (honestPos v μ ρ hσ0)) hrange).choose

/-- The honest injection is injective. -/
theorem honestE_inj (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ) (N : ℕ)
    (hσ0 : 0 < honestSigma v μ ρ) (hσ1 : honestSigma v μ ρ ≤ 1)
    (hrange : (N : ℝ) + 2 ≤ honestSigma v μ ρ * (honestH v μ ρ : ℝ)) :
    Function.Injective (honestE v μ ρ N hσ0 hσ1 hrange) := by
  rw [honestE]
  exact ((meshInj (N := N) (n := honestN v μ ρ) (H := honestH v μ ρ)
    hσ0 hσ1 (honestH_grid v μ ρ (honestPos v μ ρ hσ0)) hrange).choose_spec).1

/-- The honest injection's mesh bound. -/
theorem honestE_mesh (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ ρ : ℝ) (N : ℕ)
    (hσ0 : 0 < honestSigma v μ ρ) (hσ1 : honestSigma v μ ρ ≤ 1)
    (hrange : (N : ℝ) + 2 ≤ honestSigma v μ ρ * (honestH v μ ρ : ℝ)) :
    ∀ k : Work.BoseBoxFock.Lab N, ∀ i : Fin 3,
      (Work.BoseB6.meshD (honestN v μ ρ))
          * (|((Work.BoseBoxFock.labVec N k i : ℤ) : ℝ)| / honestSigma v μ ρ + 1 / 2)
        ≤ |(Work.BoseB6Est.modePos (honestN v μ ρ)
            (honestE v μ ρ N hσ0 hσ1 hrange k)) i| := by
  rw [honestE]
  exact ((meshInj (N := N) (n := honestN v μ ρ) (H := honestH v μ ρ)
    hσ0 hσ1 (honestH_grid v μ ρ (honestPos v μ ρ hσ0)) hrange).choose_spec).2

/-- **The honest `FsMatchEnv`**, packaged from its four genuinely new field-rows
(`FINDING_honestZP_design.md` §2).  The rows `hA`/`hB`/`hpair` are the conclusions of the proved
session-7 envelopes `Work.BoseBogFS.hA_env_of_rows`, `hB_env_of_viewFS`, `hpair_env_of_viewFS`
(the reductions `honest_hA_row`/`honest_hB_row`/`honest_hpair_row` are filed separately), and
`hG0` is `chiM = 1`. -/
theorem honestFsMatchEnv_of_rows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {R ε₀ : ℝ} {μ ρ : ℝ}
    (hR : 0 ≤ R) (hℓ3 : 3 ≤ (Work.BoseFixR.ell v μ) ^ 3)
    (hT : 0 ≤ honestZPT v μ ρ ((HM μ).N))
    (e : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode
      → Work.BoseB6Est.modeIdx (honestN v μ ρ))
    (hinj : Function.Injective e)
    (hA : ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
      bogA (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k
        ≤ Work.BoseB6Est.fsA ρ (_root_.BoseGases.a v)
            (honestK v R μ ρ ((HM μ).N) (by rw [honestZPη]; positivity) hT)
            (paramsAt μ (_root_.BoseGases.a v)).eT
            ((2 * (paramsAt μ (_root_.BoseGases.a v)).s * Work.BoseFixR.ell v μ)⁻¹
              / Real.sqrt (ρ * _root_.BoseGases.a v))
            ((2 * (paramsAt μ (_root_.BoseGases.a v)).d
                * (paramsAt μ (_root_.BoseGases.a v)).s * Work.BoseFixR.ell v μ)⁻¹
              / Real.sqrt (ρ * _root_.BoseGases.a v))
            (Work.BoseB6Est.modePos (honestN v μ ρ) (e k)))
    (hB : ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
      bogB (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k
        ≤ Work.BoseB6Est.fsB ρ (_root_.BoseGases.a v)
            (honestK v R μ ρ ((HM μ).N) (by rw [honestZPη]; positivity) hT)
            (Work.BoseB6Est.modePos (honestN v μ ρ) (e k)))
    (hpair : ∀ k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode,
      Work.BoseB6Est.fsB ρ (_root_.BoseGases.a v)
          (honestK v R μ ρ ((HM μ).N) (by rw [honestZPη]; positivity) hT)
          (Work.BoseB6Est.modePos (honestN v μ ρ) (e k))
        ≤ bogA (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ k)
    (hGw : Work.BoseB6Est.fsGω0 ρ (_root_.BoseGases.a v)
        (honestK v R μ ρ ((HM μ).N) (by rw [honestZPη]; positivity) hT)
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega0)
    (hG0 : Work.BoseB6Est.fsG0 ρ (_root_.BoseGases.a v) (Work.BoseFixR.ell v μ)
        (Real.sqrt (ρ * (Work.BoseFixR.ell v μ) ^ 3)) 1
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0) :
    ∃ M : FsMatchEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0,
      M.n = honestN v μ ρ := by
  let D0 : Work.BoseB6Est.FsBogData (honestN v μ ρ) :=
    honestD v R μ ρ ((HM μ).N) (by rw [honestZPη]; positivity) hT hℓ3
      (sum_hatChi_shifted_cube_le (honestN v μ ρ))
  refine ⟨(⟨honestN v μ ρ, D0, e, hinj, rfl, rfl, rfl, rfl, rfl, hA, hB, hpair, hGw, hG0⟩ :
    FsMatchEnv (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).gHat0), rfl⟩

end Work.BoseBogFS
