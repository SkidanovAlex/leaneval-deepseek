import ChallengeDeps
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBogFS.honestFsCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- **The two kernel-size rows of `FsI1Regime` at the honest kernel.**

`ηT ≤ 1` and `B ≤ 100` for `K = bogKernel v R ρ μ`, whose `η` is `max 0 (16πR√(ρa))`
and whose `T` is `max 0 (bogT v R μ)`.

Route: `Work.BoseBogFS.core_bounds` (with `δ := ε₀ := min (threshold) (coreBound v R)`)
gives `Core v R μ ρ`, i.e. `0 ≤ bogEta v R ρ`, `0 < bogT v R μ`, the upper bound
`bogT ≤ 2·10⁶(323/156)·D^{-1/1292}` and `√(ρa) ≤ √(11/10)·√D/a` (`D = dil v μ`).
Hence `ηT ≤ 16π√(11/10)·(R/a)·2·10⁶(323/156)·D^{645/1292} ≤ 1` for
`D^{645/1292} ≤ a/(16π√(11/10)·2·10⁶(323/156)·R)` — a threshold of the form
`D ≤ C(a,R)` absorbable in `ε₀` (take `ε₀ = min C (coreBound v R)`).
The `B` row is then `8π + ηT ≤ 8π + 1 ≤ 100`. -/
theorem honestFsEtaT {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      (Work.BoseBogFS.bogKernel v R ρ μ).η * (Work.BoseBogFS.bogKernel v R ρ μ).T ≤ 1 ∧
      (Work.BoseBogFS.bogKernel v R ρ μ).B ≤ 100 := by
  -- the constant `M` of the threshold: `η ≤ M·D^{1/2}` and `T ≤ 2·10⁶(323/156)·D^{-1/1292}`
  set M : ℝ := 16 * Real.pi * R * Real.sqrt (11 / 10) * 2 * 10 ^ 6 * (323 / 156)
    / _root_.BoseGases.a v with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]; positivity
  have hT0pos : 0 < (1 / M) ^ ((1292 : ℝ) / 645) :=
    Real.rpow_pos_of_pos (one_div_pos.mpr hMpos) _
  refine ⟨min (coreBound v R) ((1 / M) ^ ((1292 : ℝ) / 645)),
    lt_min (coreBound_pos hR hav) hT0pos, ?_⟩
  intro μ hAdm ρ hclose
  have hμ : 0 < μ := hAdm.1
  have hDle : Work.BoseFixR.dil v μ ≤ min (coreBound v R) ((1 / M) ^ ((1292 : ℝ) / 645)) :=
    hAdm.2.1
  -- the shared parameter bounds
  have hCore : Core v R μ ρ :=
    core_bounds (δ := min (coreBound v R) ((1 / M) ^ ((1292 : ℝ) / 645)))
      hR hav (min_le_left _ _) μ ρ hμ hDle hclose
  have hD0 : 0 < Work.BoseFixR.dil v μ := hCore.hD0
  have hη0 : 0 ≤ bogEta v R ρ := hCore.hη0
  have hTpos : 0 < bogT v R μ := hCore.hTpos
  -- the diluteness is below the threshold, so `D^{645/1292} ≤ 1/M`
  have hDpow : (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292) ≤ 1 / M := by
    have h1 : (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292)
        ≤ ((1 / M) ^ ((1292 : ℝ) / 645)) ^ ((645 : ℝ) / 1292) :=
      Real.rpow_le_rpow hD0.le (le_trans hDle (min_le_right _ _)) (by norm_num)
    have h2 : ((1 / M) ^ ((1292 : ℝ) / 645)) ^ ((645 : ℝ) / 1292) = 1 / M := by
      rw [← Real.rpow_mul (le_of_lt (one_div_pos.mpr hMpos))]
      rw [show (1292 : ℝ) / 645 * (645 / 1292) = 1 by norm_num, Real.rpow_one]
    rw [h2] at h1; exact h1
  have hetaT : bogEta v R ρ * bogT v R μ ≤ 1 := by
    have h1 : bogEta v R ρ ≤ 16 * Real.pi * R * (Real.sqrt (11 / 10)
        * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v) := by
      rw [bogEta]
      exact mul_le_mul_of_nonneg_left hCore.hsqρa (by positivity)
    have h2 : bogT v R μ ≤ 2 * 10 ^ 6 * (323 / 156)
        * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ)) := hCore.hTup
    have h3 : 0 ≤ 16 * Real.pi * R * (Real.sqrt (11 / 10)
        * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v) := by positivity
    calc bogEta v R ρ * bogT v R μ
        ≤ (16 * Real.pi * R * (Real.sqrt (11 / 10)
            * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v)) * bogT v R μ :=
          mul_le_mul_of_nonneg_right h1 hTpos.le
      _ ≤ (16 * Real.pi * R * (Real.sqrt (11 / 10)
            * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2) / _root_.BoseGases.a v))
          * (2 * 10 ^ 6 * (323 / 156) * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ))) :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = M * ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 2)
            * (Work.BoseFixR.dil v μ) ^ (-(1 / 1292 : ℝ))) := by
          rw [hMdef]; ring
      _ = M * (Work.BoseFixR.dil v μ) ^ ((645 : ℝ) / 1292) := by
          rw [← Real.rpow_add hD0,
            show (1 : ℝ) / 2 + (-(1 / 1292 : ℝ)) = 645 / 1292 by norm_num]
      _ ≤ M * (1 / M) := mul_le_mul_of_nonneg_left hDpow hMpos.le
      _ = 1 := by rw [mul_one_div, div_self (ne_of_gt hMpos)]
  have hetaeq : (bogKernel v R ρ μ).η * (bogKernel v R ρ μ).T = bogEta v R ρ * bogT v R μ := by
    rw [bogKernel_eta, bogKernel_T, max_eq_right hη0, max_eq_right hTpos.le]
  constructor
  · rw [hetaeq]; exact hetaT
  · have hB : (bogKernel v R ρ μ).B = 8 * Real.pi + bogEta v R ρ * bogT v R μ := by
      rw [show (bogKernel v R ρ μ).B = 8 * Real.pi
        + (bogKernel v R ρ μ).η * (bogKernel v R ρ μ).T from rfl,
        bogKernel_eta, bogKernel_T, max_eq_right hη0, max_eq_right hTpos.le]
    rw [hB]
    linarith [Real.pi_lt_four]

end Work.BoseBogFS
