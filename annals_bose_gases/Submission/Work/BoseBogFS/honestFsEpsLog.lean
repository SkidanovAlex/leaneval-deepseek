import ChallengeDeps
import Submission.Work.BoseBogFS.bogC2InvLogLe
import Submission.Work.BoseBogFS.bogEpsLogArith
import Submission.Work.BoseBogFS.bogTLogLe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

local notation "DIL" => Work.BoseFixR.dil

/-- **The `hEpsLog` row of `FsI1Regime` at the honest kernel.**

`(K_ℓ s)⁻¹·(1 + log(T/c₂)) ≤ ε`, where `T = max 0 (bogT v R μ)`,
`c₂ = bogC2 v ρ μ` and `ε = lhyEps (a v) R ε_T K_ℓ s d μ`.

Route.  `Work.BoseBogFS.core_bounds` gives `Core v R μ ρ`; with `D = dil v μ`,
`L = log D^{-1}` and `B = D^{1/1292} ≤ 1/1024` (`Core.hDs`) one has
`(K_ℓs)⁻¹ = D^{1/646} = B²` (`Work.BoseBogFS.sKl_inv`), `lhyEps = lhyEpsX` (`Core.hEeq`)
and `lhyEpsX ≥ B(1 + (156/323)L)` (`Core.hE3`), `≥ B²(1 + (162/323)L)` (`Core.hE2`).
It remains to bound `1 + log(T/c₂)` by `(1+K)(1 + L)` with a *linear* rate `K`, and the
two logarithms come from

* `log T ≤ log 10⁶ + log(1+L) - log ε` with `-log ε ≤ (1/1292)L` (from `ε ≥ D^{1/1292}`,
  `Real.log_rpow`) and `log(1+L) ≤ L` (`Real.log_le_sub_one_of_pos`), so `log T ≤ 14 + 1.001L`;
* `1/c₂ = 2·D^{11/646}·√(ρ/μ) ≤ 4·D^{11/646}` (from `Core.hρhi`, `ρ ≤ 11/10 μ`), so
  `log(1/c₂) ≤ 2 + (11/646)L` via `Real.log_le_sub_one_of_pos` (or `log_mul` + `log_rpow`).

Hence `(K_ℓs)⁻¹(1+log(T/c₂)) ≤ B²(17+1.02L)`, and it suffices that
`B(16+0.52L) ≤ 1 + 0.483L` (deduced from `Core.hE2`/`Core.hE3` after dividing by `B`).
The ratio `(1+0.483L)/(16+0.52L)` is increasing in `L ≥ 0` with value `1/16` at `L = 0`,
so `B ≤ 1/16` suffices — and `Core.hDs` gives the much stronger `B ≤ 1/1024`.
No extra threshold beyond `coreBound v R` is needed (mind the divisions: `B²·X ≤ B·Y`
needs `B > 0`). -/
theorem honestFsEpsLog {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹
        * (1 + Real.log ((Work.BoseBogFS.bogKernel v R ρ μ).T / Work.BoseBogFS.bogC2 v ρ μ))
        ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  refine ⟨coreBound v R, coreBound_pos hR hav, ?_⟩
  intro μ hAdm ρ hclose
  have hμ : 0 < μ := hAdm.1
  have hDle : DIL v μ ≤ coreBound v R := hAdm.2.1
  have hCore : Core v R μ ρ := core_bounds hR hav le_rfl μ ρ hμ hDle hclose
  have hD0 : 0 < DIL v μ := hCore.hD0
  have hL0 : 0 ≤ bogL v μ := hCore.hL0
  have hBpos : 0 < DIL v μ ^ ((1:ℝ)/1292) := Real.rpow_pos_of_pos hD0 _
  have hBle : DIL v μ ^ ((1:ℝ)/1292) ≤ 1 / 1024 := hCore.hDs
  -- `(K_ℓ s)^{-1} = B²`
  have hKlsinv : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ = (DIL v μ ^ ((1:ℝ)/1292)) ^ 2 := by
    rw [mul_comm (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s, sKl_inv v μ hD0,
      pow_two, ← Real.rpow_add hD0]
    norm_num
  -- positivity of `c₂` (needed for the logarithmic split)
  have hc2pos : 0 < bogC2 v ρ μ := by
    have hc2form := bogC2_eq v ρ μ hav hμ hCore.hρ0
    have hprodeq : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s = DIL v μ ^ ((11:ℝ)/646) := by
      rw [← dsKl_eq v μ hD0]
      ring
    have hXpos : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s := by
      rw [hprodeq]; exact Real.rpow_pos_of_pos hD0 _
    have hYpos : 0 < Real.sqrt (μ/ρ) := Real.sqrt_pos.mpr (div_pos hμ hCore.hρ0)
    rw [hc2form]
    exact mul_pos (mul_pos (by norm_num) (inv_pos.mpr hXpos)) hYpos
  -- the split of `log (T / c₂)`
  have hTbog : (bogKernel v R ρ μ).T = bogT v R μ := by
    rw [bogKernel_T, max_eq_right hCore.hTpos.le]
  have hloginv : Real.log (1 / bogC2 v ρ μ) = - Real.log (bogC2 v ρ μ) := by
    rw [one_div, Real.log_inv]
  have hlogsplit : Real.log ((bogKernel v R ρ μ).T / bogC2 v ρ μ)
      = Real.log (bogT v R μ) + Real.log (1 / bogC2 v ρ μ) := by
    rw [hTbog, Real.log_div (ne_of_gt hCore.hTpos) (ne_of_gt hc2pos), hloginv]
    ring
  have hYbound : 1 + Real.log ((bogKernel v R ρ μ).T / bogC2 v ρ μ)
      ≤ 58 + (1293/1292) * bogL v μ := by
    have hA' := bogTLogLe hCore
    have hB' := bogC2InvLogLe hav hCore
    rw [hlogsplit]
    linarith
  rw [hKlsinv, hCore.hEeq]
  exact bogEpsLogArith hBpos hBle hL0 hYbound hCore.hE3

end Work.BoseBogFS
