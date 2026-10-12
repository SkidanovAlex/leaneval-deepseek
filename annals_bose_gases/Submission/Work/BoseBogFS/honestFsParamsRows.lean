import ChallengeDeps
import Submission.Work.BoseBogFS.honestFsCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

/-- `1 ≤ D^e` for `0 < D ≤ 1` and `e ≤ 0`. -/
lemma one_le_rpow_of_le_one_of_nonpos {D e : ℝ} (h0 : 0 < D) (h1 : D ≤ 1) (he : e ≤ 0) :
    1 ≤ D ^ e := by
  rw [show e = -(-e) by ring, Real.rpow_neg h0.le]
  rw [one_le_inv₀ (Real.rpow_pos_of_pos h0 _)]
  exact Real.rpow_le_one h0.le h1 (by linarith)

/-- **The thirteen parameter/E-rows of `FsI1Regime` at the honest kernel.**

At the honest parameter block `K_ℓ = D^{-3/646}`, `s = D^{1/323}`, `d = D^{6/323}`,
`ε_T = D^{23/1292}` (`D = dil v μ = μ(a v)³`) and the kernel `K = bogKernel v R ρ μ`:
`K_ℓ > 0`, `s > 0`, `d > 0`, `ε_T ≥ 0`, `ε_T ≤ 1/2`, `d ≤ 1`, `K_ℓ s ≥ 1`,
`K_ℓ d s/D^{1/2} ≥ 1` (`hlog1`), `ε_T ≤ ε`, `(μa)^{1/4}√R ≤ ε`, `(K_ℓs)⁻¹ ≤ ε`
(`ε = lhyEps (a v) R ε_T K_ℓ s d μ`), `1 ≤ K.T` and `bogC1 v ρ μ < K.T`.

Route.  `Work.BoseBogFS.core_bounds` gives `Core v R μ ρ` with `D ≤ 1` (`Core.hD1`),
`D^{1/1292} ≤ 1/1024` (`Core.hDs`), `1 ≤ L = log D^{-1}` (`Core.hL1`) and the
`lhyEpsX` bounds `Core.hEeq`, `Core.hE1` (so `ε ≥ D^{23/1292} = ε_T`), `Core.hEμa`
(so `ε ≥ (μa)^{1/4}√R`) and `Core.hE2` (so `ε ≥ D^{1/646} = (K_ℓs)⁻¹`, using
`Work.BoseBogFS.sKl_inv` and `1 + (162/323)L ≥ 1`).  The monomial rows are instances of
`Work.BoseBogFS.paramsAt_s/d/eT/Kl` and `Work.BoseBogFS.rpow_le_one'`:
`ε_T = D^{23/1292} ≤ 1/2` (from `D^{1/1292} ≤ 1/1024`), `d = D^{6/323} ≤ 1`,
`K_ℓ s = D^{-1/646} ≥ 1`, `K_ℓ d s/D^{1/2} = D^{11/646-1/2} = D^{-156/323} ≥ 1`.
Finally `1 ≤ K.T`: `K.T = bogT` by `Core.hTpos` and `10⁶/4 ≤ bogT` (`Core.hTlow`).
For `bogC1 v ρ μ < K.T` use `Work.BoseBogFS.bogC1_eq`:
`bogC1 = ½D^{1/646}√(μ/ρ) ≤ ½·(1/1024)²·2 < 10⁶/4 ≤ K.T` (`Core.hρsqrt`, `Core.hDs`).
No threshold beyond `coreBound v R` is needed; `ε₀ = coreBound v R` works. -/
theorem honestFsParamsRows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl ∧
      0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ∧
      0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ∧
      0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ∧
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1 / 2 ∧
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 ∧
      1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ∧
      1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
            / (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) ∧
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ ∧
      (μ * _root_.BoseGases.a v) ^ (1 / 4 : ℝ) * Real.sqrt R
          ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ ∧
      ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹
          ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ ∧
      1 ≤ (Work.BoseBogFS.bogKernel v R ρ μ).T ∧
      Work.BoseBogFS.bogC1 v ρ μ < (Work.BoseBogFS.bogKernel v R ρ μ).T := by
  refine ⟨coreBound v R, coreBound_pos hR hav, ?_⟩
  intro μ hAdm ρ hclose
  have hμ : 0 < μ := hAdm.1
  have hDδ : Work.BoseFixR.dil v μ ≤ coreBound v R := hAdm.2.1
  have hC : Core v R μ ρ := core_bounds hR hav le_rfl μ ρ hμ hDδ hclose
  have hD0 : 0 < Work.BoseFixR.dil v μ := hC.hD0
  have hD1 : Work.BoseFixR.dil v μ ≤ 1 := hC.hD1
  have hDs : Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 1292) ≤ 1 / 1024 := hC.hDs
  -- the monomial identities for the parameter block
  have hKs : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      = Work.BoseFixR.dil v μ ^ (-(1 / 646 : ℝ)) := by
    rw [paramsAt_Kl, paramsAt_s, ← Real.rpow_add hD0]
    norm_num
  have hKsi : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹
      = Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 646) := by
    rw [mul_comm, sKl_inv v μ hD0]
  have hKds : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      = Work.BoseFixR.dil v μ ^ ((11 : ℝ) / 646) := by
    rw [← dsKl_eq v μ hD0]
    ring
  -- `T = bogT ≥ 1`
  have hTmax : max 0 (bogT v R μ) = bogT v R μ :=
    max_eq_right (by linarith [hC.hTlow] : (0 : ℝ) ≤ bogT v R μ)
  have hT1 : 1 ≤ (Work.BoseBogFS.bogKernel v R ρ μ).T := by
    rw [bogKernel_T, hTmax]
    linarith [hC.hTlow]
  have hD646 : Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 646) ≤ (1 / 1024) ^ 2 := by
    rw [show (1 : ℝ) / 646 = (1 / 1292) * 2 by norm_num, Real.rpow_mul hD0.le]
    rw [← Real.rpow_natCast ((1 : ℝ) / 1024) 2]
    exact Real.rpow_le_rpow (x := Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 1292))
      (y := 1 / 1024) (z := (2 : ℝ)) (Real.rpow_nonneg hD0.le _) hDs (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [paramsAt_Kl]
    exact Real.rpow_pos_of_pos hD0 _
  · rw [paramsAt_s]
    exact Real.rpow_pos_of_pos hD0 _
  · rw [paramsAt_d]
    exact Real.rpow_pos_of_pos hD0 _
  · rw [paramsAt_eT]
    exact (Real.rpow_pos_of_pos hD0 _).le
  · rw [paramsAt_eT]
    have h22 : Work.BoseFixR.dil v μ ^ ((22 : ℝ) / 1292) ≤ 1 :=
      Real.rpow_le_one hD0.le hD1 (by norm_num)
    have hsplit : Work.BoseFixR.dil v μ ^ ((23 : ℝ) / 1292)
        = Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 1292)
          * Work.BoseFixR.dil v μ ^ ((22 : ℝ) / 1292) := by
      rw [← Real.rpow_add hD0]
      norm_num
    have hmul : Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 1292)
        * Work.BoseFixR.dil v μ ^ ((22 : ℝ) / 1292) ≤ (1 / 1024) * 1 :=
      mul_le_mul hDs h22 (Real.rpow_nonneg hD0.le _) (by norm_num)
    linarith [hsplit, hmul]
  · rw [paramsAt_d]
    exact Real.rpow_le_one hD0.le hD1 (by norm_num)
  · rw [hKs]
    exact one_le_rpow_of_le_one_of_nonpos hD0 hD1 (by norm_num)
  · have hden : (μ * _root_.BoseGases.a v ^ 3) = Work.BoseFixR.dil v μ := rfl
    rw [hKds, hden, ← Real.rpow_sub hD0 ((11 : ℝ) / 646) ((1 : ℝ) / 2)]
    rw [show (11 : ℝ) / 646 - 1 / 2 = -(156 / 323) by norm_num]
    exact one_le_rpow_of_le_one_of_nonpos hD0 hD1 (by norm_num)
  · rw [hC.hEeq, paramsAt_eT]
    exact hC.hE1
  · rw [hC.hEeq]
    exact hC.hEμa
  · rw [hKsi]
    rw [hC.hEeq]
    have hfac : 1 ≤ 1 + ((162 : ℝ) / 323) * bogL v μ := by
      have := hC.hL1
      linarith
    have h1 : Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 646)
        ≤ Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 646)
          * (1 + ((162 : ℝ) / 323) * bogL v μ) :=
      le_mul_of_one_le_right (Real.rpow_nonneg hD0.le _) hfac
    exact le_trans h1 hC.hE2
  · exact hT1
  · have hc1 : bogC1 v ρ μ ≤ (1 / 1024) ^ 2 := by
      rw [bogC1_eq v ρ μ hav hC.hμ hC.hρ0, hKsi]
      have h1 : (1 / 2 : ℝ) * Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 646)
            * Real.sqrt (μ / ρ)
          ≤ (1 / 2 : ℝ) * Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 646) * 2 := by
        apply mul_le_mul_of_nonneg_left hC.hρsqrt
        positivity
      have h2 : (1 / 2 : ℝ) * Work.BoseFixR.dil v μ ^ ((1 : ℝ) / 646) * 2
          ≤ (1 / 2 : ℝ) * (1 / 1024) ^ 2 * 2 := by
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hD646 (by norm_num)
      linarith [h1, h2]
    have hnum : (1 / 1024 : ℝ) ^ 2 < 1 := by norm_num
    linarith [hc1, hnum, hT1]

end Work.BoseBogFS
