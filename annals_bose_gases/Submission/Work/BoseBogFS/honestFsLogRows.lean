import ChallengeDeps
import Submission.Work.BoseBogFS.bogL_ge
import Submission.Work.BoseBogFS.honestFsEtaT
import Submission.Work.BoseBogFS.logBogTBound
import Submission.Work.BoseBogFS.row1Arith
import Submission.Work.BoseBogFS.row2Arith
import Submission.Work.BoseBogFS.row3Arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric
open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 0. The two monomial evaluations of the cutoffs

`c₁ = bogC1 v ρ μ` and `ε_T c₂` (`c₂ = bogC2 v ρ μ`) are
`½(K_ℓs)^{-1}√(μ/ρ)` and `½(K_ℓds)^{-1}√(μ/ρ)` (`honestFsCore.bogC1_eq`, `bogC2_eq`); with
`(K_ℓs)^{-1} = D^{1/646}` (`honestFsCore.sKl_inv`) and
`ε_T(K_ℓds)^{-1} = D^{1/1292}` (`honestFsCore.eT_dsKl_inv`) they become the monomials
`½D^{1/646}√(μ/ρ)` and `½D^{1/1292}√(μ/ρ)` of the diluteness `D = dil v μ`.  Since
`D^{1/646} = B²` with `B = D^{1/1292}`, this is the `½(B² + B)√(μ/ρ)` of the target. -/

/-- `c₁ = ½ D^{1/646}√(μ/ρ)` at the honest parameters. -/
private lemma bogC1_val (v : E3 → ℝ) (ρ μ : ℝ) (hav : 0 < _root_.BoseGases.a v)
    (hμ : 0 < μ) (hρ : 0 < ρ) :
    bogC1 v ρ μ = (1 / 2) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
      * Real.sqrt (μ / ρ) := by
  rw [bogC1_eq v ρ μ hav hμ hρ]
  have h : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹
      = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646) := by
    rw [show (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl by ring]
    exact sKl_inv v μ (dil_pos v hμ hav)
  rw [h]

/-- `ε_T c₂ = ½ D^{1/1292}√(μ/ρ)` at the honest parameters. -/
private lemma eT_mul_bogC2_val (v : E3 → ℝ) (ρ μ : ℝ)
    (hD0 : 0 < Work.BoseFixR.dil v μ) (hav : 0 < _root_.BoseGases.a v)
    (hμ : 0 < μ) (hρ : 0 < ρ) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT * bogC2 v ρ μ
      = (1 / 2) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) * Real.sqrt (μ / ρ) := by
  rw [bogC2_eq v ρ μ hav hμ hρ]
  have hcomm : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
      = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl := by ring
  have h' : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)
      = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) := by
    rw [hcomm]; exact eT_dsKl_inv v μ hD0
  calc (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        * ((1 / 2) * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ * Real.sqrt (μ / ρ))
      = (1 / 2) * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)) * Real.sqrt (μ / ρ) := by
        ring
    _ = (1 / 2) * (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) * Real.sqrt (μ / ρ) := by rw [h']

/-- **The three logarithmic rows of `FsI1Regime` at the honest kernel.**

`hEpsLogT`, `hEpsTlog` and `hTtail` for `K = bogKernel v R ρ μ`,
`ε = lhyEps (a v) R ε_T K_ℓ s d μ`, `c₁ = bogC1 v ρ μ`, `c₂ = bogC2 v ρ μ`.

Route.  `Work.BoseBogFS.core_bounds` gives `Core v R μ ρ`; put `D = dil v μ`, `L = log D^{-1}`,
`B = D^{1/1292}`, so `B ≤ 1/1024` (`Core.hDs`), `L ≥ 8955` (since `D ≤ 2^{-12920}`),
`ε = lhyEpsX ≥ B(1+(156/323)L)` (`Core.hE3`), `ε ≥ B²(1+(162/323)L)` (`Core.hE2`),
`T = max 0 (bogT)` with `Core.hTpos` collapsing the `max 0`, and
`T = 10⁶(1+L)/ε` exactly (`Core.hTdef`).

* **`hEpsLogT`**: `c₁ + ε_Tc₂ = ½(B² + B)√(μ/ρ) ≤ 2B` by `Work.BoseBogFS.bogC1_eq`,
  `Work.BoseBogFS.bogC2_eq`, `Work.BoseBogFS.sKl_inv`, `Work.BoseBogFS.eT_dsKl_inv`
  and `Core.hρsqrt` (`√(μ/ρ) ≤ 2`).  Next, `log T = log 10⁶ + log(1+L) - log ε ≤
  13.8 + 1.2 + (1/1292)L`: bound `log(1+L) - log(1+(156/323)L) ≤ 1.2` by
  `Real.log_le_sub_one_of_pos` on `(1+L)/(1+(156/323)L)` (whose excess over `1` is at
  most `1/0.483`), and `-log ε ≤ -log B = (1/1292)L` by `Core.hE3` + `Real.log_rpow`.
  Hence `(c₁+ε_Tc₂)log T ≤ 2B(15 + 0.001L) ≤ B(1 + 0.483L) ≤ ε` — true because
  `L ≥ 8955` gives `30 + 0.002L ≤ 1 + 0.483L`.  **Do not use the crude
  `log(1+L) ≤ L`**: it is fatal here (the `L`-rates must match).
* **`hEpsTlog`**: write `T = 10⁶(1+L)/ε`, so `log T/T = log T·ε/(10⁶(1+L))` and
  `log T/(1+L) ≤ 15` (`log(1+L) ≤ L` and `-log ε ≤ (1/1292)L`); with
  `K.B ≤ 100` (`ηT ≤ 1`, as in `Work.BoseBogFS.honestFsEtaT`) the row is
  `(K.B+8π)²·15·ε/10⁶ ≤ ε` since `2660·15/10⁶ ≤ 1`.
* **`hTtail`**: `4π(8π)³/(2T) = 0.0997·ε/(1+L) ≤ ε` — again use `T = 10⁶(1+L)/ε`. -/
theorem honestFsLogRows {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ ρ : ℝ,
      Work.BoseBoxFock.CloseCondFS v μ ρ →
      (Work.BoseBogFS.bogC1 v ρ μ
            + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              * Work.BoseBogFS.bogC2 v ρ μ)
          * Real.log (Work.BoseBogFS.bogKernel v R ρ μ).T
          ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ ∧
      ((Work.BoseBogFS.bogKernel v R ρ μ).B + 8 * Real.pi) ^ 2
          * Real.log (Work.BoseBogFS.bogKernel v R ρ μ).T
          / (Work.BoseBogFS.bogKernel v R ρ μ).T
          ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ ∧
      4 * Real.pi * (8 * Real.pi) ^ 3 / (2 * (Work.BoseBogFS.bogKernel v R ρ μ).T)
          ≤ Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  -- the threshold is `min (coreBound v R) ε₁`, `ε₁` being `honestFsEtaT`'s threshold
  obtain ⟨ε₁, hε₁pos, hε₁⟩ := honestFsEtaT hR hav
  refine ⟨min (coreBound v R) ε₁, lt_min (coreBound_pos hR hav) hε₁pos, ?_⟩
  intro μ hAdm ρ hclose
  have hμ : 0 < μ := hAdm.1
  have hDε : Work.BoseFixR.dil v μ ≤ min (coreBound v R) ε₁ := hAdm.2.1
  -- the shared parameter bounds, and FS's error as `lhyEpsX`
  have hCore : Core v R μ ρ :=
    core_bounds (δ := min (coreBound v R) ε₁) hR hav (min_le_left _ _) μ ρ hμ hDε hclose
  rw [hCore.hEeq]
  -- the kernel-size row `ηT ≤ 1` at the honest parameters
  have hEtaT : (bogKernel v R ρ μ).η * (bogKernel v R ρ μ).T ≤ 1 :=
    (hε₁ μ ⟨hμ, le_trans hDε (min_le_right _ _), hAdm.2.2⟩ ρ hclose).1
  -- `B = D^{1/1292} ∈ (0,1]`, `L ≥ 231`, `ε > 0`
  have hBB0 : 0 < (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) :=
    Real.rpow_pos_of_pos hCore.hD0 _
  have hBB1 : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) ≤ 1 :=
    Real.rpow_le_one hCore.hD0.le hCore.hD1 (by norm_num)
  have hLbig : 231 ≤ bogL v μ := by
    have h := bogL_ge hCore.hD0 hCore.hDs
    simpa [bogL] using h
  have hepspos : 0 < lhyEpsX v R μ :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hCore.hD0 _) hCore.hE1
  -- `log T ≤ 56 + (1/1292)L` from `T = 10⁶(1+L)/ε` and `ε ≥ B(1+(156/323)L)`
  have hlogT : Real.log (bogT v R μ) ≤ 56 + (1 / 1292) * bogL v μ := by
    rw [hCore.hTdef]
    exact logBogTBound (D := Work.BoseFixR.dil v μ) (L := bogL v μ) (eps := lhyEpsX v R μ)
      hCore.hD0 hCore.hL1 rfl hepspos hCore.hE3
  -- collapse the `max 0` in the kernel's `T`
  have hTmax : (bogKernel v R ρ μ).T = bogT v R μ := by
    rw [bogKernel_T, max_eq_right hCore.hTpos.le]
  have hlogT' : Real.log (bogKernel v R ρ μ).T ≤ 56 + (1 / 1292) * bogL v μ := by
    rw [hTmax]; exact hlogT
  have hKpos : 0 < (bogKernel v R ρ μ).T := by rw [hTmax]; exact hCore.hTpos
  have hTdef' : (bogKernel v R ρ μ).T = 10 ^ 6 * (1 + bogL v μ) / lhyEpsX v R μ := by
    rw [hTmax]; exact hCore.hTdef
  -- `(D^{1/1292})² = D^{1/646}`
  have hBBsq : ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)) ^ 2
      = (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646) := by
    rw [← Real.rpow_natCast ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)) 2,
      ← Real.rpow_mul hCore.hD0.le]
    norm_num
  -- the monomial form `c₁ + ε_Tc₂ = ½(B²+B)√(μ/ρ)`
  have hval : bogC1 v ρ μ + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT * bogC2 v ρ μ
      = (1 / 2) * (((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)) ^ 2
          + (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)) * Real.sqrt (μ / ρ) := by
    rw [bogC1_val v ρ μ hav hCore.hμ hCore.hρ0,
      eT_mul_bogC2_val v ρ μ hCore.hD0 hav hCore.hμ hCore.hρ0, hBBsq]
    ring
  refine ⟨?_, ?_, ?_⟩
  · exact row1Arith hBB0.le hBB1 hCore.hL0 hLbig hepspos (Real.sqrt_nonneg _) hCore.hρsqrt
      hval hlogT' hCore.hE3
  · exact row2Arith (T := (bogKernel v R ρ μ).T) (B := (bogKernel v R ρ μ).B)
      (η := (bogKernel v R ρ μ).η) (L := bogL v μ) (eps := lhyEpsX v R μ)
      hKpos hepspos (bogKernel v R ρ μ).ηnn hCore.hL1 hTdef' hEtaT rfl hlogT'
  · exact row3Arith (T := (bogKernel v R ρ μ).T) (L := bogL v μ) (eps := lhyEpsX v R μ)
      hKpos hepspos hCore.hL0 hTdef'

end Work.BoseBogFS
