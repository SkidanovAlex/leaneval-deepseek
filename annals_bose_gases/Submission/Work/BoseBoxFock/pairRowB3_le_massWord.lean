import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.PB3FirstHalf
import Submission.Work.BoseBoxFock.PB3Shape
import Submission.Work.BoseBoxFock.chat_W1fun_zero_bounds
import Submission.Work.BoseBoxFock.exists_fderiv_chiScale_bound_inv
import Submission.Work.BoseBoxFock.pb3_deficit_uniform
import Submission.Work.BoseBoxFock.pb3_row_arith
import Submission.Work.BoseBoxFock.pinDirChi_le_kinFormB_uniform
import Submission.Work.BoseBoxFock.secondSlotSum_re_eq
import Submission.Work.BoseBoxFock.sum_limSlotForm_eq_q2MassChi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

local notation "xR3" => EuclideanSpace ℝ (Fin 3)

/-- `boxPow` is the corpus box `abox` (for a positive side). -/
private theorem pb3_boxPow_eq_abox (N : ℕ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Work.MB.boxPow N ℓ = Submission.BoseGases.abox N ℓ := by
  rw [Work.MB.boxPow, Submission.BoseGases.abox_eq_pi_acube]
  exact Set.pi_congr rfl fun i _ => corpusBox_boxL_eq_acube hℓ

/-- **The block-III row splits into its two slot sums.**  `pairRowB3` is the real combination
`α • (pinned pair sum) − β • (second slot sum)`; taking real parts. -/
theorem pb3_pairRowB3_re_split {n : ℕ} {v : xR3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} (N : ℕ)
    (c : ℂ) (Θ : Work.BoseDict.Xn n → ℂ) :
    (Work.BoseBoxFock.pairRowB3 v h μ N c Θ).re
      = (((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0
          + ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹
            * Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ)) 0)
        * (Work.BoseBoxFock.b3PairSum Θ (Work.BoseBoxFock.pinCond v μ c)
            (Work.BoseBoxFock.pinCond v μ c)
            (Work.BoseBoxFock.K1exp v μ N (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ)))).re
      - (μ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0)
        * (∑ j : Fin n, ∫ x : Work.BoseDict.Xn n, ∫ y : xR3,
            (starRingEnd ℂ) (Θ x)
              * Work.BoseBoxFock.K1exp v μ N (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ)) (x j) y
              * Θ (Function.update x j y)).re := by
  rw [Work.BoseBoxFock.pairRowB3, Complex.sub_re]
  simp only [Complex.smul_re, smul_eq_mul, Work.BoseBoxFock.b3PairSum, starRingEnd_apply]

/-- **The pinned pair sum is dominated by the mass word** (`PB3Shape` + `PB3FirstHalf`). -/
theorem pb3_b3PairSum_re_le {n : ℕ} {v : xR3 → ℝ} {μ : ℝ} {c : ℂ} (N : ℕ)
    (hc : (starRingEnd ℂ) c * c = (((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ : ℝ))
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))} :
    (Work.BoseBoxFock.b3PairSum
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
          (Φ : Submission.BoseGases.X n → ℝ))
        (Work.BoseBoxFock.pinCond v μ c) (Work.BoseBoxFock.pinCond v μ c)
        (Work.BoseBoxFock.K1exp v μ N (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ)))).re
      ≤ Work.BoseBoxFock.n0MassWord (Work.BoseBoxFock.ellH v μ)
          (Φ : Submission.BoseGases.X n → ℝ) := by
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  obtain ⟨hm, C, hC⟩ :=
    Work.BoseBoxFock.K1exp_meas_bdd (v := v) (μ := μ) (N := N)
      (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ))
  obtain ⟨CΘ, -, hCΘ⟩ := Work.BoseBoxFock.boxRestrictC_bound' hℓ hΦc
  have hsupp : Function.support (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
      (Φ : Submission.BoseGases.X n → ℝ)) ⊆ Work.MB.boxPow n (Work.BoseBoxFock.ellH v μ) := by
    rw [pb3_boxPow_eq_abox n hℓ]
    exact Work.BoseBoxFock.boxRestrictC_support' _ _
  rw [Work.BoseBoxFock.PB3Shape (v := v) (μ := μ) (c := c) hc
    (Work.BoseBoxFock.boxRestrictC_measurable' _ hΦc) ⟨CΘ, hCΘ⟩ hsupp
    (Work.BoseBoxFock.K1exp v μ N (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ))) hm ⟨C, hC⟩]
  exact Work.BoseBoxFock.PB3FirstHalf (v := v) (μ := μ) (Φ := Φ) N

/-- **The mass word at the box side, in the split form** of `pairRowB3`. -/
theorem pb3_rowMassWord_eq {n : ℕ} {v : xR3 → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    {Φ : Submission.BoseGases.X n → ℝ} :
    Work.BoseBoxFock.rowMassWord v h μ (Work.BoseBoxFock.ellH v μ) Φ
      = (((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0
          + ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹
            * Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ)) 0)
        * Work.BoseBoxFock.n0MassWord (Work.BoseBoxFock.ellH v μ) Φ
      - (μ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0)
        * Submission.BoseGases.q2MassChi (N := n) (Work.BoseBoxFock.ellH v μ) (Φ := Φ) := by
  simp only [Work.BoseBoxFock.rowMassWord, Work.BoseFixR.W1fun, Work.BoseFixR.W1omegaFun]
  ring

/-- **`a·μ ≤ 1`** for the diluteness chosen below. -/
theorem pb3_mu_a_le_one {v : xR3 → ℝ} {ε₀ μ : ℝ} (hav : 0 < BoseGases.a v)
    (hε₀ : ε₀ ≤ (BoseGases.a v) ^ 2) (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) :
    BoseGases.a v * μ ≤ 1 := by
  have h1 : μ * (BoseGases.a v) ^ 3 ≤ (BoseGases.a v) ^ 2 := le_trans hAdm.2.1 hε₀
  have h2 : BoseGases.a v * (μ * BoseGases.a v) ≤ BoseGases.a v * 1 := by nlinarith [h1]
  have h3 : μ * BoseGases.a v ≤ 1 := le_of_mul_le_mul_left h2 hav
  linarith [h3]

/-- **The allowance comparison**: the `X = √(dil)·K_ℓ^{-3}` multiple of `μ²·a·ℓ³` is dominated by
`errKafz v R μ 1` (the other three bracket terms of `errKafz` being nonnegative). -/
theorem pb3_errKafz_ge {v : xR3 → ℝ} {R μ : ℝ} (hav : 0 < BoseGases.a v) (hμ : 0 < μ) :
    μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3
        * (Real.sqrt (Work.BoseFixR.dil v μ)
            * (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ)))
      ≤ Work.BoseFixR.errKafz v R μ 1 := by
  have hℓE : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [Work.BoseBoxFock.ellH, if_pos (Work.BoseBox.sideAt_pos hμ hav)]
  have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have hkl : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ)) := by
    change 0 ≤ Work.BoseBox.fsXp (μ * (BoseGases.a v) ^ 3) (-(3 / 2) : ℝ) ^ (-(3 : ℝ))
    exact (Real.rpow_pos_of_pos (Work.BoseBox.fsXp_pos ht) _).le
  have hdil : 0 ≤ Work.BoseFixR.dil v μ := by rw [Work.BoseFixR.dil]; positivity
  have hfsX : 0 ≤ (Work.BoseFixR.fsX v μ) ^ 2 := sq_nonneg _
  have hth : 0 ≤ (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ) :=
    mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have herr : 0 ≤ Work.BoseFixR.errExp v μ := by
    rw [Work.BoseFixR.errExp]; exact Real.rpow_nonneg hdil _
  rw [Work.BoseFixR.errKafz, Work.BoseFixR.ell3, Work.BoseFixR.ell, ← hℓE]
  have hS : (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ))
      ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ))
        + (Work.BoseFixR.fsX v μ) ^ 2
        + (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)
        + Work.BoseFixR.errExp v μ := by linarith [hfsX, hth, herr]
  have h0 : 0 ≤ 1 * μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3
      * Real.sqrt (Work.BoseFixR.dil v μ) := by
    rw [one_mul]
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le)
      (pow_nonneg (Work.BoseBoxFock.ellH_pos v μ).le 3)) (Real.sqrt_nonneg _)
  calc μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3
        * (Real.sqrt (Work.BoseFixR.dil v μ)
            * (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ)))
      = 1 * μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3
        * Real.sqrt (Work.BoseFixR.dil v μ)
        * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ))) := by ring
    _ ≤ 1 * μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3
        * Real.sqrt (Work.BoseFixR.dil v μ)
        * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ))
          + (Work.BoseFixR.fsX v μ) ^ 2
          + (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)
          + Work.BoseFixR.errExp v μ) := by
          exact mul_le_mul_of_nonneg_left hS h0

/-- **The block-III row comparison** `pairRowB3 ≤ rowMassWord + ½·errKafz·‖Φ‖²`. -/
theorem pairRowB3_le_massWord (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
          (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
          0 < Work.BoseBoxFix.normB v μ n Φ →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
            (Φ : Submission.BoseGases.X n → ℝ) →
          ∀ (N : ℕ), Nmin μ ≤ N → ∀ (c : ℂ),
            (starRingEnd ℂ) c * c = ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ →
            (starRingEnd ℂ) c = c →
            (Work.BoseBoxFock.pairRowB3 v h μ N c
                (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)).re
              ≤ Work.BoseBoxFock.rowMassWord v h μ (Work.BoseBoxFock.ellH v μ)
                  (Φ : Submission.BoseGases.X n → ℝ)
                + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ := by
  classical
  -- the four ingredient constants
  obtain ⟨Cw, hCw0, hCw⟩ := chat_W1fun_zero_bounds v h hv hvrad hR hv_supp hav
  obtain ⟨εR, hεRpos, hεR⟩ := Work.BoseFixB2.DvApriori.exists_adm_chiR0_ge v hav hR
  obtain ⟨εK, CK, hεKpos, hCK0, hεK⟩ := kinFormB_le_of_isLowB v h hv hv1 hvrad hR hv_supp hav
  obtain ⟨M, hM0, hMder⟩ := exists_fderiv_chiScale_bound_inv
  -- the diluteness and the deficit constant
  set ε₀ : ℝ := min εR (min εK (min ((BoseGases.a v) ^ 2) 1)) with hε₀def
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    exact lt_min hεRpos (lt_min hεKpos (lt_min (pow_pos hav 2) one_pos))
  have hε₀R : ε₀ ≤ εR := by rw [hε₀def]; exact min_le_left _ _
  have hε₀K : ε₀ ≤ εK := by
    rw [hε₀def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₀a : ε₀ ≤ (BoseGases.a v) ^ 2 := by
    rw [hε₀def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε₀1 : ε₀ ≤ 1 := by
    rw [hε₀def]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  set Cd : ℝ := max 2 (6 * M ^ 2 / (2 * Real.pi) ^ 2) with hCddef
  have hCd0 : 0 ≤ Cd := by
    rw [hCddef]; exact le_trans (by norm_num : (0 : ℝ) ≤ 2) (le_max_left _ _)
  -- the per-`μ` threshold statement
  have hmain : ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
          (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
          0 < Work.BoseBoxFix.normB v μ n Φ →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
            (Φ : Submission.BoseGases.X n → ℝ) →
          ∀ (N : ℕ), N₀ ≤ N → ∀ (c : ℂ),
            (starRingEnd ℂ) c * c = ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ →
            (starRingEnd ℂ) c = c →
            (Work.BoseBoxFock.pairRowB3 v h μ N c
                (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)).re
              ≤ Work.BoseBoxFock.rowMassWord v h μ (Work.BoseBoxFock.ellH v μ)
                  (Φ : Submission.BoseGases.X n → ℝ)
                + (1 / 2) * Work.BoseFixR.errKafz v R μ 1 * Work.BoseBoxFix.normB v μ n Φ := by
    intro μ hAdm hJ
    have hμ : 0 < μ := hAdm.1
    have hℓpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) :=
      Work.BoseBox.sideAt_pos hμ hav
    have hℓE : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
      rw [Work.BoseBoxFock.ellH, if_pos hℓpos]
    have hAdmR : Work.BoseBoxFix.Adm v εR μ := ⟨hAdm.1, le_trans hAdm.2.1 hε₀R, hAdm.2.2⟩
    have hAdmK : Work.BoseBoxFix.Adm v εK μ := ⟨hAdm.1, le_trans hAdm.2.1 hε₀K, hAdm.2.2⟩
    have hRℓ : R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 := by
      rw [hℓE]; exact hεR μ hAdmR
    have haμ1 : BoseGases.a v * μ ≤ 1 := pb3_mu_a_le_one hav hε₀a hAdm
    -- the parameter positivity of FS's choice
    have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
    have ht1 : μ * (BoseGases.a v) ^ 3 ≤ 1 := le_trans hAdm.2.1 hε₀1
    have hd : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).d := by
      change 0 < Work.BoseBox.fsXp (μ * (BoseGases.a v) ^ 3) (6 : ℝ)
      exact Work.BoseBox.fsXp_pos ht
    have hs : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).s := by
      change 0 < Work.BoseBox.fsXp (μ * (BoseGases.a v) ^ 3) (1 : ℝ)
      exact Work.BoseBox.fsXp_pos ht
    have hb : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).b := by
      change 0 ≤ Work.BoseBox.bValue
      rw [Work.BoseBox.bValue]; norm_num
    have hεT0 : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT := by
      change 0 ≤ Work.BoseBox.fsXp (μ * (BoseGases.a v) ^ 3) (23 / 4 : ℝ)
      exact (Work.BoseBox.fsXp_pos ht).le
    have hεT1 : (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT ≤ 1 := by
      change Work.BoseBox.fsXp (μ * (BoseGases.a v) ^ 3) (23 / 4 : ℝ) ≤ 1
      exact Work.BoseBox.fsXp_le_one ht ht1 (by norm_num)
    obtain ⟨Cp, hCppos, hCp⟩ :=
      pinDirChi_le_kinFormB_uniform (v := v) (h := h) (μ := μ) hav hμ hd hs hb hεT0 hεT1
    have hCp0 : 0 ≤ Cp := hCppos.le
    -- the payer scaling
    set X : ℝ := Real.sqrt (Work.BoseFixR.dil v μ)
        * (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ)) with hXdef
    have hXpos : 0 < X := by
      rw [hXdef]
      refine mul_pos (Real.sqrt_pos.mpr ?_) ?_
      · rw [Work.BoseFixR.dil]; positivity
      · change 0 < Work.BoseBox.fsXp (μ * (BoseGases.a v) ^ 3) (-(3 / 2) : ℝ) ^ (-(3 : ℝ))
        exact Real.rpow_pos_of_pos (Work.BoseBox.fsXp_pos ht) _
    -- the threshold
    let N₀ : ℕ := max 1 ⌈max (Real.sqrt (4 * Cw * Cd * Cp * (CK + 2)
          * (Work.BoseBoxFock.ellH v μ) ^ 2 / X)) (Real.sqrt (8 * Cw * Cd / X))⌉₊
    refine ⟨N₀, le_max_left 1 _, ?_⟩
    intro n Φ hn hnorm hlow hspec N hN c hc1 hc2
    have hN1 : 1 ≤ N := le_trans (le_max_left 1 _) hN
    -- the two threshold facts
    have hceil : max (Real.sqrt (4 * Cw * Cd * Cp * (CK + 2)
          * (Work.BoseBoxFock.ellH v μ) ^ 2 / X)) (Real.sqrt (8 * Cw * Cd / X)) ≤ (N : ℝ) := by
      have h1 : ⌈max (Real.sqrt (4 * Cw * Cd * Cp * (CK + 2)
            * (Work.BoseBoxFock.ellH v μ) ^ 2 / X)) (Real.sqrt (8 * Cw * Cd / X))⌉₊ ≤ N :=
        le_trans (le_max_right 1 _) hN
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
    have hN2 : 4 * Cw * Cd * Cp * (CK + 2) * (Work.BoseBoxFock.ellH v μ) ^ 2 / X
        ≤ (N : ℝ) ^ 2 := by
      have h1 : Real.sqrt (4 * Cw * Cd * Cp * (CK + 2) * (Work.BoseBoxFock.ellH v μ) ^ 2 / X)
          ≤ (N : ℝ) := le_trans (le_max_left _ _) hceil
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rwa [Real.sq_sqrt (by positivity)] at h2
    have hN3 : 8 * Cw * Cd / X ≤ (N : ℝ) ^ 2 := by
      have h1 : Real.sqrt (8 * Cw * Cd / X) ≤ (N : ℝ) := le_trans (le_max_right _ _) hceil
      have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      rwa [Real.sq_sqrt (by positivity)] at h2
    -- the two state payers
    have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
    have hkinB := hεK J μ hAdmK hJ n Φ (by simpa only [hℓE] using hn) hnorm hlow
    have hkin' : Work.BoseKinLoc.kinFormB n (Work.BoseBoxFock.ellH v μ)
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
          (Φ : Submission.BoseGases.X n → ℝ)
        ≤ CK * BoseGases.a v * μ ^ 2 * (Work.BoseBoxFock.ellH v μ) ^ 3
            * Work.BoseBoxFix.normB v μ n Φ := by
      simpa only [hℓE] using hkinB
    have hpin' : Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ)
          (fun x => (((Φ : Submission.BoseGases.X n → ℝ) x : ℝ) : ℂ))
        ≤ Cp * (Work.BoseKinLoc.kinFormB n (Work.BoseBoxFock.ellH v μ)
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
              (Φ : Submission.BoseGases.X n → ℝ)
            + (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ) := by
      rw [hℓE]
      exact hCp n Φ
    -- the two real coefficients of the row
    have hα0 : 0 ≤ ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0
          + ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹
            * Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ)) 0 := by
      have h1 := (hCw (Work.BoseBoxFock.ellH v μ) (Work.BoseBoxFock.ellH_pos v μ) hRℓ)
      have h2 : (0 : ℝ) < ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ :=
        inv_pos.mpr (pow_pos (Work.BoseBoxFock.ellH_pos v μ) 3)
      exact add_nonneg (mul_nonneg h2.le h1.1) (mul_nonneg h2.le h1.2.2)
    have hβ0 : 0 ≤ μ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0 :=
      mul_nonneg hμ.le (hCw (Work.BoseBoxFock.ellH v μ) (Work.BoseBoxFock.ellH_pos v μ) hRℓ).1
    have hβle : μ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0
        ≤ μ * Cw * BoseGases.a v := by
      have h1 := (hCw (Work.BoseBoxFock.ellH v μ) (Work.BoseBoxFock.ellH_pos v μ) hRℓ).2.1
      have h := mul_le_mul_of_nonneg_left h1 hμ.le
      linarith [h]
    -- the deficit
    have hdef := pb3_deficit_uniform (v := v) (μ := μ) (M := M) hμ hav hM0 hMder
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) Φ.contDiff hnorm N hN1
    rw [← hCddef] at hdef
    -- the arithmetic
    have harith := pb3_row_arith (ℓ := Work.BoseBoxFock.ellH v μ) (X := X) (nv := (n : ℝ))
      (nb := Work.BoseBoxFix.normB v μ n Φ)
      (pin := Work.BoseBoxFock.pinDirChi (Work.BoseBoxFock.ellH v μ)
        (fun x => (((Φ : Submission.BoseGases.X n → ℝ) x : ℝ) : ℂ)))
      (kin := Work.BoseKinLoc.kinFormB n (Work.BoseBoxFock.ellH v μ)
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (BoseGases.a v)).b (Φ : Submission.BoseGases.X n → ℝ))
      (β := μ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0)
      (μv := μ) (av := BoseGases.a v) (Cw := Cw) (Cd := Cd) (Cp := Cp) (Ck := CK)
      hN1 (Work.BoseBoxFock.ellH_pos v μ) hXpos hnorm.le hCw0 hCd0 hCp0 hCK0 hav.le hμ.le haμ1
      (Nat.cast_nonneg n) (by simpa only [hℓE] using hn) hβ0 hβle
      (Work.BoseBoxFock.pinDirChi_nonneg _ _) hpin' hkin' hN2 hN3
    have herr := pb3_errKafz_ge (v := v) (R := R) (μ := μ) hav hμ
    have hnormBnn : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := hnorm.le
    have hfin : (1 / 2) * (μ ^ 2 * BoseGases.a v * (Work.BoseBoxFock.ellH v μ) ^ 3 * X)
          * Work.BoseBoxFix.normB v μ n Φ
        ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ 1 * Work.BoseBoxFix.normB v μ n Φ := by
      have h := mul_le_mul_of_nonneg_right herr hnormBnn
      linarith [h]
    -- the split of the row
    have hsplit := pb3_pairRowB3_re_split (v := v) (h := h) (μ := μ) N c
      (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
        (Φ : Submission.BoseGases.X n → ℝ))
    have hP := pb3_b3PairSum_re_le (v := v) (μ := μ) (c := c) N hc1 (Φ := Φ)
    have hS := secondSlotSum_re_eq (v := v) (μ := μ) (N := N) (Φ := Φ)
    have hlim := sum_limSlotForm_eq_q2MassChi (v := v) (μ := μ) (Φ := Φ)
    have hrow := pb3_rowMassWord_eq (v := v) h μ (Φ := Φ)
    -- the middle identity
    have hmid : (((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹
              * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0
            + ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹
              * Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ)) 0)
          * Work.BoseBoxFock.n0MassWord (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ)
        - (μ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0)
          * (∑ j : Fin n, Work.BoseBoxFock.frameSlotForm v μ N j
              (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                (Φ : Submission.BoseGases.X n → ℝ)))
        = Work.BoseBoxFock.rowMassWord v h μ (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ)
          + (μ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0)
            * ((∑ j : Fin n, Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
                  (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                    (Φ : Submission.BoseGases.X n → ℝ)))
              - (∑ j : Fin n, Work.BoseBoxFock.frameSlotForm v μ N j
                  (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                    (Φ : Submission.BoseGases.X n → ℝ)))) := by
      rw [hrow, hlim]
      ring
    calc (Work.BoseBoxFock.pairRowB3 v h μ N c
            (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ))).re
        = (((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹
              * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0
            + ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹
              * Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ)) 0)
          * (Work.BoseBoxFock.b3PairSum
              (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                (Φ : Submission.BoseGases.X n → ℝ))
              (Work.BoseBoxFock.pinCond v μ c) (Work.BoseBoxFock.pinCond v μ c)
              (Work.BoseBoxFock.K1exp v μ N (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ)))).re
          - (μ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0)
            * (∑ j : Fin n, ∫ x : Work.BoseDict.Xn n, ∫ y : xR3,
                (starRingEnd ℂ) (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                    (Φ : Submission.BoseGases.X n → ℝ) x)
                  * Work.BoseBoxFock.K1exp v μ N
                      (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ)) (x j) y
                  * Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                      (Φ : Submission.BoseGases.X n → ℝ)
                      (Function.update x j y)).re := hsplit
      _ ≤ (((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹
              * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0
            + ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹
              * Work.BoseFixR.chat (Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ)) 0)
          * Work.BoseBoxFock.n0MassWord (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ)
          - (μ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0)
            * (∑ j : Fin n, Work.BoseBoxFock.frameSlotForm v μ N j
                (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                  (Φ : Submission.BoseGases.X n → ℝ))) := by
          have h1 := mul_le_mul_of_nonneg_left hP hα0
          have h2 : (∑ j : Fin n, Work.BoseBoxFock.frameSlotForm v μ N j
                (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                  (Φ : Submission.BoseGases.X n → ℝ)))
              ≤ (∑ j : Fin n, ∫ x : Work.BoseDict.Xn n, ∫ y : xR3,
                  (starRingEnd ℂ) (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                      (Φ : Submission.BoseGases.X n → ℝ) x)
                    * Work.BoseBoxFock.K1exp v μ N
                        (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ)) (x j) y
                    * Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                        (Φ : Submission.BoseGases.X n → ℝ)
                        (Function.update x j y)).re := le_of_eq hS.symm
          have h3 := mul_le_mul_of_nonneg_left h2 hβ0
          linarith [h1, h3]
      _ = Work.BoseBoxFock.rowMassWord v h μ (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ)
          + (μ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0)
            * ((∑ j : Fin n, Work.BoseBoxFock.limSlotForm (Work.BoseBoxFock.ellH v μ) j
                  (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                    (Φ : Submission.BoseGases.X n → ℝ)))
              - (∑ j : Fin n, Work.BoseBoxFock.frameSlotForm v μ N j
                  (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                    (Φ : Submission.BoseGases.X n → ℝ)))) := hmid
      _ ≤ Work.BoseBoxFock.rowMassWord v h μ (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ)
          + (1 / 2) * Work.BoseFixR.errKafz v R μ 1 * Work.BoseBoxFix.normB v μ n Φ := by
          have h := mul_le_mul_of_nonneg_left hdef hβ0
          linarith [h, harith, hfin]
  -- assemble the existential
  refine ⟨fun μ => if hh : (Work.BoseBoxFix.Adm v ε₀ μ
        ∧ J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3)
      then Classical.choose (hmain μ hh.1 hh.2) else 1, ε₀, 1, hε₀pos, zero_le_one, ?_⟩
  intro μ hAdm hJ n Φ hn hnorm hlow hspec N hN c hc1 hc2
  have hh : Work.BoseBoxFix.Adm v ε₀ μ
      ∧ J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 := ⟨hAdm, hJ⟩
  have hN' : Classical.choose (hmain μ hh.1 hh.2) ≤ N := by
    simpa only [dif_pos hh] using hN
  exact (Classical.choose_spec (hmain μ hh.1 hh.2)).2 n Φ hn hnorm hlow hspec N hN' c hc1 hc2

end

end Work.BoseBoxFock
