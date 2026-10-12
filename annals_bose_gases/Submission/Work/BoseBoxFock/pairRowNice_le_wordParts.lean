import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.BoseBoxFock.K1lim_eq_qmqKCtheta_L1
import Submission.Work.BoseBoxFock.dict13_L1
import Submission.Work.BoseBoxFock.dictII_L1
import Submission.Work.BoseBoxFock.imagesWordLe
import Submission.Work.BoseBoxFock.pairRowB3_le_massWord
import Submission.Work.BoseBoxFock.qmqAssemblyAux
import Submission.Work.BoseBoxFock.qmqRowDict
import Submission.Work.BoseBoxFock.qmqRowKernelChain
import Submission.Work.BoseBoxFock.qmqWordK_add
import Submission.Work.ESYRound8.Dict.wScaled_even
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem pairRowNice_le_wordParts (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
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
            (Work.BoseBoxFock.rowPairSubC (((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹)
                (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
                (Work.BoseBoxFock.pinCond v μ c)
                (Work.BoseBoxFock.pairRowNice (Work.BoseBoxFock.ellH v μ)
                  (fun x => Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x
                    + Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ) x))
                (Work.BoseBoxFock.pairRowNice (Work.BoseBoxFock.ellH v μ)
                  (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
              + Work.BoseBoxFock.pairRowB3 v h μ N c
                  (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)).re
              ≤ Work.BoseBoxFock.rowWordPartsH v h μ Φ
                + (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ := by
  classical
  -- ## 0. the children
  obtain ⟨ε₀s, Cs, hεs, hCs, hstrip⟩ :=
    stripImages_cost_le v h hv hv1 hvrad hR hv_supp hav fc fu J hB3
  obtain ⟨ε₀i, Ci, hεi, hCi, himg⟩ :=
    imagesWordLe v h hv hv1 hvrad hR hv_supp hav fc fu J hB3
  obtain ⟨NminB, ε₀B, CB, hεB, hCB, hB3m⟩ :=
    pairRowB3_le_massWord v h hv hv1 hvrad hR hv_supp hav fc fu J hB3
  -- ## 1. the diluteness régime data
  obtain ⟨chiC, hchiC0, rchi, hrchi, hchiT⟩ := Submission.BoseGases.conv3chi_second_order_bound
  set rm : ℝ := (Real.sqrt (2 * chiC + 1))⁻¹ with hrmdef
  have hrmpos : 0 < rm := by
    rw [hrmdef]; exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  set rr : ℝ := min (1 / 4) (min rchi rm) with hrrdef
  have hrrpos : 0 < rr := lt_min (by norm_num) (lt_min hrchi hrmpos)
  have hrr4 : rr ≤ 1 / 4 := min_le_left _ _
  have hrrr : rr ≤ rchi := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrrm : rr ≤ rm := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨ε_R, hε_Rpos, _hε_Rle1, hε_R⟩ := exists_threshold_sideAt_ge_mul (v := v) hav hR hrrpos
  refine ⟨NminB, min ε_R (min ε₀i (min ε₀s ε₀B)), Cs + (Ci + CB),
    lt_min hε_Rpos (lt_min hεi (lt_min hεs hεB)), by positivity, ?_⟩
  intro μ hAdm hJ n Φ hn hnorm hlow hspec N hN c hc hr
  -- ## 2. the admissibilities
  have hAdm_i : Work.BoseBoxFix.Adm v ε₀i μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (le_trans (min_le_right _ _) (min_le_left _ _)), hAdm.2.2⟩
  have hAdm_s : Work.BoseBoxFix.Adm v ε₀s μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))), hAdm.2.2⟩
  have hAdm_B : Work.BoseBoxFix.Adm v ε₀B μ :=
    ⟨hAdm.1, le_trans hAdm.2.1 (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))), hAdm.2.2⟩
  have hμ : 0 < μ := hAdm.1
  have hsidepos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  -- ## 3. the box side
  set ℓ : ℝ := Work.BoseBoxFock.ellH v μ with hℓeq
  have hℓrw : Work.BoseBoxFock.ellH v μ = ℓ := hℓeq.symm
  have hℓpos : 0 < ℓ := by rw [hℓeq]; exact Work.BoseBoxFock.ellH_pos v μ
  have hℓside : ℓ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [hℓeq]; exact pairRow_ellH_eq_sideAt hsidepos
  -- the children are stated at `ellH v μ` and take `c` in that form
  have hc_orig : (starRingEnd ℂ) c * c = ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ := by
    rw [hℓrw]; exact hc
  -- ## 4. the two honest weights
  set W₂ : ℝ³ → ℝ := Work.BoseFixR.W1fun v h ℓ with hW₂def
  set W₁ : ℝ³ → ℝ := fun x => Work.BoseFixR.W1fun v h ℓ x + Work.BoseFixR.W1omegaFun v h ℓ x
    with hW₁def
  -- ## 5. the régime at `ℓ`
  have hleR : μ * BoseGases.a v ^ 3 ≤ ε_R := le_trans hAdm.2.1 (min_le_left _ _)
  have hRrr : R ≤ ℓ * rr := by
    rw [hℓside]; exact hε_R μ hμ hleR
  have hRdiv : R / ℓ ≤ rr := by
    rw [div_le_iff₀ hℓpos, mul_comm]; exact hRrr
  have hreg : R / ℓ ≤ rchi := le_trans hRdiv hrrr
  have hcond : chiC * (R / ℓ) ^ 2 ≤ 1 / 2 := by
    have hRl0 : 0 ≤ R / ℓ := by positivity
    have h1 : R / ℓ ≤ rm := le_trans hRdiv hrrm
    have hsq : (R / ℓ) ^ 2 ≤ rm ^ 2 := by
      have hmul := mul_le_mul h1 h1 hRl0 hrmpos.le
      simpa [pow_two] using hmul
    have hrsq : chiC * rm ^ 2 ≤ 1 / 2 := by
      have h1 : rm ^ 2 = (2 * chiC + 1)⁻¹ := by
        rw [hrmdef, inv_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * chiC + 1)]
      rw [h1, mul_inv_le_iff₀ (by linarith : (0 : ℝ) < 2 * chiC + 1)]
      linarith
    calc chiC * (R / ℓ) ^ 2 ≤ chiC * rm ^ 2 := mul_le_mul_of_nonneg_left hsq hchiC0
      _ ≤ 1 / 2 := hrsq
  -- ## 6. the weight facts
  obtain ⟨hW1i, _hW1nn, hW1s⟩ := W1fun_integrable_of_regime (v := v) (h := h) (R := R) (ℓ := ℓ)
    (r₁ := rchi) (C := chiC) hR hv hvrad hv_supp hchiC0 hrchi hchiT hℓpos hreg hcond
  obtain ⟨hW2i, _hW2nn, hW2s, hW2e, _hW2J, _hWsumJ⟩ := W1omega_weight_facts (v := v) (h := h)
    (R := R) (ℓ := ℓ) (r₁ := rchi) (C := chiC) hR hv hvrad hv_supp hchiC0 hrchi hchiT hℓpos hreg hcond
  have hW₁i : MeasureTheory.Integrable W₁ := by
    rw [hW₁def]; exact hW1i.add hW2i
  have hW₂i : MeasureTheory.Integrable W₂ := hW1i
  have hW₁s : ∀ x : ℝ³, R ≤ ‖x‖ → W₁ x = 0 := by
    intro x hx; rw [hW₁def]; simp [hW1s x hx, hW2s x hx]
  have hW₂s : ∀ x : ℝ³, R ≤ ‖x‖ → W₂ x = 0 := fun x hx => hW1s x hx
  have hW1e : ∀ x : ℝ³, Work.BoseFixR.W1fun v h ℓ (-x) = Work.BoseFixR.W1fun v h ℓ x := by
    intro x
    rw [W1fun_eq_wScaled]
    exact Work.ESYRound8.Dict.wScaled_even (Submission.BoseGases.g0_even hvrad h) ℓ x
  have hW₁e : ∀ x : ℝ³, W₁ (-x) = W₁ x := by
    intro x
    rw [hW₁def]
    simp only [Pi.add_apply]
    rw [hW1e x, hW2e x]
  have hW₂e : ∀ x : ℝ³, W₂ (-x) = W₂ x := by
    intro x; rw [hW₂def]; exact hW1e x
  have hW₁eq : W₁ = Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g2 v h) := by
    rw [hW₁def]; exact W1fun_add_W1omegaFun_fun
  have hW₂eq : W₂ = Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) := by
    rw [hW₂def]; exact W1fun_eq_wScaled v h ℓ
  have hW₁supp : Function.support W₁ ⊆ Metric.closedBall (0 : ℝ³) R := by
    intro x hx
    rw [Function.mem_support] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    exact hx (hW₁s x (le_of_lt (not_le.mp hcon)))
  have hW₁cs : HasCompactSupport W₁ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ³) R) hW₁supp
  have hW₂supp : Function.support W₂ ⊆ Metric.closedBall (0 : ℝ³) R := by
    intro x hx
    rw [Function.mem_support] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hcon
    exact hx (hW₂s x (le_of_lt (not_le.mp hcon)))
  have hW₂cs : HasCompactSupport W₂ :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ³) R) hW₂supp
  -- the normalisation of `c` in the form the dictionary lemmas use
  have hcd : (starRingEnd ℂ) c * c * ((ℓ ^ 3 : ℝ) : ℂ) = 1 := by
    rw [hc, ← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓpos)),
      Complex.ofReal_one]
  -- ## 7. the honest kernels and their integrability
  set k₁ : ℝ³ → ℝ³ → ℝ :=
    fun a b => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g2 v h) a b + imgKernel ℓ W₁ a b
    with hk₁def
  set k₂ : ℝ³ → ℝ³ → ℝ :=
    fun a b => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) a b + imgKernel ℓ W₂ a b
    with hk₂def
  obtain ⟨hIntA₁, hIntB₁⟩ := uncurry_pairImg_integrable (ℓ := ℓ) (R := R) hℓpos hW₁i hW₁s
  obtain ⟨hIntA₂, hIntB₂⟩ := uncurry_pairImg_integrable (ℓ := ℓ) (R := R) hℓpos hW₂i hW₂s
  have hIntP₁ : MeasureTheory.Integrable
      (Function.uncurry (fun a b => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g2 v h) a b))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hint := hIntA₁
    rw [show (fun a b : ℝ³ => Submission.BoseGases.chiScale ℓ a * W₁ (a - b)
          * Submission.BoseGases.chiScale ℓ b)
        = (fun a b : ℝ³ => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g2 v h) a b) from by
      funext a b
      rw [Submission.BoseGases.wPair, hW₁eq]] at hint
    exact hint
  have hIntP₂ : MeasureTheory.Integrable
      (Function.uncurry (fun a b => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) a b))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hint := hIntA₂
    rw [show (fun a b : ℝ³ => Submission.BoseGases.chiScale ℓ a * W₂ (a - b)
          * Submission.BoseGases.chiScale ℓ b)
        = (fun a b : ℝ³ => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) a b) from by
      funext a b
      rw [Submission.BoseGases.wPair, hW₂eq]] at hint
    exact hint
  have hk₁I : MeasureTheory.Integrable (Function.uncurry k₁)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    rw [hk₁def]; exact hIntP₁.add hIntB₁
  have hk₂I : MeasureTheory.Integrable (Function.uncurry k₂)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    rw [hk₂def]; exact hIntP₂.add hIntB₂
  -- ## 8. the kernel-value chain
  have hK₁per : K1lim ℓ W₁ = qmqKCθ ℓ (fun a b => ((ℓ ^ 3)⁻¹ : ℂ)
      * ((Submission.BoseGases.chiScale ℓ a : ℝ) : ℂ)
      * latPer3 ℓ W₁ (a - b)
      * ((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)) :=
    funext fun w => funext fun y =>
      K1lim_eq_qmqKCtheta_L1 (ℓ := ℓ) (R := R) hℓpos hW₁i hW₁cs hW₁e
        (fun z hz => hW₁s z hz.le) w y
  have hK₂per : K1lim ℓ W₂ = qmqKCθ ℓ (fun a b => ((ℓ ^ 3)⁻¹ : ℂ)
      * ((Submission.BoseGases.chiScale ℓ a : ℝ) : ℂ)
      * latPer3 ℓ W₂ (a - b)
      * ((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ)) :=
    funext fun w => funext fun y =>
      K1lim_eq_qmqKCtheta_L1 (ℓ := ℓ) (R := R) hℓpos hW₂i hW₂cs hW₂e
        (fun z hz => hW₂s z hz.le) w y
  have hm₁ : (fun a b => ((ℓ ^ 3)⁻¹ : ℂ) * ((Submission.BoseGases.chiScale ℓ a : ℝ) : ℂ)
        * latPer3 ℓ W₁ (a - b) * ((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ))
      = fun a b => ((Submission.BoseGases.wPair ℓ (Submission.BoseGases.g2 v h) a b
          + imgKernel ℓ W₁ a b : ℝ) : ℂ) := by
    funext a b
    have hsum1 : Summable (fun m : Fin 3 → ℤ =>
        ((Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g2 v h)
          (a - b + ℓ • latVec m) : ℝ) : ℂ)) :=
      summable_shift_of_support hℓpos
        (W := Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g2 v h))
        (fun x hx => by rw [← hW₁eq]; exact hW₁s x hx.le) (a - b)
    have hk := kPer_eq_wPair_add_img ℓ (Submission.BoseGases.g2 v h) a b (ne_of_gt hℓpos) hsum1
    rw [hW₁eq]
    push_cast
    exact hk
  have hm₂ : (fun a b => ((ℓ ^ 3)⁻¹ : ℂ) * ((Submission.BoseGases.chiScale ℓ a : ℝ) : ℂ)
        * latPer3 ℓ W₂ (a - b) * ((Submission.BoseGases.chiScale ℓ b : ℝ) : ℂ))
      = fun a b => ((Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) a b
          + imgKernel ℓ W₂ a b : ℝ) : ℂ) := by
    funext a b
    have hsum2 : Summable (fun m : Fin 3 → ℤ =>
        ((Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h)
          (a - b + ℓ • latVec m) : ℝ) : ℂ)) :=
      summable_shift_of_support hℓpos
        (W := Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h))
        (fun x hx => by rw [← hW₂eq]; exact hW₂s x hx.le) (a - b)
    have hk := kPer_eq_wPair_add_img ℓ (Submission.BoseGases.g0 v h) a b (ne_of_gt hℓpos) hsum2
    rw [hW₂eq]
    push_cast
    exact hk
  have hΘs : Function.support (boxRestrictC ℓ Φ) ⊆ Work.MB.boxPow n ℓ := by
    intro x hx
    have h1 := boxRestrictC_support_subset ℓ Φ hx
    rw [Submission.BoseGases.abox_eq_pi_acube] at h1
    rw [Work.MB.boxPow, boxL_eq_acube hℓpos]
    exact h1
  have hchain : rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
        (K1lim ℓ W₁) (K1lim ℓ W₂)
      = rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
          (qmqKernel ℓ k₁) (qmqKernel ℓ k₂) := by
    have hmain := rowPairSubC_K1lim_eq_qmqKernel (n := n) (ℓ := ℓ) (A := pinCond v μ c)
      hℓpos hΘs hK₁per hK₂per hm₁ hm₂
    rwa [show (fun a b => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g2 v h) a b
            + imgKernel ℓ W₁ a b) = k₁ from hk₁def.symm,
      show (fun a b => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) a b
            + imgKernel ℓ W₂ a b) = k₂ from hk₂def.symm] at hmain
  -- ## 9. the dictionary identities
  have hsym₁ : ∀ a b, k₁ a b = k₁ b a := by
    intro a b
    rw [hk₁def]
    beta_reduce
    rw [wPair_symm (Submission.BoseGases.g2_even hvrad h) a b, imgKernel_symm hW₁e a b]
  have hsym₂ : ∀ a b, k₂ a b = k₂ b a := by
    intro a b
    rw [hk₂def]
    beta_reduce
    rw [wPair_symm (Submission.BoseGases.g0_even hvrad h) a b, imgKernel_symm hW₂e a b]
  have hdict13 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ((ℓ ^ 3)⁻¹ : ℝ) * (rowShape13 (boxRestrictC ℓ Φ)
          (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
          (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y) (qmqKernel ℓ k₁) p).re
        = ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 (Φ : Submission.BoseGases.X n → ℝ)) x
              * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 (Φ : Submission.BoseGases.X n → ℝ)) x
              * k₁ (x p.1) (x p.2) := fun p hp =>
    dict13_L1 (ℓ := ℓ) hℓpos Φ.contDiff.continuous Φ.symm
      (MeasureTheory.Integrable.aestronglyMeasurable hk₁I) hk₁I hsym₁
      hcd hr (p := p) (mem_pairSet_iff.mp hp)
  have hdictII : ∀ p ∈ Submission.BoseGases.pairSet n,
      (1 / 2) * ((ℓ ^ 3)⁻¹ : ℝ) *
          ((rowShape21 (boxRestrictC ℓ Φ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
              (qmqKernel ℓ k₂) p).re
            + (rowShape23 (boxRestrictC ℓ Φ) (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y)
                (fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y) (qmqKernel ℓ k₂) p).re)
        = ∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 (Φ : Submission.BoseGases.X n → ℝ)) x
              * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 (Φ : Submission.BoseGases.X n → ℝ)) x
              * k₂ (x p.1) (x p.2) := fun p hp =>
    dictII_L1 (ℓ := ℓ) hℓpos Φ.contDiff.continuous Φ.symm
      (MeasureTheory.Integrable.aestronglyMeasurable hk₂I) hk₂I hsym₂
      hcd hr (p := p) (mem_pairSet_iff.mp hp)
  have hAc : pinCond v μ c = fun y => c * Work.BoseK15.corpusBox.thetaFun ℓ y := by
    rw [pinCond_congr hℓside.symm c]
    funext y
    rw [← hℓside]
  have hrow : (rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
        (qmqKernel ℓ k₁) (qmqKernel ℓ k₂)).re
      = q1WordK ℓ k₁ (Φ : Submission.BoseGases.X n → ℝ)
        + q4WordK ℓ k₂ (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [hAc]
    exact rowPairSubC_re_qmqKernel hdict13 hdictII
  -- ## 10. the word split
  have hwords : q1WordK ℓ k₁ (Φ : Submission.BoseGases.X n → ℝ)
        + q4WordK ℓ k₂ (Φ : Submission.BoseGases.X n → ℝ)
      = Submission.BoseGases.q1PairWord (ℓ := ℓ) (v := v) h
          (Φ := (Φ : Submission.BoseGases.X n → ℝ))
        + Submission.BoseGases.q4PairWord (ℓ := ℓ) (v := v) h
            (Φ := (Φ : Submission.BoseGases.X n → ℝ))
        + (q1WordK ℓ (imgKernel ℓ W₁) (Φ : Submission.BoseGases.X n → ℝ)
          + q4WordK ℓ (imgKernel ℓ W₂) (Φ : Submission.BoseGases.X n → ℝ)) := by
    have hsplit := qmqWordK_add (ℓ := ℓ) (Φ := (Φ : Submission.BoseGases.X n → ℝ))
      (k := fun a b => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g2 v h) a b)
      (κ := fun a b => imgKernel ℓ W₁ a b)
      (k' := fun a b => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) a b)
      (κ' := fun a b => imgKernel ℓ W₂ a b) Φ.contDiff.continuous hIntP₁ hIntB₁ hIntP₂ hIntB₂
    have hq1 : q1WordK ℓ (fun a b => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g2 v h) a b)
        (Φ : Submission.BoseGases.X n → ℝ)
        = Submission.BoseGases.q1PairWord (ℓ := ℓ) (v := v) h
            (Φ := (Φ : Submission.BoseGases.X n → ℝ)) :=
      (q1PairWord_eq_q1WordK ℓ h (Φ : Submission.BoseGases.X n → ℝ)).symm
    have hq4 : q4WordK ℓ (fun a b => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) a b)
        (Φ : Submission.BoseGases.X n → ℝ)
        = Submission.BoseGases.q4PairWord (ℓ := ℓ) (v := v) h
            (Φ := (Φ : Submission.BoseGases.X n → ℝ)) :=
      (q4PairWord_eq_q4WordK ℓ h (Φ : Submission.BoseGases.X n → ℝ)).symm
    rw [show q1WordK ℓ k₁ (Φ : Submission.BoseGases.X n → ℝ)
        = q1WordK ℓ (fun a b => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g2 v h) a b
            + imgKernel ℓ W₁ a b) (Φ : Submission.BoseGases.X n → ℝ) from by
      rw [hk₁def]]
    rw [show q4WordK ℓ k₂ (Φ : Submission.BoseGases.X n → ℝ)
        = q4WordK ℓ (fun a b => Submission.BoseGases.wPair ℓ (Submission.BoseGases.g0 v h) a b
            + imgKernel ℓ W₂ a b) (Φ : Submission.BoseGases.X n → ℝ) from by
      rw [hk₂def]]
    rw [hsplit, hq1, hq4]
    ring
  -- ## 11. the assembly
  have hstep0 : (rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
        (pairRowNice ℓ W₁) (pairRowNice ℓ W₂)
      + pairRowB3 v h μ N c (boxRestrictC ℓ Φ)).re
      ≤ (rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
          (K1lim ℓ W₁) (K1lim ℓ W₂)
        + pairRowB3 v h μ N c (boxRestrictC ℓ Φ)).re
        + (1 / 2) * Work.BoseFixR.errKafz v R μ Cs * Work.BoseBoxFix.normB v μ n Φ := by
    have h := hstrip μ hAdm_s hJ n Φ hn hnorm hlow hspec c hc_orig
    rw [hℓrw] at h
    rw [← hW₁def, ← hW₂def] at h
    have h1 : (rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
          (pairRowNice ℓ W₁) (pairRowNice ℓ W₂)).re
        ≤ (rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
            (K1lim ℓ W₁) (K1lim ℓ W₂)).re
          + (1 / 2) * Work.BoseFixR.errKafz v R μ Cs * Work.BoseBoxFix.normB v μ n Φ := by
      have h2 : (rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
            (pairRowNice ℓ W₁) (pairRowNice ℓ W₂)).re
          - (rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
            (K1lim ℓ W₁) (K1lim ℓ W₂)).re
          ≤ ‖rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
              (K1lim ℓ W₁) (K1lim ℓ W₂)
            - rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
              (pairRowNice ℓ W₁) (pairRowNice ℓ W₂)‖ := by
        have hcl := Complex.re_le_norm (rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
            (pairRowNice ℓ W₁) (pairRowNice ℓ W₂)
          - rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
            (K1lim ℓ W₁) (K1lim ℓ W₂))
        rw [Complex.sub_re, norm_sub_rev] at hcl
        exact hcl
      linarith [h2, h]
    rw [Complex.add_re, Complex.add_re]
    linarith [h1]
  have hstep1 : (rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
        (K1lim ℓ W₁) (K1lim ℓ W₂)
      + pairRowB3 v h μ N c (boxRestrictC ℓ Φ)).re
      = q1WordK ℓ k₁ (Φ : Submission.BoseGases.X n → ℝ)
        + q4WordK ℓ k₂ (Φ : Submission.BoseGases.X n → ℝ)
        + (pairRowB3 v h μ N c (boxRestrictC ℓ Φ)).re := by
    have h3 : (rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
          (K1lim ℓ W₁) (K1lim ℓ W₂)
        + pairRowB3 v h μ N c (boxRestrictC ℓ Φ)).re
        = (rowPairSubC ((ℓ ^ 3)⁻¹) (boxRestrictC ℓ Φ) (pinCond v μ c)
            (K1lim ℓ W₁) (K1lim ℓ W₂)).re
          + (pairRowB3 v h μ N c (boxRestrictC ℓ Φ)).re := Complex.add_re _ _
    rw [h3, hchain, hrow]
  have hstep2 : q1WordK ℓ k₁ (Φ : Submission.BoseGases.X n → ℝ)
        + q4WordK ℓ k₂ (Φ : Submission.BoseGases.X n → ℝ)
        + (pairRowB3 v h μ N c (boxRestrictC ℓ Φ)).re
      ≤ rowWordPartsH v h μ Φ
        + (1 / 2) * Work.BoseFixR.errKafz v R μ (Ci + CB)
            * Work.BoseBoxFix.normB v μ n Φ := by
    have he := himg μ hAdm_i hJ n Φ hn hnorm hlow hspec
    rw [hℓrw] at he
    rw [← hW₁def, ← hW₂def] at he
    have hb := hB3m μ hAdm_B hJ n Φ hn hnorm hlow hspec N hN c hc_orig hr
    rw [hℓrw] at hb
    have hparts : rowWordPartsH v h μ Φ
        = Submission.BoseGases.q1PairWord (ℓ := ℓ) (v := v) h
            (Φ := (Φ : Submission.BoseGases.X n → ℝ))
          + Submission.BoseGases.q4PairWord (ℓ := ℓ) (v := v) h
              (Φ := (Φ : Submission.BoseGases.X n → ℝ))
          + rowMassWord v h μ ℓ (Φ : Submission.BoseGases.X n → ℝ) := by
      unfold rowWordPartsH rowWordParts
      rw [hℓrw]
    have harr : (1 / 2) * Work.BoseFixR.errKafz v R μ (Ci + CB)
          * Work.BoseBoxFix.normB v μ n Φ
        = (1 / 2) * Work.BoseFixR.errKafz v R μ Ci * Work.BoseBoxFix.normB v μ n Φ
          + (1 / 2) * Work.BoseFixR.errKafz v R μ CB * Work.BoseBoxFix.normB v μ n Φ := by
      rw [pairRow_errKafz_add v R μ Ci CB]
      ring
    rw [hwords, hparts]
    have herr : 0 ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ Cs * Work.BoseBoxFix.normB v μ n Φ :=
      mul_nonneg (mul_nonneg (by norm_num) (errKafz_nonneg' hμ hav hCs)) hnorm.le
    linarith [he, hb, harr, herr]
  have htot : (1 / 2) * Work.BoseFixR.errKafz v R μ (Cs + (Ci + CB))
        * Work.BoseBoxFix.normB v μ n Φ
      = (1 / 2) * Work.BoseFixR.errKafz v R μ (Ci + CB) * Work.BoseBoxFix.normB v μ n Φ
        + (1 / 2) * Work.BoseFixR.errKafz v R μ Cs * Work.BoseBoxFix.normB v μ n Φ := by
    rw [pairRow_errKafz_add v R μ Cs (Ci + CB)]
    ring
  linarith [hstep0, hstep1, hstep2, htot]

end Work.BoseBoxFock
