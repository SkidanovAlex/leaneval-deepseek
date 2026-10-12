import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.imagesEnergyB
import Submission.Work.BoseBoxFock.imagesWordArith
import Submission.Work.BoseBoxFock.imagesWordAux
import Submission.Work.BoseBoxFock.imgFibreDchiLe
import Submission.Work.BoseBoxFock.imgFibreDchiPin
import Submission.Work.BoseBoxFock.imgFibreDchiSelf
import Submission.Work.BoseBoxFock.imgFibreEnergyLe
import Submission.Work.BoseBoxFock.imgFibreNormLe
import Submission.Work.BoseBoxFock.pairRowWordParts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.imagesWordLe` — the images word is `≤ ½·errKafz·normB`

The two words `q1WordK ℓ (imgKernel ℓ W₁') Φ` and `q4WordK ℓ (imgKernel ℓ W₂) Φ` (the images part
of the `Q₂` pair kernel, `FINDING_PotPairRows_exists.md` §9) are bounded uniformly in the state.

**The obstruction** (`FINDING_imagesWordLe.md` §0): `imgKernel ℓ W` is neither bounded nor `L²`
(the honest weights `W1fun`/`W1omegaFun` are only `L¹`), so no crude bound applies.  The working
route is the corpus's **images-pairing tail** `chiChiImages_pairing_boxSmooth`, which needs only the
pairing test function's `BoxSmooth`-ness and its **Dirichlet energy**.

**The route.**  Each pair term is **peeled** into a `boxL × boxL` pairing against a fibre
(`imgFibre_peel` for the `q1` word — its free factor `aP ℓ p.2 (aQ ℓ p.1 Φ)` is `p.2`-independent;
`imgFibre2_peel` for the `q4` word, whose free factor is `aQ ℓ p.2 (aQ ℓ p.1 Φ)` and whose averaged
factor `aP ℓ p.2 (aP ℓ p.1 Φ) = aP ℓ p.1 (aP ℓ p.2 Φ)` *is* `p.1`-independent), then the pairing is
bounded by `imagesCimg·(R/ℓ)^6·√(∫coulInt W)·√(ℓ³·pairEnergy)` (`imagesWordAux`), and the fibre's
Dirichlet energy by `imgFibreEnergyLe`/`imgFibre2EnergyLe`.  The chain of the state's data is

    `imgFibreDχ ≤ pinDirChi ℓ Φ` (`imgFibreDchiPin`, `imgFibreDchiSelf`, `imgFibreDchiLe`)
      `≤ K10(2+κ)μℓ³ normB` (`pinDirChiExp` + `IsLowB`),

and the final monomial comparison is `imagesWordArith` + `errKafz_ge`.
-/

noncomputable section

set_option maxHeartbeats 4000000

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

theorem imagesWordLe (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
          (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
          0 < Work.BoseBoxFix.normB v μ n Φ →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
            (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFock.q1WordK (Work.BoseBoxFock.ellH v μ)
              (Work.BoseBoxFock.imgKernel (Work.BoseBoxFock.ellH v μ)
                (fun x => Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x
                  + Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ) x))
              (Φ : Submission.BoseGases.X n → ℝ)
            + Work.BoseBoxFock.q4WordK (Work.BoseBoxFock.ellH v μ)
                (Work.BoseBoxFock.imgKernel (Work.BoseBoxFock.ellH v μ)
                  (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
                (Φ : Submission.BoseGases.X n → ℝ)
            ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ := by
  classical
  -- ## 0. constants and thresholds
  obtain ⟨chiC, hchiC0, rchi, hrchi, hchiT⟩ := Submission.BoseGases.conv3chi_second_order_bound
  obtain ⟨kap, εkap, hkappos, hεkappos, hkap⟩ :=
    kinFormBLeLowBudgetB (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨ε_sr, hε_srpos, hε_srle1, hε_sr⟩ := sideAt_regime (v := v) hav
  set rm : ℝ := (Real.sqrt (2 * chiC + 1))⁻¹ with hrmdef
  have hrmpos : 0 < rm := by rw [hrmdef]; exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hrmsq : chiC * rm ^ 2 ≤ 1 / 2 := by
    have h1 : rm ^ 2 = (2 * chiC + 1)⁻¹ := by
      rw [hrmdef, inv_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * chiC + 1)]
    rw [h1, mul_inv_le_iff₀ (by linarith : (0 : ℝ) < 2 * chiC + 1)]
    linarith
  set rr : ℝ := min (1 / 4) (min rchi rm) with hrrdef
  have hrrpos : 0 < rr := lt_min (by norm_num) (lt_min hrchi hrmpos)
  have hrr4 : rr ≤ 1 / 4 := le_trans (min_le_left _ _) le_rfl
  have hrrr : rr ≤ rchi := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrrm : rr ≤ rm := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨ε_R, hε_Rpos, hε_Rle1, hε_R⟩ :=
    exists_threshold_sideAt_ge_mul (v := v) hav hR hrrpos
  set a : ℝ := BoseGases.a v with hadef
  have ha0 : 0 < a := hav
  set P : ℝ := Work.BoseFixB1S.chiPlateau with hPdef
  have hP0 : 0 ≤ P := Work.BoseFixB1S.chiPlateau_nonneg
  have hchiGB0 : 0 ≤ L1Tails.chiGB :=
    le_trans (norm_nonneg (fderiv ℝ Submission.BoseGases.chiBase (0 : ℝ³)))
      (L1Tails.chiBase_fderiv_le_chiGB 0)
  set K10 : ℝ := 4 + 16 * (1 / (2 * a ^ 2)) * P ^ 2
      + 24 * (L1Tails.chiGB * P / a) ^ 2 with hK10def
  have hK100 : 0 ≤ K10 := by rw [hK10def]; positivity
  set Cwin0 : ℝ := max (2 * (3 * (L1Tails.chiGB * P / a) ^ 2) + (1 / a ^ 2) * P ^ 2) 2
    with hCwin0def
  have hCwin00 : 0 ≤ Cwin0 := le_trans (by norm_num) (le_max_right _ _)
  set Ccoef : ℝ := imagesCimg * (8 * 32 * Real.pi * Real.sqrt a * Real.sqrt Cwin0 * R ^ 6
      * a ^ (-(11 / 2) : ℝ) * (1 + Real.sqrt (K10 * (kap + 2)))) with hCcoefdef
  have hCcoef0 : 0 ≤ Ccoef := by
    rw [hCcoefdef]
    refine mul_nonneg imagesCimg_nonneg ?_
    have h6 : (0 : ℝ) ≤ 8 * 32 * Real.pi := by positivity
    have h3 : (0 : ℝ) ≤ Real.sqrt a := Real.sqrt_nonneg _
    have h4 : (0 : ℝ) ≤ Real.sqrt Cwin0 := Real.sqrt_nonneg _
    have h5 : (0 : ℝ) ≤ R ^ 6 := pow_nonneg hR.le 6
    have h1 : (0 : ℝ) ≤ a ^ (-(11 / 2) : ℝ) := Real.rpow_nonneg ha0.le _
    have h2 : (0 : ℝ) ≤ 1 + Real.sqrt (K10 * (kap + 2)) :=
      by linarith [Real.sqrt_nonneg (K10 * (kap + 2))]
    have h7 : (0 : ℝ) ≤ 8 * 32 * Real.pi * Real.sqrt a := mul_nonneg h6 h3
    have h8 : (0 : ℝ) ≤ 8 * 32 * Real.pi * Real.sqrt a * Real.sqrt Cwin0 := mul_nonneg h7 h4
    have h9 : (0 : ℝ) ≤ 8 * 32 * Real.pi * Real.sqrt a * Real.sqrt Cwin0 * R ^ 6 :=
      mul_nonneg h8 h5
    have h10 : (0 : ℝ) ≤ 8 * 32 * Real.pi * Real.sqrt a * Real.sqrt Cwin0 * R ^ 6
        * a ^ (-(11 / 2) : ℝ) := mul_nonneg h9 h1
    exact mul_nonneg h10 h2
  refine ⟨min (min ε_R ε_sr) (min εkap 1), 2 * Ccoef + 1,
    lt_min (lt_min hε_Rpos hε_srpos) (lt_min hεkappos one_pos), by linarith, ?_⟩
  intro μ hAdm hJ n Φ hn hnorm hlow hspec
  -- ## 1. the regime
  let ℓ : ℝ := Work.BoseBox.sideAt μ (BoseGases.a v)
  have hℓpos : 0 < ℓ := Work.BoseBox.sideAt_pos hAdm.1 hav
  have hℓeq : Work.BoseBoxFock.ellH v μ = ℓ := by
    show (if 0 < Work.BoseBox.sideAt μ (BoseGases.a v) then Work.BoseBox.sideAt μ (BoseGases.a v)
      else 1) = ℓ
    rw [if_pos hℓpos]
  rw [hℓeq]
  have hμ : 0 < μ := hAdm.1
  have htε : μ * a ^ 3 ≤ min (min ε_R ε_sr) (min εkap 1) := hAdm.2.1
  have hPOK : Work.BoseBox.ParamsOK (Work.BoseBox.paramsAt μ a) (μ * a ^ 3) := hAdm.2.2
  obtain ⟨_hXp, hdP, hsP, heT0P, heT1P, hbP, _hKlP⟩ := Work.BoseBox.paramsAt_facts hμ hPOK
  have ht1 : μ * a ^ 3 ≤ 1 :=
    le_trans htε (le_trans (min_le_right _ _) (min_le_right _ _))
  have htR : μ * a ^ 3 ≤ ε_R := le_trans htε (le_trans (min_le_left _ _) (min_le_left _ _))
  have htSR : μ * a ^ 3 ≤ ε_sr := le_trans htε (le_trans (min_le_left _ _) (min_le_right _ _))
  have htk : μ * a ^ 3 ≤ εkap := le_trans htε (le_trans (min_le_right _ _) (min_le_left _ _))
  obtain ⟨ha_le_ℓ, hone_le_ℓ, hμa, hμℓ3, hκbr⟩ := hε_sr μ hμ htSR
  have hRrr : R ≤ ℓ * rr := hε_R μ hμ htR
  have hRdiv : R / ℓ ≤ rr := by
    rw [div_le_iff₀ hℓpos, mul_comm]
    exact hRrr
  have hRℓ4 : R ≤ ℓ / 4 := by
    calc R ≤ ℓ * rr := hRrr
      _ ≤ ℓ * (1 / 4) := mul_le_mul_of_nonneg_left hrr4 hℓpos.le
      _ = ℓ / 4 := by ring
  have hreg : R / ℓ ≤ rchi := le_trans hRdiv hrrr
  have hrm : R / ℓ ≤ rm := le_trans hRdiv hrrm
  have hcond : chiC * (R / ℓ) ^ 2 ≤ 1 / 2 := by
    have hRl0 : 0 ≤ R / ℓ := by positivity
    have hsq : (R / ℓ) ^ 2 ≤ rm ^ 2 := by
      have hmul := mul_le_mul hrm hrm hRl0 hrmpos.le
      simpa [pow_two] using hmul
    calc chiC * (R / ℓ) ^ 2 ≤ chiC * rm ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hchiC0
      _ ≤ 1 / 2 := hrmsq
  -- ## 2. the weights and their `L¹`/Coulomb data
  obtain ⟨hW1i, hW10, hW1s⟩ := W1fun_integrable_of_regime (v := v) (h := h) (R := R) (ℓ := ℓ)
    (r₁ := rchi) (C := chiC) hR hv hvrad hv_supp hchiC0 hrchi hchiT hℓpos hreg hcond
  obtain ⟨hW2i, hW20, hW2s, _hW2e, _hW2J, hWsumJ⟩ := W1omega_weight_facts (v := v) (h := h)
    (R := R) (ℓ := ℓ) (r₁ := rchi) (C := chiC) hR hv hvrad hv_supp hchiC0 hrchi hchiT hℓpos hreg
    hcond
  obtain ⟨hW1Jint, hW1J, hW2Jint, hW2J⟩ := L1Tails.W1fun_coulomb_le (v := v) (R := R) (ℓ := ℓ)
    (r₁ := rchi) (C := chiC) hR hv hvrad hv_supp h hchiC0 hrchi hchiT hℓpos hreg hcond
  set W₁ : ℝ³ → ℝ := fun x => Work.BoseFixR.W1fun v h ℓ x + Work.BoseFixR.W1omegaFun v h ℓ x
    with hW1def
  set W₂ : ℝ³ → ℝ := Work.BoseFixR.W1fun v h ℓ with hW2def
  have hW₁i : MeasureTheory.Integrable W₁ := hW1i.add hW2i
  have hW₁0 : ∀ᵐ x : ℝ³, 0 ≤ W₁ x := by
    filter_upwards [hW10, hW20] with x h1 h2
    simp only [hW1def]; linarith
  have hW₁s : ∀ x : ℝ³, R ≤ ‖x‖ → W₁ x = 0 := by
    intro x hx
    simp only [hW1def]; rw [hW1s x hx, hW2s x hx, add_zero]
  have hW₁Jint : MeasureTheory.Integrable (coulInt W₁) := by rw [hW1def]; exact hWsumJ
  have hW₂i : MeasureTheory.Integrable W₂ := hW1i
  have hW₂0 : ∀ᵐ x : ℝ³, 0 ≤ W₂ x := by
    filter_upwards [hW10] with x h1; simpa only [hW2def] using h1
  have hW₂s : ∀ x : ℝ³, R ≤ ‖x‖ → W₂ x = 0 := by
    intro x hx; simpa only [hW2def] using hW1s x hx
  have hW₂Jint : MeasureTheory.Integrable (coulInt W₂) := hW1Jint
  have hcoul₁ : (∫ p, coulInt W₁ p) ≤ 1024 * Real.pi ^ 2 * a := by
    rw [hW1def]
    exact coulInt_sum_le (v := v) (h := h) (R := R) (ℓ := ℓ) (r₁ := rchi) (C := chiC)
      hR hv hvrad hv_supp hchiC0 hrchi hchiT hℓpos hreg hcond
  have hcoul₂ : (∫ p, coulInt W₂ p) ≤ 1024 * Real.pi ^ 2 * a := by
    rw [hW2def, hadef]
    have hX0 : (0 : ℝ) ≤ Real.pi ^ 2 * BoseGases.a v :=
      mul_nonneg (pow_nonneg Real.pi_pos.le 2) hav.le
    have hle : (256 : ℝ) * (Real.pi ^ 2 * BoseGases.a v)
        ≤ 1024 * (Real.pi ^ 2 * BoseGases.a v) := by linarith
    calc (∫ p, coulInt (Work.BoseFixR.W1fun v h ℓ) p)
        ≤ 256 * Real.pi ^ 2 * BoseGases.a v := hW1J
      _ = 256 * (Real.pi ^ 2 * BoseGases.a v) := by ring
      _ ≤ 1024 * (Real.pi ^ 2 * BoseGases.a v) := hle
      _ = 1024 * Real.pi ^ 2 * BoseGases.a v := by ring
  have hsqrt_a : Real.sqrt (1024 * Real.pi ^ 2 * a) = 32 * Real.pi * Real.sqrt a := by
    rw [show (1024 : ℝ) * Real.pi ^ 2 * a = (32 * Real.pi) ^ 2 * a by ring,
      Real.sqrt_mul (by positivity) a, Real.sqrt_sq (by positivity)]
  -- ## 3. the window data
  set Kg : ℝ := 3 * (L1Tails.chiGB * P / ℓ) ^ 2 with hKgdef
  set Kc : ℝ := P ^ 2 with hKcdef
  have hKg0 : 0 ≤ Kg := by rw [hKgdef]; exact mul_nonneg (by norm_num) (sq_nonneg _)
  have hKc0 : 0 ≤ Kc := by rw [hKcdef]; exact sq_nonneg _
  have hKg : ∀ w : ℝ³, ∑ j : Fin 3,
      ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        ≤ Kg := by
    intro w
    have h1 := chiS_grad_bound ℓ hℓpos w
    have h2 : ∀ j : Fin 3,
        ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖
          = |fderiv ℝ (Submission.BoseGases.chiScale ℓ) w (EuclideanSpace.single j (1 : ℝ))| := by
      intro j
      rw [show chiS ℓ = fun y => ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ) from
        funext (chiS_eq ℓ)]
      rw [ofReal_fderiv (Submission.BoseGases.chiScale ℓ)
        ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓpos)).differentiable (by simp))
        w (EuclideanSpace.single j (1 : ℝ))]
      exact RCLike.norm_ofReal _
    rw [hKgdef]
    calc ∑ j : Fin 3,
        ‖fderiv ℝ (Submission.BoseGases.chiScale ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2
        = ∑ j : Fin 3, ‖fderiv ℝ (chiS ℓ) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [h2 j, Real.norm_eq_abs]
      _ ≤ 3 * (L1Tails.chiGB * Work.BoseFixB1S.chiPlateau / ℓ) ^ 2 := h1
  have hKc : ∀ w : ℝ³, (Submission.BoseGases.chiScale ℓ w) ^ 2 ≤ Kc := by
    intro w
    have h1 := chiS_sq_bound ℓ w
    have h2 : ‖chiS ℓ w‖ = |Submission.BoseGases.chiScale ℓ w| := by
      rw [chiS_eq]; exact RCLike.norm_ofReal _
    rw [hKcdef, ← sq_abs, ← h2]
    exact h1
  set Cw : ℝ := max (2 * Kg + (ℓ ^ 2)⁻¹ * Kc) 2 with hCwdef
  have hCw0 : 0 ≤ Cw := le_trans (by norm_num) (le_max_right _ _)
  have hCwle : Cw ≤ Cwin0 := by
    rw [hCwdef, hCwin0def]
    refine max_le_max ?_ le_rfl
    have hKg' : Kg ≤ 3 * (L1Tails.chiGB * P / a) ^ 2 := by
      rw [hKgdef, hPdef]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine pow_le_pow_left₀ (div_nonneg (mul_nonneg hchiGB0 hP0) hℓpos.le) ?_ 2
      have h1 : ℓ⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 ha_le_ℓ
      calc L1Tails.chiGB * Work.BoseFixB1S.chiPlateau / ℓ
          = (L1Tails.chiGB * Work.BoseFixB1S.chiPlateau) * ℓ⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ (L1Tails.chiGB * Work.BoseFixB1S.chiPlateau) * a⁻¹ :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg hchiGB0 hP0)
        _ = L1Tails.chiGB * Work.BoseFixB1S.chiPlateau / a := by rw [div_eq_mul_inv]
    have hKc' : (ℓ ^ 2)⁻¹ * Kc ≤ (a ^ 2)⁻¹ * P ^ 2 := by
      rw [hKcdef, hPdef]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      exact inv_anti₀ (pow_pos ha0 2) (pow_le_pow_left₀ ha0.le ha_le_ℓ 2)
    have h2 : 2 * Kg ≤ 2 * (3 * (L1Tails.chiGB * P / a) ^ 2) := by linarith [hKg']
    rw [one_div]
    linarith [h2, hKc']
  -- ## 4. the state data
  set pL : ℝ := Work.BoseBoxFix.normB v μ n Φ with hpLdef
  have hpL : 0 ≤ pL := Work.BoseFixB1.normB_nonneg Φ
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hΦcd : ContDiff ℝ (⊤ : ℕ∞) (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff
  set D : ℝ := Work.BoseBoxFock.pinDirChi ℓ (fun x => ((Φ x : ℝ) : ℂ)) with hDdef
  have hD0 : 0 ≤ D := Work.BoseBoxFock.pinDirChi_nonneg ℓ _
  have hNΦ : imgFibreN ℓ (Φ : Submission.BoseGases.X n → ℝ) = pL := by
    rw [hpLdef]
    simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, imgFibreN]
    rfl
  have hKinB : Work.BoseKinLoc.kinFormB n ℓ (Work.BoseBox.paramsAt μ a).d
        (Work.BoseBox.paramsAt μ a).s (Work.BoseBox.paramsAt μ a).eT
        (Work.BoseBox.paramsAt μ a).b (Φ : Submission.BoseGases.X n → ℝ)
      ≤ kap * μ ^ 2 * a * ℓ ^ 3 * pL := by
    have hAdmkap : Work.BoseBoxFix.Adm v εkap μ :=
      Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
    rcases le_or_gt 0 J with hJ0 | hJneg
    · exact hkap μ hAdmkap J hJ0 hJ n Φ hlow hn
    · have hθ : Work.UBB.Theta (BoseGases.a v) J μ ≤ Work.UBB.Theta (BoseGases.a v) 0 μ :=
        Theta_le_Theta_zero hav.le hJneg.le
      have hstep : Work.BoseBox.sideAt μ a ^ 3 * Work.UBB.Theta (BoseGases.a v) J μ
            * Work.BoseBoxFix.normB v μ n Φ
          ≤ Work.BoseBox.sideAt μ a ^ 3 * Work.UBB.Theta (BoseGases.a v) 0 μ
            * Work.BoseBoxFix.normB v μ n Φ := by
        refine mul_le_mul_of_nonneg_right ?_ (Work.BoseFixB1.normB_nonneg Φ)
        exact mul_le_mul_of_nonneg_left hθ (pow_nonneg hℓpos.le 3)
      have hlow0 : Work.BoseBoxFix.IsLowB v h 0 μ n Φ := by
        have hall := hlow
        simp only [Work.BoseBoxFix.IsLowB] at hall ⊢
        exact hall.trans hstep
      have hKB0 : 0 ≤ (Work.BoseBox.paramsAt μ a).KB ^ 3 := by
        have hKBpos : 0 < (Work.BoseBox.paramsAt μ a).KB := by
          simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
          exact Real.rpow_pos_of_pos (mul_pos hμ (pow_pos ha0 3)) _
        exact pow_nonneg hKBpos.le 3
      exact hkap μ hAdmkap 0 (le_refl 0) hKB0 n Φ hlow0 hn
  have hDbound : D ≤ K10 * (2 + kap) * μ * ℓ ^ 3 * pL := by
    rw [hDdef]
    have hDχ : ∀ x v : ℝ³, |fderiv ℝ (Submission.BoseGases.chiScale ℓ) x v|
        ≤ (L1Tails.chiGB * P / a) * ‖v‖ := by
      intro x v
      refine (chiScale_fderiv_bound ℓ hℓpos x v).trans ?_
      have h1 : ℓ⁻¹ ≤ a⁻¹ := inv_anti₀ ha0 ha_le_ℓ
      have h2 : L1Tails.chiGB * P / ℓ ≤ L1Tails.chiGB * P / a := by
        calc L1Tails.chiGB * P / ℓ = (L1Tails.chiGB * P) * ℓ⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ (L1Tails.chiGB * P) * a⁻¹ := mul_le_mul_of_nonneg_left h1 (mul_nonneg hchiGB0 hP0)
          _ = L1Tails.chiGB * P / a := by rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right h2 (norm_nonneg v)
    have hpd := Work.BoseBoxFock.pinDirChiExp (l := ℓ) (d := (Work.BoseBox.paramsAt μ a).d)
      (s := (Work.BoseBox.paramsAt μ a).s) (εT := (Work.BoseBox.paramsAt μ a).eT)
      (b := (Work.BoseBox.paramsAt μ a).b) (D := L1Tails.chiGB * P / a)
      hℓpos hdP hsP hbP heT0P heT1P (div_nonneg (mul_nonneg hchiGB0 hP0) ha0.le) hDχ Φ
    have hK10' : 4 + 16 * ((1 - (Work.BoseBox.paramsAt μ a).eT)
          * ((2 * ((Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2
        + (Work.BoseBox.paramsAt μ a).eT
          * ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2)
        * P ^ 2 + 24 * (L1Tails.chiGB * P / a) ^ 2 ≤ K10 := by
      rw [hK10def]
      have h1 : 16 * ((1 - (Work.BoseBox.paramsAt μ a).eT)
            * ((2 * ((Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2
          + (Work.BoseBox.paramsAt μ a).eT
            * ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2)
          * P ^ 2 ≤ 16 * (1 / (2 * a ^ 2)) * P ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hκbr (by norm_num)) (sq_nonneg P)
      linarith [h1]
    have hsum : Work.BoseKinLoc.kinFormB n ℓ (Work.BoseBox.paramsAt μ a).d
          (Work.BoseBox.paramsAt μ a).s (Work.BoseBox.paramsAt μ a).eT
          (Work.BoseBox.paramsAt μ a).b (Φ : Submission.BoseGases.X n → ℝ)
        + (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
        ≤ (2 + kap) * μ * ℓ ^ 3 * pL := by
      have h2 : (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2)
          ≤ 2 * μ * ℓ ^ 3 * pL := by
        have hΦ2 : (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) = pL := by
          rw [hpLdef]
          simp only [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
          rfl
        rw [hΦ2]
        exact mul_le_mul_of_nonneg_right hn hpL
      have h3 : kap * μ ^ 2 * a * ℓ ^ 3 * pL ≤ kap * μ * ℓ ^ 3 * pL := by
        have h1 : μ ^ 2 * a ≤ μ := by
          calc μ ^ 2 * a = μ * (μ * a) := by ring
            _ ≤ μ * 1 := mul_le_mul_of_nonneg_left hμa hμ.le
            _ = μ := by ring
        calc kap * μ ^ 2 * a * ℓ ^ 3 * pL = kap * (μ ^ 2 * a) * ℓ ^ 3 * pL := by ring
          _ ≤ kap * μ * ℓ ^ 3 * pL := by
              refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left h1 hkappos.le) (pow_nonneg hℓpos.le 3)) hpL
      linarith [hKinB, h2, h3]
    calc Work.BoseBoxFock.pinDirChi ℓ (fun x => ((Φ x : ℝ) : ℂ))
        ≤ (4 + 16 * ((1 - (Work.BoseBox.paramsAt μ a).eT)
            * ((2 * ((Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2
          + (Work.BoseBox.paramsAt μ a).eT
            * ((2 * ((Work.BoseBox.paramsAt μ a).d * (Work.BoseBox.paramsAt μ a).s * ℓ))⁻¹) ^ 2)
          * P ^ 2 + 24 * (L1Tails.chiGB * P / a) ^ 2)
          * (Work.BoseKinLoc.kinFormB n ℓ (Work.BoseBox.paramsAt μ a).d
              (Work.BoseBox.paramsAt μ a).s (Work.BoseBox.paramsAt μ a).eT
              (Work.BoseBox.paramsAt μ a).b (Φ : Submission.BoseGases.X n → ℝ)
            + (n : ℝ) * ∫ x in Submission.BoseGases.abox n ℓ,
                ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := hpd
      _ ≤ K10 * ((2 + kap) * μ * ℓ ^ 3 * pL) := by
          have hsum0 : 0 ≤ Work.BoseKinLoc.kinFormB n ℓ (Work.BoseBox.paramsAt μ a).d
                (Work.BoseBox.paramsAt μ a).s (Work.BoseBox.paramsAt μ a).eT
                (Work.BoseBox.paramsAt μ a).b (Φ : Submission.BoseGases.X n → ℝ)
              + (n : ℝ) * (∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2) :=
            add_nonneg (Work.BoseKinLoc.Word.kinFormB_nonneg hℓpos hdP hsP heT0P heT1P hbP Φ)
              (mul_nonneg (Nat.cast_nonneg n) (MeasureTheory.integral_nonneg fun x => sq_nonneg _))
          exact mul_le_mul hK10' hsum hsum0 hK100
      _ = K10 * (2 + kap) * μ * ℓ ^ 3 * pL := by ring
  -- ## 5. the per-pair fibre data
  set εpair : ℝ := imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a)
      * Real.sqrt Cwin0 with hεpairdef
  have hεpair0 : 0 ≤ εpair := by
    rw [hεpairdef]
    refine mul_nonneg (mul_nonneg (mul_nonneg imagesCimg_nonneg
      (pow_nonneg (div_nonneg hR.le hℓpos.le) 6)) ?_) (Real.sqrt_nonneg _)
    exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  -- the norm inputs of the two fibres
  have hnormA : ∀ p : Fin n × Fin n, p.1 ≠ p.2 →
      imgFibreN ℓ (Submission.BoseGases.aQ ℓ p.2 Φ) ≤ pL ∧
      imgFibreN ℓ (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)) ≤ pL := by
    intro p hp
    have h1 := (imgFibreNormLe (ℓ := ℓ) hℓpos (i := p.2) (F := (Φ : Submission.BoseGases.X n → ℝ))
      hΦc).2
    have hcQ : Continuous (Submission.BoseGases.aQ ℓ p.1 (Φ : Submission.BoseGases.X n → ℝ)) :=
      (Submission.BoseGases.contDiff_aQ hℓpos p.1 hΦcd).continuous
    have h2' := (imgFibreNormLe (ℓ := ℓ) hℓpos (i := p.2)
      (F := Submission.BoseGases.aQ ℓ p.1 (Φ : Submission.BoseGases.X n → ℝ)) hcQ).1
    have h3 := (imgFibreNormLe (ℓ := ℓ) hℓpos (i := p.1) (F := (Φ : Submission.BoseGases.X n → ℝ))
      hΦc).2
    exact ⟨h1.trans (le_of_eq hNΦ), h2'.trans (h3.trans (le_of_eq hNΦ))⟩
  have hnormB : ∀ p : Fin n × Fin n, p.1 ≠ p.2 →
      imgFibreN ℓ (Submission.BoseGases.aP ℓ p.1 Φ) ≤ pL ∧
      imgFibreN ℓ (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)) ≤ pL := by
    intro p hp
    have h1 := (imgFibreNormLe (ℓ := ℓ) hℓpos (i := p.1) (F := (Φ : Submission.BoseGases.X n → ℝ))
      hΦc).1
    have hcQ : Continuous (Submission.BoseGases.aQ ℓ p.1 (Φ : Submission.BoseGases.X n → ℝ)) :=
      (Submission.BoseGases.contDiff_aQ hℓpos p.1 hΦcd).continuous
    have h2' := (imgFibreNormLe (ℓ := ℓ) hℓpos (i := p.2)
      (F := Submission.BoseGases.aQ ℓ p.1 (Φ : Submission.BoseGases.X n → ℝ)) hcQ).2
    have h3 := (imgFibreNormLe (ℓ := ℓ) hℓpos (i := p.1) (F := (Φ : Submission.BoseGases.X n → ℝ))
      hΦc).2
    exact ⟨h1.trans (le_of_eq hNΦ), h2'.trans (h3.trans (le_of_eq hNΦ))⟩
  have hDleA : ∀ p : Fin n × Fin n, (hp : p.1 ≠ p.2) →
      imgFibreDχ ℓ p (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)) ≤ D := by
    intro p hp
    have h2 : p.2 ≠ p.1 := fun hh => hp hh.symm
    have hcQ : ContDiff ℝ (⊤ : ℕ∞) (Submission.BoseGases.aQ ℓ p.1 Φ) :=
      Submission.BoseGases.contDiff_aQ hℓpos p.1 hΦcd
    refine ((imgFibreDchiLe hℓpos hp (F := Submission.BoseGases.aQ ℓ p.1 Φ) hcQ h2).1.trans ?_)
    exact ((imgFibreDchiSelf hℓpos (F := (Φ : Submission.BoseGases.X n → ℝ)) hΦcd).trans
      (imgFibreDchiPin (p := p) hΦcd)).trans (le_of_eq hDdef.symm)
  have hDleB : ∀ p : Fin n × Fin n, (hp : p.1 ≠ p.2) →
      imgFibreDχ ℓ p (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)) ≤ D := by
    intro p hp
    have h2 : p.2 ≠ p.1 := fun hh => hp hh.symm
    have hcQ : ContDiff ℝ (⊤ : ℕ∞) (Submission.BoseGases.aQ ℓ p.1 Φ) :=
      Submission.BoseGases.contDiff_aQ hℓpos p.1 hΦcd
    refine ((imgFibreDchiLe hℓpos hp (F := Submission.BoseGases.aQ ℓ p.1 Φ) hcQ h2).2.trans ?_)
    exact ((imgFibreDchiSelf hℓpos (F := (Φ : Submission.BoseGases.X n → ℝ)) hΦcd).trans
      (imgFibreDchiPin (p := p) hΦcd)).trans (le_of_eq hDdef.symm)
  -- the common fibre-energy majorant
  have hfibA : ∀ p : Fin n × Fin n, (hp : p.1 ≠ p.2) →
      Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ
          (imgFibreC ℓ p (Submission.BoseGases.aQ ℓ p.2 Φ)
            (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))))
        ≤ Real.sqrt Cw * Real.sqrt (pL * (pL + D) / ℓ ^ 3) := by
    intro p hp
    have hcF : ContDiff ℝ (⊤ : ℕ∞) (Submission.BoseGases.aQ ℓ p.2 Φ) :=
      Submission.BoseGases.contDiff_aQ hℓpos p.2 hΦcd
    have hcG : ContDiff ℝ (⊤ : ℕ∞)
        (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)) :=
      Submission.BoseGases.contDiff_aP hℓpos p.2 (Submission.BoseGases.contDiff_aQ hℓpos p.1 hΦcd)
    have hGind : ∀ (x : Submission.BoseGases.X n) (t : ℝ³),
        Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)
          (Function.update x p.2 t)
          = Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x :=
      fun x t => Work.BoseBoxFock.aP_update p.2 _ x t
    have henergy := imgFibreEnergyLe hℓpos hp hcF hcG hGind hKg0 hKc0 hKg hKc
    have h1 : imgFibreN ℓ (Submission.BoseGases.aQ ℓ p.2 Φ) ≤ pL := (hnormA p hp).1
    have h2' : imgFibreN ℓ (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))
        ≤ pL := (hnormA p hp).2
    have h3 : imgFibreDχ ℓ p (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))
        ≤ D := hDleA p hp
    have hstep : imgFibreN ℓ (Submission.BoseGases.aQ ℓ p.2 Φ)
          * (imgFibreN ℓ (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))
              + imgFibreDχ ℓ p (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)))
        ≤ pL * (pL + D) := by
      refine mul_le_mul h1 (add_le_add h2' h3) ?_ hpL
      exact add_nonneg (imgFibreN_nonneg ℓ _) (imgFibreDχ_nonneg ℓ p _)
    have hE : L1Tails.pairEnergy ℓ (imgFibreC ℓ p (Submission.BoseGases.aQ ℓ p.2 Φ)
          (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)))
        ≤ Cw * (pL * (pL + D) / ℓ ^ 6) := by
      refine henergy.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCw0
      exact div_le_div_of_nonneg_right hstep (pow_nonneg hℓpos.le 6)
    calc Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ (imgFibreC ℓ p (Submission.BoseGases.aQ ℓ p.2 Φ)
            (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))))
        ≤ Real.sqrt (ℓ ^ 3 * (Cw * (pL * (pL + D) / ℓ ^ 6))) := by
          refine Real.sqrt_le_sqrt ?_
          exact mul_le_mul_of_nonneg_left hE (pow_nonneg hℓpos.le 3)
      _ = Real.sqrt Cw * Real.sqrt (pL * (pL + D) / ℓ ^ 3) := by
          have h1 : ℓ ^ 3 * (Cw * (pL * (pL + D) / ℓ ^ 6))
              = Cw * (pL * (pL + D) / ℓ ^ 3) := by
            field_simp
          rw [h1, Real.sqrt_mul hCw0]
  have hfibB : ∀ p : Fin n × Fin n, (hp : p.1 ≠ p.2) →
      Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ
          (imgFibre₂C ℓ p (Submission.BoseGases.aP ℓ p.1 Φ)
            (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))))
        ≤ Real.sqrt Cw * Real.sqrt (pL * (pL + D) / ℓ ^ 3) := by
    intro p hp
    have hcF : ContDiff ℝ (⊤ : ℕ∞) (Submission.BoseGases.aP ℓ p.1 Φ) :=
      Submission.BoseGases.contDiff_aP hℓpos p.1 hΦcd
    have hcG : ContDiff ℝ (⊤ : ℕ∞)
        (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)) :=
      Submission.BoseGases.contDiff_aQ hℓpos p.2
        (Submission.BoseGases.contDiff_aQ hℓpos p.1 hΦcd)
    have hFind : ∀ (x : Submission.BoseGases.X n) (t : ℝ³),
        Submission.BoseGases.aP ℓ p.1 Φ (Function.update x p.1 t)
          = Submission.BoseGases.aP ℓ p.1 Φ x :=
      fun x t => Work.BoseBoxFock.aP_update p.1 _ x t
    have henergy := imgFibre2EnergyLe hℓpos hp hcF hcG hFind hKg0 hKc0 hKg hKc
    have h1 : imgFibreN ℓ (Submission.BoseGases.aP ℓ p.1 Φ) ≤ pL := (hnormB p hp).1
    have h2' : imgFibreN ℓ (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))
        ≤ pL := (hnormB p hp).2
    have h3 : imgFibreDχ ℓ p (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))
        ≤ D := hDleB p hp
    have hstep : imgFibreN ℓ (Submission.BoseGases.aP ℓ p.1 Φ)
          * (imgFibreN ℓ (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))
              + imgFibreDχ ℓ p (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)))
        ≤ pL * (pL + D) := by
      refine mul_le_mul h1 (add_le_add h2' h3) ?_ hpL
      exact add_nonneg (imgFibreN_nonneg ℓ _) (imgFibreDχ_nonneg ℓ p _)
    have hE : L1Tails.pairEnergy ℓ (imgFibre₂C ℓ p (Submission.BoseGases.aP ℓ p.1 Φ)
          (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)))
        ≤ Cw * (pL * (pL + D) / ℓ ^ 6) := by
      refine henergy.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCw0
      exact div_le_div_of_nonneg_right hstep (pow_nonneg hℓpos.le 6)
    calc Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ (imgFibre₂C ℓ p (Submission.BoseGases.aP ℓ p.1 Φ)
            (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))))
        ≤ Real.sqrt (ℓ ^ 3 * (Cw * (pL * (pL + D) / ℓ ^ 6))) := by
          refine Real.sqrt_le_sqrt ?_
          exact mul_le_mul_of_nonneg_left hE (pow_nonneg hℓpos.le 3)
      _ = Real.sqrt Cw * Real.sqrt (pL * (pL + D) / ℓ ^ 3) := by
          have h1 : ℓ ^ 3 * (Cw * (pL * (pL + D) / ℓ ^ 6))
              = Cw * (pL * (pL + D) / ℓ ^ 3) := by
            field_simp
          rw [h1, Real.sqrt_mul hCw0]
  -- ## 6. the two per-pair bounds
  have hpairA : ∀ p ∈ Submission.BoseGases.pairSet n,
      |∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x
            * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            * imgKernel ℓ W₁ (x p.1) (x p.2)|
        ≤ εpair * Real.sqrt (pL * (pL + D) / ℓ ^ 3) := by
    intro p hp
    have hp' : p.1 ≠ p.2 := by
      have h' := hp
      simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at h'
      exact h'
    have hcF : ContDiff ℝ (⊤ : ℕ∞) (Submission.BoseGases.aQ ℓ p.2 Φ) :=
      Submission.BoseGases.contDiff_aQ hℓpos p.2 hΦcd
    have hcG : ContDiff ℝ (⊤ : ℕ∞)
        (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)) :=
      Submission.BoseGases.contDiff_aP hℓpos p.2
        (Submission.BoseGases.contDiff_aQ hℓpos p.1 hΦcd)
    have hpeel := imgPairLe (n := n) (ℓ := ℓ) (R := R) hℓpos hR hRℓ4 hp' hW₁i hW₁0 hW₁s
      hW₁Jint hcF hcG
    have hCoul : Real.sqrt (∫ z, coulInt W₁ z) ≤ 32 * Real.pi * Real.sqrt a := by
      calc Real.sqrt (∫ z, coulInt W₁ z) ≤ Real.sqrt (1024 * Real.pi ^ 2 * a) :=
            Real.sqrt_le_sqrt hcoul₁
        _ = 32 * Real.pi * Real.sqrt a := hsqrt_a
    have hX0 : (0 : ℝ) ≤ Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ
        (imgFibreC ℓ p (Submission.BoseGases.aQ ℓ p.2 Φ)
          (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)))) := Real.sqrt_nonneg _
    have hK6 : (0 : ℝ) ≤ imagesCimg * (R / ℓ) ^ 6 :=
      mul_nonneg imagesCimg_nonneg (pow_nonneg (div_nonneg hR.le hℓpos.le) 6)
    have hK32 : (0 : ℝ) ≤ imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a) :=
      mul_nonneg hK6 (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    have hA0 : (0 : ℝ) ≤ Real.sqrt (pL * (pL + D) / ℓ ^ 3) := Real.sqrt_nonneg _
    have hfib := hfibA p hp'
    have hstep1 : imagesCimg * (R / ℓ) ^ 6 * Real.sqrt (∫ z, coulInt W₁ z)
          * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ
              (imgFibreC ℓ p (Submission.BoseGases.aQ ℓ p.2 Φ)
                (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))))
        ≤ imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a)
          * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ
              (imgFibreC ℓ p (Submission.BoseGases.aQ ℓ p.2 Φ)
                (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCoul hK6) hX0
    have hstep2 : imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a)
          * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ
              (imgFibreC ℓ p (Submission.BoseGases.aQ ℓ p.2 Φ)
                (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))))
        ≤ imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a) * Real.sqrt Cw
          * Real.sqrt (pL * (pL + D) / ℓ ^ 3) := by
      have h := mul_le_mul_of_nonneg_left hfib hK32
      calc imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a)
            * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ
                (imgFibreC ℓ p (Submission.BoseGases.aQ ℓ p.2 Φ)
                  (Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))))
          ≤ imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a)
            * (Real.sqrt Cw * Real.sqrt (pL * (pL + D) / ℓ ^ 3)) := h
        _ = imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a) * Real.sqrt Cw
            * Real.sqrt (pL * (pL + D) / ℓ ^ 3) := by ring
    have hstep3 : imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a) * Real.sqrt Cw
          * Real.sqrt (pL * (pL + D) / ℓ ^ 3)
        ≤ εpair * Real.sqrt (pL * (pL + D) / ℓ ^ 3) := by
      rw [hεpairdef]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hCwle) hK32) hA0
    exact hpeel.trans (hstep1.trans (hstep2.trans hstep3))
  have hpairB : ∀ p ∈ Submission.BoseGases.pairSet n,
      |∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x
            * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            * imgKernel ℓ W₂ (x p.1) (x p.2)|
        ≤ εpair * Real.sqrt (pL * (pL + D) / ℓ ^ 3) := by
    intro p hp
    have hp' : p.1 ≠ p.2 := by
      have h' := hp
      simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ,
        true_and] at h'
      exact h'
    have hcF : ContDiff ℝ (⊤ : ℕ∞) (Submission.BoseGases.aP ℓ p.1 Φ) :=
      Submission.BoseGases.contDiff_aP hℓpos p.1 hΦcd
    have hcG : ContDiff ℝ (⊤ : ℕ∞)
        (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)) :=
      Submission.BoseGases.contDiff_aQ hℓpos p.2
        (Submission.BoseGases.contDiff_aQ hℓpos p.1 hΦcd)
    have hpeel := imgPairLe2 (n := n) (ℓ := ℓ) (R := R) hℓpos hR hRℓ4 hp' hW₂i hW₂0 hW₂s
      hW₂Jint hcF hcG
    have hCoul : Real.sqrt (∫ z, coulInt W₂ z) ≤ 32 * Real.pi * Real.sqrt a := by
      calc Real.sqrt (∫ z, coulInt W₂ z) ≤ Real.sqrt (1024 * Real.pi ^ 2 * a) :=
            Real.sqrt_le_sqrt hcoul₂
        _ = 32 * Real.pi * Real.sqrt a := hsqrt_a
    have hcomm : ∀ x : Submission.BoseGases.X n,
        Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x
          = Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x :=
      fun x => Submission.BoseGases.aP_comm hℓpos p.1 p.2 hΦc x
    have hcongr : |∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x
            * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            * imgKernel ℓ W₂ (x p.1) (x p.2)|
        = |∫ x in Submission.BoseGases.abox n ℓ,
            Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aP ℓ p.1 Φ) x
              * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
              * imgKernel ℓ W₂ (x p.1) (x p.2)| := by
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hcomm x]
    rw [hcongr]
    have hX0 : (0 : ℝ) ≤ Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ
        (imgFibre₂C ℓ p (Submission.BoseGases.aP ℓ p.1 Φ)
          (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)))) := Real.sqrt_nonneg _
    have hK6 : (0 : ℝ) ≤ imagesCimg * (R / ℓ) ^ 6 :=
      mul_nonneg imagesCimg_nonneg (pow_nonneg (div_nonneg hR.le hℓpos.le) 6)
    have hK32 : (0 : ℝ) ≤ imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a) :=
      mul_nonneg hK6 (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
    have hA0 : (0 : ℝ) ≤ Real.sqrt (pL * (pL + D) / ℓ ^ 3) := Real.sqrt_nonneg _
    have hfib := hfibB p hp'
    have hstep1 : imagesCimg * (R / ℓ) ^ 6 * Real.sqrt (∫ z, coulInt W₂ z)
          * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ
              (imgFibre₂C ℓ p (Submission.BoseGases.aP ℓ p.1 Φ)
                (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))))
        ≤ imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a)
          * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ
              (imgFibre₂C ℓ p (Submission.BoseGases.aP ℓ p.1 Φ)
                (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ)))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCoul hK6) hX0
    have hstep2 : imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a)
          * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ
              (imgFibre₂C ℓ p (Submission.BoseGases.aP ℓ p.1 Φ)
                (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))))
        ≤ imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a) * Real.sqrt Cw
          * Real.sqrt (pL * (pL + D) / ℓ ^ 3) := by
      have h := mul_le_mul_of_nonneg_left hfib hK32
      calc imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a)
            * Real.sqrt (ℓ ^ 3 * L1Tails.pairEnergy ℓ
                (imgFibre₂C ℓ p (Submission.BoseGases.aP ℓ p.1 Φ)
                  (Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ))))
          ≤ imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a)
            * (Real.sqrt Cw * Real.sqrt (pL * (pL + D) / ℓ ^ 3)) := h
        _ = imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a) * Real.sqrt Cw
            * Real.sqrt (pL * (pL + D) / ℓ ^ 3) := by ring
    have hstep3 : imagesCimg * (R / ℓ) ^ 6 * (32 * Real.pi * Real.sqrt a) * Real.sqrt Cw
          * Real.sqrt (pL * (pL + D) / ℓ ^ 3)
        ≤ εpair * Real.sqrt (pL * (pL + D) / ℓ ^ 3) := by
      rw [hεpairdef]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hCwle) hK32) hA0
    exact hpeel.trans (hstep1.trans (hstep2.trans hstep3))
  -- ## 7. the two words
  set A : ℝ := Real.sqrt (pL * (pL + D) / ℓ ^ 3) with hAdef
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hcard : ((Submission.BoseGases.pairSet n).card : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hc : (Submission.BoseGases.pairSet n).card ≤ n ^ 2 := by
      calc (Submission.BoseGases.pairSet n).card
          ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = n ^ 2 := by simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, pow_two]
    exact_mod_cast hc
  have hpairA' : ∀ p ∈ Submission.BoseGases.pairSet n,
      |∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aQ ℓ p.2 Φ) x
            * Submission.BoseGases.aP ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            * imgKernel ℓ W₁ (x p.1) (x p.2)| ≤ εpair * A := by
    intro p hp; rw [hAdef]; exact hpairA p hp
  have hpairB' : ∀ p ∈ Submission.BoseGases.pairSet n,
      |∫ x in Submission.BoseGases.abox n ℓ,
          Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x
            * Submission.BoseGases.aQ ℓ p.2 (Submission.BoseGases.aQ ℓ p.1 Φ) x
            * imgKernel ℓ W₂ (x p.1) (x p.2)| ≤ εpair * A := by
    intro p hp; rw [hAdef]; exact hpairB p hp
  have hq1 : |Work.BoseBoxFock.q1WordK ℓ (imgKernel ℓ W₁) (Φ : Submission.BoseGases.X n → ℝ)|
      ≤ (n : ℝ) ^ 2 * (εpair * A) := by
    rw [Work.BoseBoxFock.q1WordK]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 := Finset.sum_le_sum hpairA'
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hcard (mul_nonneg hεpair0 hA0))
  have hq4 : |Work.BoseBoxFock.q4WordK ℓ (imgKernel ℓ W₂) (Φ : Submission.BoseGases.X n → ℝ)|
      ≤ (n : ℝ) ^ 2 * (εpair * A) := by
    rw [Work.BoseBoxFock.q4WordK]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 := Finset.sum_le_sum hpairB'
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right hcard (mul_nonneg hεpair0 hA0))
  have htotal : Work.BoseBoxFock.q1WordK ℓ (imgKernel ℓ W₁) (Φ : Submission.BoseGases.X n → ℝ)
        + Work.BoseBoxFock.q4WordK ℓ (imgKernel ℓ W₂) (Φ : Submission.BoseGases.X n → ℝ)
      ≤ 2 * ((n : ℝ) ^ 2 * (εpair * A)) := by
    have h2 : (n : ℝ) ^ 2 * (εpair * A) + (n : ℝ) ^ 2 * (εpair * A)
        = 2 * ((n : ℝ) ^ 2 * (εpair * A)) := by ring
    calc Work.BoseBoxFock.q1WordK ℓ (imgKernel ℓ W₁) (Φ : Submission.BoseGases.X n → ℝ)
          + Work.BoseBoxFock.q4WordK ℓ (imgKernel ℓ W₂) (Φ : Submission.BoseGases.X n → ℝ)
        ≤ |Work.BoseBoxFock.q1WordK ℓ (imgKernel ℓ W₁) (Φ : Submission.BoseGases.X n → ℝ)|
          + |Work.BoseBoxFock.q4WordK ℓ (imgKernel ℓ W₂) (Φ : Submission.BoseGases.X n → ℝ)| :=
          add_le_add (le_abs_self _) (le_abs_self _)
      _ ≤ 2 * ((n : ℝ) ^ 2 * (εpair * A)) := by
          rw [← h2]
          exact add_le_add hq1 hq4
  -- ## 8. the monomial comparison
  have hn2 : (n : ℝ) ^ 2 ≤ 4 * μ ^ 2 * ℓ ^ 6 := by
    calc (n : ℝ) ^ 2 ≤ (2 * μ * ℓ ^ 3) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg n) hn 2
      _ = 4 * μ ^ 2 * ℓ ^ 6 := by ring
  have hK1 : 0 ≤ K10 * (kap + 2) := mul_nonneg hK100 (by linarith [hkappos])
  have hK1μℓ : 0 ≤ K10 * (kap + 2) * μ * ℓ ^ 3 :=
    mul_nonneg (mul_nonneg hK1 hμ.le) (pow_nonneg hℓpos.le 3)
  have hsl : A ≤ (pL + Real.sqrt (K10 * (kap + 2) * μ * ℓ ^ 3) * pL)
        * ℓ ^ (-(3 / 2) : ℝ) := by
    have h3 : 0 ≤ pL * D := mul_nonneg hpL hD0
    have hsqrt : Real.sqrt (pL * (pL + D)) ≤ pL + Real.sqrt (pL * D) := by
      have h4 : Real.sqrt (pL * D) ^ 2 = pL * D := Real.sq_sqrt h3
      have h2 : pL * (pL + D) ≤ (pL + Real.sqrt (pL * D)) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (pL * D)]
      calc Real.sqrt (pL * (pL + D)) ≤ Real.sqrt ((pL + Real.sqrt (pL * D)) ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = pL + Real.sqrt (pL * D) :=
            Real.sqrt_sq (by linarith [Real.sqrt_nonneg (pL * D)])
    have h2' : Real.sqrt (pL * D) ≤ Real.sqrt (K10 * (kap + 2) * μ * ℓ ^ 3) * pL := by
      have harg : pL * D ≤ (Real.sqrt (K10 * (kap + 2) * μ * ℓ ^ 3) * pL) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hK1μℓ]
        calc pL * D ≤ pL * (K10 * (2 + kap) * μ * ℓ ^ 3 * pL) :=
              mul_le_mul_of_nonneg_left hDbound hpL
          _ ≤ K10 * (kap + 2) * μ * ℓ ^ 3 * pL ^ 2 := by
              have h5 : (2 + kap) * μ * ℓ ^ 3 * pL * pL
                  ≤ (kap + 2) * μ * ℓ ^ 3 * pL ^ 2 := by
                nlinarith [hpL, mul_nonneg hμ.le (pow_nonneg hℓpos.le 3)]
              linarith [h5]
      calc Real.sqrt (pL * D) ≤ Real.sqrt ((Real.sqrt (K10 * (kap + 2) * μ * ℓ ^ 3) * pL) ^ 2) :=
            Real.sqrt_le_sqrt harg
        _ = Real.sqrt (K10 * (kap + 2) * μ * ℓ ^ 3) * pL :=
            Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hpL)
    have hsum : Real.sqrt (pL * (pL + D)) ≤ (pL + Real.sqrt (K10 * (kap + 2) * μ * ℓ ^ 3) * pL) := by
      linarith [hsqrt, h2']
    rw [hAdef]
    have hsplit : Real.sqrt (pL * (pL + D) / ℓ ^ 3)
        = Real.sqrt (pL * (pL + D)) * ℓ ^ (-(3 / 2) : ℝ) := by
      have hsq : (ℓ ^ (-(3 / 2) : ℝ)) ^ 2 = (ℓ ^ 3)⁻¹ := by
        rw [sq, ← Real.rpow_add hℓpos]
        norm_num
      have hXD : 0 ≤ pL * (pL + D) := mul_nonneg hpL (by linarith [hD0])
      calc Real.sqrt (pL * (pL + D) / ℓ ^ 3)
          = Real.sqrt (pL * (pL + D) * (ℓ ^ (-(3 / 2) : ℝ)) ^ 2) := by
              rw [hsq, div_eq_mul_inv]
        _ = Real.sqrt (pL * (pL + D)) * Real.sqrt ((ℓ ^ (-(3 / 2) : ℝ)) ^ 2) := by
              rw [Real.sqrt_mul hXD]
        _ = Real.sqrt (pL * (pL + D)) * ℓ ^ (-(3 / 2) : ℝ) := by
              rw [Real.sqrt_sq (Real.rpow_nonneg hℓpos.le _)]
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg hℓpos.le _)
  have hmain : 2 * ((n : ℝ) ^ 2 * (εpair * A)) ≤ Ccoef * μ * a * pL := by
    have h1 : 2 * ((n : ℝ) ^ 2 * (εpair * A)) ≤ 2 * ((4 * μ ^ 2 * ℓ ^ 6) * (εpair * A)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      exact mul_le_mul_of_nonneg_right hn2 (mul_nonneg hεpair0 hA0)
    refine h1.trans ?_
    have h2 : (4 * μ ^ 2 * ℓ ^ 6) * (εpair * A)
        ≤ 4 * μ ^ 2 * ℓ ^ 6 * (εpair * ((pL + Real.sqrt (K10 * (kap + 2) * μ * ℓ ^ 3) * pL)
            * ℓ ^ (-(3 / 2) : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hsl hεpair0
    refine (mul_le_mul_of_nonneg_left h2 (by norm_num)).trans ?_
    have hcollapse : 2 * (4 * μ ^ 2 * ℓ ^ 6
          * (εpair * ((pL + Real.sqrt (K10 * (kap + 2) * μ * ℓ ^ 3) * pL)
            * ℓ ^ (-(3 / 2) : ℝ))))
        = 8 * (imagesCimg * (32 * Real.pi * Real.sqrt a) * Real.sqrt Cwin0)
            * ((R / ℓ) ^ 6 * μ ^ 2 * ℓ ^ ((9 : ℝ) / 2)
              * (1 + Real.sqrt (K10 * (kap + 2)) * Real.sqrt (μ * ℓ ^ 3))) * pL := by
      have h9 : ℓ ^ ((9 : ℝ) / 2) = ℓ ^ (6 : ℕ) * ℓ ^ (-(3 / 2) : ℝ) := by
        rw [show ((9 : ℝ) / 2) = (((6 : ℕ) : ℝ)) + (-(3 / 2)) by norm_num,
          Real.rpow_add hℓpos, Real.rpow_natCast]
      rw [hεpairdef, h9,
        show Real.sqrt (K10 * (kap + 2) * μ * ℓ ^ 3)
            = Real.sqrt (K10 * (kap + 2)) * Real.sqrt (μ * ℓ ^ 3) by
          rw [show K10 * (kap + 2) * μ * ℓ ^ 3 = (K10 * (kap + 2)) * (μ * ℓ ^ 3) by ring,
            Real.sqrt_mul hK1]]
      ring
    rw [hcollapse]
    have hEXTRA : 0 ≤ 8 * (imagesCimg * (32 * Real.pi * Real.sqrt a) * Real.sqrt Cwin0) := by
      refine mul_nonneg (by norm_num) ?_
      exact mul_nonneg (mul_nonneg imagesCimg_nonneg (mul_nonneg (by positivity)
        (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)
    have harith := imagesWordArith (α := a) (R := R) (kk := Real.sqrt (K10 * (kap + 2)))
      (μ := μ) ha0 hμ (Real.sqrt_nonneg _) ht1
    have h4 : 8 * (imagesCimg * (32 * Real.pi * Real.sqrt a) * Real.sqrt Cwin0)
          * ((R / ℓ) ^ 6 * μ ^ 2 * ℓ ^ ((9 : ℝ) / 2)
            * (1 + Real.sqrt (K10 * (kap + 2)) * Real.sqrt (μ * ℓ ^ 3))) * pL
        ≤ 8 * (imagesCimg * (32 * Real.pi * Real.sqrt a) * Real.sqrt Cwin0)
          * (R ^ 6 * a ^ (-(11 / 2) : ℝ) * (1 + Real.sqrt (K10 * (kap + 2))) * (μ * a))
          * pL := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left harith hEXTRA) hpL
    refine h4.trans (le_of_eq ?_)
    rw [hCcoefdef]; ring
  -- ## 9. the `errKafz` comparison
  have hkafz := errKafz_ge (v := v) (R := R) (μ := μ) (C := 2 * Ccoef + 1) hμ hav (by linarith)
  have hfinal : Ccoef * μ * a * pL
      ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ (2 * Ccoef + 1) * pL := by
    have h1 : (1 / 2) * ((2 * Ccoef + 1) * μ * a)
        ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ (2 * Ccoef + 1) :=
      mul_le_mul_of_nonneg_left hkafz (by norm_num)
    have h2 : Ccoef * μ * a ≤ (1 / 2) * ((2 * Ccoef + 1) * μ * a) := by
      nlinarith [hCcoef0, hμ.le, ha0.le]
    calc Ccoef * μ * a * pL = (Ccoef * μ * a) * pL := by ring
      _ ≤ ((1 / 2) * ((2 * Ccoef + 1) * μ * a)) * pL := mul_le_mul_of_nonneg_right h2 hpL
      _ ≤ ((1 / 2) * Work.BoseFixR.errKafz v R μ (2 * Ccoef + 1)) * pL :=
          mul_le_mul_of_nonneg_right h1 hpL
      _ = (1 / 2) * Work.BoseFixR.errKafz v R μ (2 * Ccoef + 1) * pL := by ring
  exact htotal.trans (hmain.trans hfinal)

end Work.BoseBoxFock
