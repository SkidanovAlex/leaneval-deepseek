import Mathlib
import Submission.Work.BMF.mr_core_defs
import Submission.Work.BMF.mr_direct.buchstab_set
import Submission.Work.BMF.mr_core.badPartCell
import Submission.Work.BMF.mr_core.badPart_le2_eventual
import Submission.Work.BMF.mr_core.badPart_le2_B0
import Submission.Work.BMF.mr_core.badPart_le2_pieceA
import Submission.Work.BMF.mr_core.badPart_le2_pieceB
import Submission.Work.BMF.mr_core.badPart_le2_helpers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 3200000

open MeasureTheory intervalIntegral Filter
open scoped BigOperators

namespace Work.BMF.mr_core

theorem badPart_le2 (ε C₀ θ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hC₀ : 0 < C₀)
    (hθ₀ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ B₀ : ℝ, 0 < B₀ ∧
      ∀ B : ℝ, max B₀ (1000 / ε) ≤ B →
      ∃ W₀ : ℝ, 0 < W₀ ∧
      ∀ W : ℝ, W₀ ≤ W →
      ∀ᶠ Y in Filter.atTop, ∀ (g : ℕ → ℂ) (H T : ℝ),
        g 1 = 1 →
        (∀ m n : ℕ, m.Coprime n → g (m * n) = g m * g n) → (∀ n, ‖g n‖ ≤ 1) →
        Y ^ θ ≤ H → H ≤ Y → 3 ≤ T → Y / H ≤ T → T ≤ 2 * C₀ / ε * (Y / H) →
        (∑ p ∈ Work.BMF.primesIn (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y),
            1 / (p : ℝ)) ≤ B ^ 2 / 16 →
        (∀ u : ℝ, |u| ≤ W * Y / H →
          B ≤ BoundedMultiplicativeFunctions.𝔻 g (fun n ↦ (n : ℂ) ^ (Complex.I * u)) Y) →
        (Y / H) / T * (∫ t in Work.BMF.mrCore.badSet ε g Y (2 * T),
            ‖Work.BMF.dirPolyD g Y t‖ ^ 2) ≤ ε / 8 := by
  obtain ⟨Cbs, hCbs_pos, hCbs⟩ := Work.BMF.mr_direct.buchstab_set
  obtain ⟨Cm, hCm_pos, hCm⟩ := Work.BMF.mr_core.badPartCell ε C₀ θ hε hε1 hC₀ hθ₀ hθ₁
  obtain ⟨Clow, hClow_pos, hClow⟩ := badPart_le2_invPrimes_lower
  set D : ℝ := 3 + 4 * C₀ / ε with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  set K : ℝ := max 4 (192 * Cbs * D / ε + 1) with hKdef
  have hK4 : 4 ≤ K := le_max_left _ _
  have hK1 : 1 ≤ K := by linarith
  have hKpos : 0 < K := by linarith
  have hKbig : 192 * Cbs * D / ε ≤ K := by
    have := le_max_right (4 : ℝ) (192 * Cbs * D / ε + 1); linarith
  obtain ⟨B₀', hB₀'pos, hB₀'⟩ :=
    badPart_le2_B0 ε C₀ K Cbs Cm 1 hε hC₀ hKpos hCbs_pos hCm_pos (by norm_num)
  set B₀ : ℝ := max (max B₀' 1)
      (max (12800 * 96 * Cbs * D / ε + 1) (256 * Clow + 1)) with hB₀def
  have hB₀pos : 0 < B₀ := by
    rw [hB₀def]
    refine lt_of_lt_of_le ?_ (le_max_left _ _)
    exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_right _ _)
  refine ⟨B₀, hB₀pos, ?_⟩
  intro B hB
  have hBB₀ : B₀ ≤ B := le_trans (le_max_left _ _) hB
  have hB1000 : 1000 / ε ≤ B := le_trans (le_max_right _ _) hB
  have hB₀'le : B₀' ≤ B := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hBB₀)
  have hB1 : (1:ℝ) ≤ B := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hBB₀)
  have hBx1 : 12800 * 96 * Cbs * D / ε + 1 ≤ B :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hBB₀)
  have hBx2 : 256 * Clow + 1 ≤ B :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hBB₀)
  obtain ⟨hB8, hBfree, _hBcp⟩ := hB₀' B hB₀'le
  have hBpos : 0 < B := by linarith
  have hB2big : 12800 * 96 * Cbs * D / ε ≤ B ^ 2 := by
    have h1 : 12800 * 96 * Cbs * D / ε ≤ B := by linarith
    have h2 : B ≤ B ^ 2 := by nlinarith only [hB1, hBpos]
    linarith
  have hBClow : 256 * Clow ≤ B ^ 2 := by
    have h1 : 256 * Clow ≤ B := by linarith
    have h2 : B ≤ B ^ 2 := by nlinarith only [hB1, hBpos]
    linarith
  have hBcop : 12800 * Cbs * D / B ^ 2 ≤ ε / 96 := by
    have h2 : 12800 * 96 * Cbs * D ≤ ε * B ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hB2big hε.le
      rwa [mul_div_cancel₀ (12800 * 96 * Cbs * D) (ne_of_gt hε)] at h
    rw [div_le_iff₀ (by positivity : (0:ℝ) < B ^ 2)]
    nlinarith only [h2]
  have hAc1 : 1 ≤ Work.BMF.mrCore.Ac B := by
    rw [Work.BMF.mrCore.Ac]; exact Real.one_le_exp (by positivity)
  have hAcpos : 0 < Work.BMF.mrCore.Ac B := lt_of_lt_of_le zero_lt_one hAc1
  refine ⟨max 4 (max (8 * C₀ / ε) (256 * Cbs * Cm * K ^ 2 * (Work.BMF.mrCore.Ac B) ^ 4 / ε)),
      by positivity, ?_⟩
  intro W hW
  have hW4 : 4 ≤ W := le_trans (le_max_left _ _) hW
  have hW8C : 8 * C₀ / ε ≤ W := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hW)
  have hWbig : 256 * Cbs * Cm * K ^ 2 * (Work.BMF.mrCore.Ac B) ^ 4 / ε ≤ W :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hW)
  have hWpos : 0 < W := by linarith
  filter_upwards [badPart_le2_eventual ε C₀ θ K W Cbs Cm B hε hC₀ hθ₀ hθ₁ hK4 hW4 hCbs_pos hCm_pos,
      hClow B hBClow, hCm B hB1000 K hK4] with Y hEV hSlow hCellY
  obtain ⟨hY16, hPc2, hQcY, hQc2, hPcinv, hlogYmax, hEA, hEB, hEC⟩ := hEV
  intro g H T hg1 hgmul hgbd hHθ hHY hT3 hTH hTT hprimes hdist
  have hY1 : (1:ℝ) ≤ Y := by linarith
  have hYpos : (0:ℝ) < Y := by linarith
  have hPcpos : (0:ℝ) < Work.BMF.mrCore.Pc Y := by linarith
  have hPc1 : (1:ℝ) < Work.BMF.mrCore.Pc Y := by linarith
  have hH1 : (1:ℝ) ≤ H := le_trans (Real.one_le_rpow hY1 hθ₀.le) hHθ
  have hHpos : (0:ℝ) < H := by linarith
  have hTpos : (0:ℝ) < T := by linarith
  have hYHnn : 0 ≤ Y / H := by positivity
  have hYH1 : 1 ≤ Y / H := (le_div_iff₀ hHpos).mpr (by linarith)
  have hlogYpos : (0:ℝ) < Real.log Y := Real.log_pos (by linarith)
  have hlogYnn : 0 ≤ Real.log Y := le_of_lt hlogYpos
  have hlogPcpos : (0:ℝ) < Work.BMF.mrCore.logPc Y := by
    rw [Work.BMF.mrCore.logPc]
    exact Real.rpow_pos_of_pos hlogYpos _
  have hPcleQc : Work.BMF.mrCore.Pc Y ≤ Work.BMF.mrCore.Qc B Y := by
    rw [Work.BMF.mrCore.Pc, Work.BMF.mrCore.Qc]
    apply Real.exp_le_exp.mpr
    rw [Work.BMF.mrCore.logQc]
    nlinarith [hlogPcpos, hAc1]
  have hlogPcY : Real.log (Work.BMF.mrCore.Pc Y) = Work.BMF.mrCore.logPc Y := by
    rw [Work.BMF.mrCore.Pc, Real.log_exp]
  have hQcpos : (0:ℝ) < Work.BMF.mrCore.Qc B Y := by
    rw [Work.BMF.mrCore.Qc]; exact Real.exp_pos _
  have hlogQcY : Real.log (Work.BMF.mrCore.Qc B Y) = Work.BMF.mrCore.logQc B Y := by
    rw [Work.BMF.mrCore.Qc, Real.log_exp]
  have hlogdiv : Real.log (Work.BMF.mrCore.Qc B Y / Work.BMF.mrCore.Pc Y)
      = (Work.BMF.mrCore.Ac B - 1) * Work.BMF.mrCore.logPc Y := by
    rw [Real.log_div (ne_of_gt hQcpos) (ne_of_gt hPcpos), hlogQcY, hlogPcY,
      Work.BMF.mrCore.logQc]
    ring
  set T₀ : ℝ := W * Y / (4 * H) with hT₀def
  have hT₀pos : 0 < T₀ := by rw [hT₀def]; positivity
  have hT₀1 : 1 ≤ T₀ := by
    have hW4 : 1 ≤ W / 4 := by linarith
    calc (1:ℝ) = 1 * 1 := by ring
      _ ≤ W / 4 * (Y / H) := mul_le_mul hW4 hYH1 zero_le_one (by positivity)
      _ = T₀ := by rw [hT₀def]; ring
  have hTleT₀ : T ≤ T₀ := by
    have hid : (8 * C₀) / ε = 4 * (2 * C₀ / ε) := by ring
    have hW4' : 2 * C₀ / ε ≤ W / 4 := by linarith [hW8C, hid]
    calc T ≤ 2 * C₀ / ε * (Y / H) := hTT
      _ ≤ W / 4 * (Y / H) := mul_le_mul_of_nonneg_right hW4' hYHnn
      _ = T₀ := by rw [hT₀def]; ring
  have h4T₀ : 4 * T₀ = W * Y / H := by rw [hT₀def]; ring
  have hT₀inv : 1 / T₀ ≤ 4 / W := by
    have hWne : W ≠ 0 := ne_of_gt hWpos
    have hYne : Y ≠ 0 := ne_of_gt hYpos
    have hHne : H ≠ 0 := ne_of_gt hHpos
    have h1 : 1 / T₀ = 4 * H / (W * Y) := by
      rw [hT₀def]; field_simp
    rw [h1, div_le_div_iff₀ (by positivity : (0:ℝ) < W * Y) hWpos]
    nlinarith
  set A0 : ℝ := K * (Work.BMF.mrCore.Ac B - 1) * Work.BMF.mrCore.logPc Y with hA0def
  have hA0nn : 0 ≤ A0 := by
    rw [hA0def]
    exact mul_nonneg (mul_nonneg hKpos.le (by linarith)) hlogPcpos.le
  set u : Set ℝ := Work.BMF.mrCore.badSet ε g Y (2 * T) with hudef
  have hu_meas : MeasurableSet u := Work.BMF.mrCore.measurableSet_badSet ε g Y (2 * T)
  have hu_sub : u ⊆ Set.Icc (-(2 * T)) (2 * T) :=
    Work.BMF.mrCore.badSet_subset_Icc ε g Y (2 * T)
  have hmulgg : ∀ m p : ℕ, Nat.Prime p → Work.BMF.mrCore.Pc Y ≤ (p : ℝ) →
      (p : ℝ) ≤ Work.BMF.mrCore.Qc B Y → ¬ p ∣ m → g (m * p) = g m * g p := by
    intro m p hp h1 h2 hndvd
    exact hgmul m p (hp.coprime_iff_not_dvd.mpr hndvd).symm
  set Scop : ℝ := ∑ n ∈ (Work.BMF.natIcc Y (3 * Y)).filter
      (fun n => n.Coprime (∏ p ∈ Work.BMF.primesIn (Work.BMF.mrCore.Pc Y)
        (Work.BMF.mrCore.Qc B Y), p)), ‖g n‖ ^ 2 / (n : ℝ) with hScopdef
  have hScopnn : 0 ≤ Scop := by rw [hScopdef]; positivity
  have hbs := hCbs Y (3 * Y) K (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y) (2 * T) g g g u
      hY1 (by linarith) (by linarith) hK1 hPc2 hPcleQc (by linarith) hu_meas hu_sub
      hgbd hgbd hgbd hmulgg
  set RHS : ℝ := Cm * (Work.BMF.mrCore.Ac B) ^ 2 *
            (((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀) *
              (Real.log Y) ^ (-(47 / 24 : ℝ)))
          + Cm * Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)) with hRHSdef
  have hRSHnn : 0 ≤ RHS := by
    rw [hRHSdef]
    have hp1 : 0 ≤ (Real.log Y) ^ (-(47 / 24 : ℝ)) := Real.rpow_nonneg hlogYnn _
    have hp2 : 0 ≤ (Real.log Y) ^ (-(199 : ℝ)) := Real.rpow_nonneg hlogYnn _
    have hlog2T : 0 ≤ Real.log (2 * T) := Real.log_nonneg (by linarith)
    have hbrack : 0 ≤ (1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀ := by positivity
    have h1 : 0 ≤ Cm * (Work.BMF.mrCore.Ac B) ^ 2 *
        (((1 + B ^ 2) ^ 2 * Real.exp (-(B ^ 2 / 4)) + 1 / T₀) *
          (Real.log Y) ^ (-(47 / 24 : ℝ))) :=
      mul_nonneg (mul_nonneg hCm_pos.le (pow_nonneg hAcpos.le _)) (mul_nonneg hbrack hp1)
    have h2 : 0 ≤ Cm * Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)) :=
      mul_nonneg (mul_nonneg hCm_pos.le hlog2T) hp2
    linarith
  set s : Finset ℕ := Work.BMF.mrDirect.indexSet K (Work.BMF.mrCore.Pc Y)
      (Work.BMF.mrCore.Qc B Y) with hsdef
  have hcell : ∀ j ∈ s,
      (∫ t in u, ‖Work.BMF.mrDirect.primePoly g K j t *
          Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
            K Y (3 * Y) j t‖ ^ 2) ≤ RHS := by
    intro j hj
    rw [hsdef] at hj
    rw [hRHSdef]
    exact hCellY T₀ g H T j hT₀1 hg1 hgmul hgbd
      hPc2 hQcY hprimes (fun u hu => hdist u (by rw [← h4T₀]; exact hu))
      hHθ hHY hT3 hTH hTleT₀ hTT hj
  have hcard : ((s.card : ℝ)) ≤ A0 + 2 := by
    have h := Work.BMF.mr_direct.indexSet_card_le' K (Work.BMF.mrCore.Pc Y)
      (Work.BMF.mrCore.Qc B Y) hKpos hPc1 hPcleQc
    have haeq : K * Real.log (Work.BMF.mrCore.Qc B Y / Work.BMF.mrCore.Pc Y) = A0 := by
      rw [hA0def, hlogdiv]; ring
    rw [hsdef]
    linarith [h, haeq]
  have hsum : (∑ j ∈ s, ∫ t in u, ‖Work.BMF.mrDirect.primePoly g K j t *
          Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
            K Y (3 * Y) j t‖ ^ 2) ≤ (A0 + 2) * RHS := by
    calc (∑ j ∈ s, _) ≤ (s.card : ℝ) * RHS := by
          calc (∑ j ∈ s, _) ≤ ∑ j ∈ s, RHS := Finset.sum_le_sum hcell
            _ = (s.card : ℝ) * RHS := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (A0 + 2) * RHS := mul_le_mul_of_nonneg_right hcard hRSHnn
  have hlogdivnn : 0 ≤ Real.log (Work.BMF.mrCore.Qc B Y / Work.BMF.mrCore.Pc Y) :=
    Real.log_nonneg ((one_le_div hPcpos).mpr hPcleQc)
  have haeq2 : K * Real.log (Work.BMF.mrCore.Qc B Y / Work.BMF.mrCore.Pc Y) = A0 := by
    rw [hA0def, hlogdiv]; ring
  have hnn2 : 0 ≤ 1 / K + 1 / Work.BMF.mrCore.Pc Y + Scop := by
    have h1 : 0 ≤ 1 / Work.BMF.mrCore.Pc Y := by positivity
    have h2 : 0 ≤ 1 / K := by positivity
    linarith
  set E : ℝ := 1 / K + 1 / Work.BMF.mrCore.Pc Y + Scop with hEdef
  have h1 : K * Real.log (Work.BMF.mrCore.Qc B Y / Work.BMF.mrCore.Pc Y) *
        (∑ j ∈ s, ∫ t in u, ‖Work.BMF.mrDirect.primePoly g K j t *
          Work.BMF.mrDirect.remPolyR g (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y)
            K Y (3 * Y) j t‖ ^ 2) ≤ A0 * ((A0 + 2) * RHS) := by
    rw [haeq2]
    exact mul_le_mul_of_nonneg_left hsum hA0nn
  have h2 : (2 * T + 3 * Y) / Y * E ≤ D * E := by
    refine mul_le_mul_of_nonneg_right ?_ (by rw [hEdef]; exact hnn2)
    rw [hDdef]
    exact badPart_le2_div_le C₀ ε θ Y H T hε hC₀ hθ₀ hY1 hHθ hHY hTT
  have hmaster : (∫ t in u, ‖Work.BMF.dirPolyD g Y t‖ ^ 2)
      ≤ Cbs * (A0 * ((A0 + 2) * RHS) + D * E) := by
    have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hCbs_pos.le
    refine le_trans hbs ?_
    simpa only [hScopdef, hEdef] using h3
  set Xa : ℝ := Cm * (Work.BMF.mrCore.Ac B) ^ 2 * ((1 + B ^ 2) ^ 2 *
      Real.exp (-(B ^ 2 / 4)) * (Real.log Y) ^ (-(47 / 24 : ℝ))) with hXadef
  set Xb : ℝ := Cm * (Work.BMF.mrCore.Ac B) ^ 2 * ((1 / T₀) *
      (Real.log Y) ^ (-(47 / 24 : ℝ))) with hXbdef
  set Z : ℝ := Cm * Real.log (2 * T) * (Real.log Y) ^ (-(199 : ℝ)) with hZdef
  have hRHSsplit : RHS = Xa + Xb + Z := by
    rw [hRHSdef, hXadef, hXbdef, hZdef]; ring
  have hA : Cbs * A0 * (A0 + 2) * Xa ≤ ε / 32 := by
    rw [hA0def, hXadef]
    exact badPart_le2_pieceA ε Cbs Cm K (Work.BMF.mrCore.Ac B) B Y hε hCbs_pos hCm_pos
      (by linarith) hAc1 hY1 hBfree hEB
  have hB : Cbs * A0 * (A0 + 2) * Xb ≤ ε / 32 := by
    rw [hA0def, hXbdef]
    refine badPart_le2_pieceB ε Cbs Cm K (Work.BMF.mrCore.Ac B) B Y W T₀ hε hCbs_pos hCm_pos
      (by linarith) hAc1 hY1 hWpos hT₀inv ?_ hEC
    have h2 : 256 * Cbs * Cm * K ^ 2 * (Work.BMF.mrCore.Ac B) ^ 4 ≤ ε * W := by
      have h := mul_le_mul_of_nonneg_left hWbig hε.le
      rwa [mul_div_cancel₀ (256 * Cbs * Cm * K ^ 2 * (Work.BMF.mrCore.Ac B) ^ 4)
        (ne_of_gt hε)] at h
    rw [div_le_iff₀ hWpos]
    nlinarith only [h2]
  have hC : Cbs * A0 * (A0 + 2) * Z ≤ ε / 32 := by
    rw [hA0def, hZdef]
    refine badPart_le2_pieceC ε Cbs Cm K (Work.BMF.mrCore.Ac B) B Y T hε hCbs_pos hCm_pos
      (by linarith) hAc1 hY1 hTpos ?_ hEA
    have hlog4 : Real.log (4 * C₀ / ε) ≤ Real.log Y := le_trans (le_max_right _ _) hlogYmax
    have h4pos : 0 < 4 * C₀ / ε := by positivity
    have h2T : 2 * T ≤ (4 * C₀ / ε) * Y := by
      calc 2 * T ≤ 2 * (2 * C₀ / ε * (Y / H)) := by linarith
        _ = (4 * C₀ / ε) * (Y / H) := by ring
        _ ≤ (4 * C₀ / ε) * Y := by
              refine mul_le_mul_of_nonneg_left ?_ h4pos.le
              rw [div_le_iff₀ hHpos]
              simpa using mul_le_mul_of_nonneg_left hH1 hYpos.le
    calc Real.log (2 * T) ≤ Real.log ((4 * C₀ / ε) * Y) :=
          Real.log_le_log (by linarith) h2T
      _ = Real.log (4 * C₀ / ε) + Real.log Y := Real.log_mul (ne_of_gt h4pos) (ne_of_gt hYpos)
      _ ≤ 2 * Real.log Y := by linarith
  have hD1 : Cbs * D / K ≤ ε / 96 := by
    have hKD : 192 * Cbs * D ≤ ε * K := by
      have h := mul_le_mul_of_nonneg_left hKbig hε.le
      rwa [mul_div_cancel₀ (192 * Cbs * D) (ne_of_gt hε)] at h
    rw [div_le_iff₀ hKpos]
    nlinarith only [hKD, hKpos, hCbs_pos, hDpos]
  have hD2 : Cbs * D / Work.BMF.mrCore.Pc Y ≤ ε / 96 := by
    have h1 : Cbs * D * (1 / Work.BMF.mrCore.Pc Y) ≤ Cbs * D * (ε / (96 * Cbs * D)) :=
      mul_le_mul_of_nonneg_left hPcinv (by positivity)
    have heq : Cbs * D * (ε / (96 * Cbs * D)) = ε / 96 := by
      field_simp
      try ring
    have h2 : Cbs * D / Work.BMF.mrCore.Pc Y = Cbs * D * (1 / Work.BMF.mrCore.Pc Y) := by
      ring
    linarith [h1, heq, h2]
  have hB1000'' : (1000:ℝ) ≤ B := by
    have h1 : 1 ≤ 1 / ε := (one_le_div hε).mpr hε1
    have h2 : (1000:ℝ) ≤ 1000 * (1 / ε) := by
      calc (1000:ℝ) = 1000 * 1 := by ring
        _ ≤ 1000 * (1 / ε) := mul_le_mul_of_nonneg_left h1 (by norm_num)
    have h3 : 1000 * (1 / ε) = 1000 / ε := by ring
    linarith only [h2, h3, hB1000]
  set Sp : ℝ := ∑ p ∈ Work.BMF.primesIn (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y),
      1 / (p : ℝ) with hSpdef
  have hSlow' : B ^ 2 / 128 ≤ Sp := hSlow
  have hSpos : 0 < Sp := by nlinarith only [hSlow', hB1000'']
  have hS1 : 1 ≤ Sp := by nlinarith only [hSlow', hB1000'']
  have hScop_le : Scop ≤ 12800 / B ^ 2 := by
    have hsum1 : Scop ≤ ∑ n ∈ (Work.BMF.natIcc Y (3 * Y)).filter
        (fun n => n.Coprime (∏ p ∈ Work.BMF.primesIn (Work.BMF.mrCore.Pc Y)
          (Work.BMF.mrCore.Qc B Y), p)), 1 / (n : ℝ) := by
      rw [hScopdef]
      refine Finset.sum_le_sum (fun n hn => ?_)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        have hy : (0:ℝ) ≤ 3 * Y := by linarith
        have := (Work.BMF.mrDirect.mem_natIcc hy).mp (Finset.mem_filter.mp hn).1
        linarith only [this.1, hY1]
      have hgn : ‖g n‖ ^ 2 ≤ 1 := by
        have := hgbd n
        nlinarith only [this, norm_nonneg (g n)]
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (n:ℝ)) (by positivity : (0:ℝ) < (n:ℝ))]
      nlinarith only [hgn]
    have hcr := badPart_le2_coprime_recip (Work.BMF.mrCore.Pc Y) (Work.BMF.mrCore.Qc B Y) Y (3 * Y)
      hPc2 hPcleQc hY1 (by linarith) (by linarith) hQc2 hS1
    have hfin : 100 / Sp ≤ 12800 / B ^ 2 := by
      rw [div_le_div_iff₀ hSpos (by positivity : (0:ℝ) < B ^ 2)]
      nlinarith only [hSlow']
    linarith only [hsum1, hcr, hfin]
  have hD3 : Cbs * D * Scop ≤ ε / 96 := by
    have h1 : Cbs * D * Scop ≤ Cbs * D * (12800 / B ^ 2) :=
      mul_le_mul_of_nonneg_left hScop_le (by positivity)
    have h2 : Cbs * D * (12800 / B ^ 2) = 12800 * Cbs * D / B ^ 2 := by ring
    linarith only [h1, h2, hBcop]
  have hDp : Cbs * D * E ≤ ε / 32 := by
    rw [hEdef]
    exact badPart_le2_pieceD ε Cbs K (Work.BMF.mrCore.Pc Y) Scop D hε hCbs_pos hKpos hPcpos
      hScopnn hDpos.le hD1 hD2 hD3
  have hfinal : (∫ t in u, ‖Work.BMF.dirPolyD g Y t‖ ^ 2) ≤ ε / 8 := by
    refine le_trans hmaster ?_
    have hkey : Cbs * (A0 * ((A0 + 2) * RHS) + D * E)
        = Cbs * A0 * (A0 + 2) * Xa + Cbs * A0 * (A0 + 2) * Xb
          + Cbs * A0 * (A0 + 2) * Z + Cbs * D * E := by
      rw [hRHSsplit]; ring
    rw [hkey]
    linarith only [hA, hB, hC, hDp]
  have hYHdiv : (Y / H) / T ≤ 1 := by
    rw [div_le_one hTpos]
    exact hTH
  have hIntnn : 0 ≤ ∫ t in u, ‖Work.BMF.dirPolyD g Y t‖ ^ 2 :=
    MeasureTheory.integral_nonneg (fun t => by positivity)
  calc (Y / H) / T * (∫ t in u, ‖Work.BMF.dirPolyD g Y t‖ ^ 2)
      ≤ 1 * (ε / 8) := mul_le_mul hYHdiv hfinal hIntnn zero_le_one
    _ = ε / 8 := by ring

end Work.BMF.mr_core
