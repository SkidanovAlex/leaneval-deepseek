import Mathlib
import Submission.Work.BMF.zeta_growth_defs
import Submission.Work.BMF.zeta_offline_bound
import Submission.Work.BMF.zeta_bdd_height

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.zpt

set_option maxHeartbeats 1200000

/-- Assembly of the strip growth bound for `ζ` from the Vinogradov–Korobov partial-sum
bound, the approximate functional equation on `σ ≥ 15/16`, an elementary off-line bound
and boundedness of `ζ` on a bounded slice. -/
theorem zeta_growth_strip
    (hVK : ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ Work.BMF.VKExpSum C D)
    (hPSB : ∀ (C D : ℝ), 0 < C → 0 < D → Work.BMF.VKExpSum C D →
      ∃ A : ℝ, 0 < A ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ < 1 → 3 ≤ |t| →
        ‖∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ ≤
          A * |t| ^ ((2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ)) *
            (Real.log |t|) ^ (2 / 3 : ℝ))
    (hAFE : ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ σ t : ℝ, 15 / 16 ≤ σ → σ ≤ 1 → T₀ ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) -
        ∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ ≤ C) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ < 1 → 3 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) * (Real.log (|t| + 3)) ^ (2 / 3 : ℝ) := by
  obtain ⟨C, D, hC, hD, hVK'⟩ := hVK
  obtain ⟨Apsb, hApsbpos, hApsbb⟩ := hPSB C D hC hD hVK'
  obtain ⟨Cafe, T0, hCafepos, hT0pos, hAFEb⟩ := hAFE
  obtain ⟨Aoff, hAoffpos, hAoffb⟩ := Work.BMF.zeta_offline_bound
  obtain ⟨Ah, hAhpos, hAhb⟩ :=
    Work.BMF.zeta_bdd_height (max T0 3)
      (le_trans (by norm_num : (1 : ℝ) ≤ 3) (le_max_right T0 3))
  set L : ℝ := (Real.log 6) ^ (2 / 3 : ℝ) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; exact Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _
  set B : ℝ := max ((2 / 9) * Real.sqrt (3 * D)) 4 with hBdef
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hc_le_B : (2 / 9) * Real.sqrt (3 * D) ≤ B := le_max_left _ _
  have h4_le_B : (4 : ℝ) ≤ B := le_max_right _ _
  have hcnn : 0 ≤ (2 / 9) * Real.sqrt (3 * D) := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  set A : ℝ := (Aoff + Ah + 2 * Cafe + 2) / L + Apsb + 1 with hAdef
  have hApos : 0 < A := by
    have hnum : 0 < Aoff + Ah + 2 * Cafe + 2 := by linarith [hAoffpos, hAhpos, hCafepos]
    have h1 : 0 < (Aoff + Ah + 2 * Cafe + 2) / L := div_pos hnum hLpos
    rw [hAdef]; linarith [hApsbpos]
  have hAminus : A - Apsb = (Aoff + Ah + 2 * Cafe + 2) / L + 1 := by rw [hAdef]; ring
  have hAminuspos : 0 < A - Apsb := by
    rw [hAminus]
    have hnum : 0 < Aoff + Ah + 2 * Cafe + 2 := by linarith [hAoffpos, hAhpos, hCafepos]
    have := div_pos hnum hLpos
    linarith
  have hAminL : 2 * Cafe + 2 ≤ (A - Apsb) * L := by
    rw [hAminus, add_mul, div_mul_cancel₀ _ (ne_of_gt hLpos), one_mul]
    linarith [hAoffpos, hAhpos, hLpos]
  have hAL : Aoff + Ah + 2 * Cafe + 2 ≤ A * L := by
    have hLne : L ≠ 0 := ne_of_gt hLpos
    have hAle : (Aoff + Ah + 2 * Cafe + 2) / L ≤ A := by rw [hAdef]; linarith [hApsbpos]
    have := mul_le_mul_of_nonneg_right hAle (le_of_lt hLpos)
    rwa [div_mul_cancel₀ _ hLne] at this
  refine ⟨A, B, hApos, hBpos, ?_⟩
  intro σ t hσ hσ1 ht
  set Pbase : ℝ := (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) with hPbasedef
  set Plog : ℝ := (Real.log (|t| + 3)) ^ (2 / 3 : ℝ) with hPlogdef
  have habs0 : 0 ≤ |t| := abs_nonneg t
  have ht1 : 1 ≤ |t| := by linarith
  have hbase1 : 1 ≤ |t| + 3 := by linarith
  have h1σnn : 0 ≤ (1 - σ) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hexpBnn : 0 ≤ B * (1 - σ) ^ (3 / 2 : ℝ) := mul_nonneg (le_of_lt hBpos) h1σnn
  have hlog6pos : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hlogbase : Real.log 6 ≤ Real.log (|t| + 3) := Real.log_le_log (by norm_num) (by linarith)
  have hlogtpos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hlogtnn : 0 ≤ Real.log |t| := le_of_lt hlogtpos
  have hlogpos : 0 < Real.log (|t| + 3) := Real.log_pos (by linarith)
  have hPsi_ge_L : L ≤ Plog := by
    rw [hPlogdef, hLdef]
    exact Real.rpow_le_rpow (le_of_lt hlog6pos) hlogbase (by norm_num)
  have hPbase1 : 1 ≤ Pbase := by
    rw [hPbasedef]; exact Real.one_le_rpow hbase1 hexpBnn
  have hPbase_pos : 0 < Pbase := lt_of_lt_of_le zero_lt_one hPbase1
  have hPlog_pos : 0 < Plog := lt_of_lt_of_le hLpos hPsi_ge_L
  have hPhiPsi : L ≤ Pbase * Plog := by
    have := mul_le_mul hPbase1 hPsi_ge_L (le_of_lt hLpos) (le_of_lt hPbase_pos)
    simpa using this
  have hAoff_le : Aoff ≤ A * Plog := by
    have h1 : Aoff ≤ A * L := by linarith [hAL, hAhpos, hCafepos]
    have h2 : A * L ≤ A * Plog := mul_le_mul_of_nonneg_left hPsi_ge_L (le_of_lt hApos)
    linarith
  have hAh_le : Ah ≤ A * Plog := by
    have h1 : Ah ≤ A * L := by linarith [hAL, hAoffpos, hCafepos]
    have h2 : A * L ≤ A * Plog := mul_le_mul_of_nonneg_left hPsi_ge_L (le_of_lt hApos)
    linarith
  by_cases hle : σ ≤ 15 / 16
  · have hoff := hAoffb σ t hσ (le_of_lt hσ1) ht (Or.inl hle)
    have hpow : |t| ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) ≤ Pbase := by
      rw [hPbasedef]
      have hexp4 : 4 * (1 - σ) ^ (3 / 2 : ℝ) ≤ B * (1 - σ) ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right h4_le_B h1σnn
      calc |t| ^ (4 * (1 - σ) ^ (3 / 2 : ℝ))
          ≤ (|t| + 3) ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) :=
            Real.rpow_le_rpow habs0 (by linarith) (mul_nonneg (by norm_num) h1σnn)
        _ ≤ (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hbase1 hexp4
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Aoff * |t| ^ (4 * (1 - σ) ^ (3 / 2 : ℝ)) := hoff
      _ ≤ Aoff * Pbase := mul_le_mul_of_nonneg_left hpow (le_of_lt hAoffpos)
      _ ≤ (A * Plog) * Pbase := mul_le_mul_of_nonneg_right hAoff_le (le_of_lt hPbase_pos)
      _ = A * Pbase * Plog := by ring
  · simp only [not_le] at hle
    by_cases hT : |t| ≤ max T0 3
    · have hb := hAhb σ t hσ (le_of_lt hσ1) ht hT
      calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Ah := hb
        _ ≤ A * Plog := hAh_le
        _ ≤ A * Pbase * Plog := by
            have hAPnn : 0 ≤ A * Plog := mul_nonneg (le_of_lt hApos) (le_of_lt hPlog_pos)
            have h : A * Plog ≤ A * Plog * Pbase := by
              simpa using mul_le_mul_of_nonneg_left hPbase1 hAPnn
            calc A * Plog ≤ A * Plog * Pbase := h
              _ = A * Pbase * Plog := by ring
    · simp only [not_le] at hT
      have hσ15 : 15 / 16 ≤ σ := le_of_lt hle
      have hT0le : T0 ≤ |t| := le_trans (le_max_left T0 3) (le_of_lt hT)
      have hafe := hAFEb σ t hσ15 (le_of_lt hσ1) hT0le
      have hpsb := hApsbb σ t hσ hσ1 ht
      set S : ℂ := ∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) with hSdef
      have htri : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - S‖ + ‖S‖ := by
        have h := norm_add_le (riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - S) S
        have heq : (riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - S) + S =
            riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) := by ring
        rwa [heq] at h
      have hlogt_le : (Real.log |t|) ^ (2 / 3 : ℝ) ≤ Plog := by
        rw [hPlogdef]
        exact Real.rpow_le_rpow hlogtnn
          (Real.log_le_log (by linarith : (0:ℝ) < |t|) (by linarith : |t| ≤ |t| + 3)) (by norm_num)
      have hpowc : |t| ^ ((2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ)) ≤ Pbase := by
        rw [hPbasedef]
        have hexpc : (2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ) ≤
            B * (1 - σ) ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_right hc_le_B h1σnn
        calc |t| ^ ((2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ))
            ≤ (|t| + 3) ^ ((2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ)) :=
              Real.rpow_le_rpow habs0 (by linarith) (mul_nonneg hcnn h1σnn)
          _ ≤ (|t| + 3) ^ (B * (1 - σ) ^ (3 / 2 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hbase1 hexpc
      have hprod : |t| ^ ((2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ)) *
            (Real.log |t|) ^ (2 / 3 : ℝ) ≤ Pbase * Plog :=
        mul_le_mul hpowc hlogt_le (Real.rpow_nonneg hlogtnn _) (le_of_lt hPbase_pos)
      have hCafe_leP : Cafe ≤ (A - Apsb) * (Pbase * Plog) := by
        have h2 : (A - Apsb) * L ≤ (A - Apsb) * (Pbase * Plog) :=
          mul_le_mul_of_nonneg_left hPhiPsi (le_of_lt hAminuspos)
        linarith [hAminL, h2]
      have hApsb_leP : Apsb * (|t| ^ ((2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ)) *
            (Real.log |t|) ^ (2 / 3 : ℝ)) ≤ Apsb * (Pbase * Plog) :=
        mul_le_mul_of_nonneg_left hprod (le_of_lt hApsbpos)
      have hcomb : Cafe + Apsb * (|t| ^ ((2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ)) *
            (Real.log |t|) ^ (2 / 3 : ℝ)) ≤ A * Pbase * Plog := by
        have he : (A - Apsb) * (Pbase * Plog) + Apsb * (Pbase * Plog) = A * Pbase * Plog := by ring
        linarith [hCafe_leP, hApsb_leP, he]
      calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) - S‖ + ‖S‖ := htri
        _ ≤ Cafe + Apsb * |t| ^ ((2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ)) *
              (Real.log |t|) ^ (2 / 3 : ℝ) := add_le_add hafe hpsb
        _ = Cafe + Apsb * (|t| ^ ((2 / 9) * Real.sqrt (3 * D) * (1 - σ) ^ (3 / 2 : ℝ)) *
              (Real.log |t|) ^ (2 / 3 : ℝ)) := by ring
        _ ≤ A * Pbase * Plog := hcomb

end Work.BMF.zpt
