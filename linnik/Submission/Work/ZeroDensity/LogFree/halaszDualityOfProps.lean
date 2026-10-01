import Mathlib
import Submission.Work.ZeroDensity.LogFree.halaszGramAux

open DirichletCharacter Complex Finset
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

open Work.ZeroDensity.LogFree.HalaszGram

set_option maxHeartbeats 4000000 in
/-- **L5 of `JUTILA_UNIFIED_LEAD.md` §3, assembled from the eight analytic inputs.** -/
theorem dualityOfProps (p : Params) (hA : MassBound p) (hQ : PoleResidueBound p)
    (hdet : DetectorBound p) (hcross : GramCross p) (hsame : GramSame p)
    (hls : PoleLargeSieve p) (htail : DetectorTruncation p) (hnear : NearLineCount p) :
    DualityCount p := by
  intro c₀ hc₀
  obtain ⟨c₁, hc₁, K, hK, Dnear, hDnear, hnear⟩ := hnear
  obtain ⟨C_A, hCA, DA, hDA, hA'⟩ := hA
  obtain ⟨C_Q, hCQ, DQ, hDQ, hQ'⟩ := hQ
  obtain ⟨Cdet, hCdet, Ddet, hDdet, hdet'⟩ := hdet c₁ hc₁
  obtain ⟨Ccr, hCcr, Ecr, Dcr, hDcr, hcr⟩ := hcross c₁ hc₁
  obtain ⟨Csm, hCsm, Esm, Dsm, hDsm, hsm⟩ := hsame c₁ hc₁
  obtain ⟨CK, hCK, Dls, hDls, hls'⟩ := hls
  obtain ⟨Ctail, hCtail, Dtail, hDtail, htail⟩ := htail
  obtain ⟨DL1, hDL1, hlog1⟩ := exists_log_rpow_le_rpow (E := max Ecr Esm) (a := p.η / 2)
    (by linarith only [p.hη])
  obtain ⟨DL2, hDL2, hlog2⟩ := exists_log_rpow_le_rpow (E := (2:ℝ)) (a := (p.x - p.u) / 2)
    (by linarith only [p.hw, p.hwu, p.huv, p.hvx])
  set Cκ : ℝ := 16 * C_A * max Ccr Csm with hCκ
  set Dbig : ℝ := 16 + Real.exp (4 * (Cdet + Ctail))
    + (max DA 0 + max DQ 0 + max Ddet 0 + max Dcr 0 + max Dsm 0 + max Dls 0 + max Dtail 0
      + max Dnear 0 + max DL1 0 + max DL2 0 + max (Cκ ^ (2 / p.η) + 1) 0) with hDbig
  have hm_DA : DA ≤ max DA 0 := le_max_left _ _
  have hm_DQ : DQ ≤ max DQ 0 := le_max_left _ _
  have hm_Ddet : Ddet ≤ max Ddet 0 := le_max_left _ _
  have hm_Dcr : Dcr ≤ max Dcr 0 := le_max_left _ _
  have hm_Dsm : Dsm ≤ max Dsm 0 := le_max_left _ _
  have hm_Dls : Dls ≤ max Dls 0 := le_max_left _ _
  have hm_Dtail : Dtail ≤ max Dtail 0 := le_max_left _ _
  have hm_Dnear : Dnear ≤ max Dnear 0 := le_max_left _ _
  have hm_DL1 : DL1 ≤ max DL1 0 := le_max_left _ _
  have hm_DL2 : DL2 ≤ max DL2 0 := le_max_left _ _
  have hm_Cκ : Cκ ^ (2 / p.η) + 1 ≤ max (Cκ ^ (2 / p.η) + 1) 0 := le_max_left _ _
  have hn_DA : (0:ℝ) ≤ max DA 0 := le_max_right _ _
  have hn_DQ : (0:ℝ) ≤ max DQ 0 := le_max_right _ _
  have hn_Ddet : (0:ℝ) ≤ max Ddet 0 := le_max_right _ _
  have hn_Dcr : (0:ℝ) ≤ max Dcr 0 := le_max_right _ _
  have hn_Dsm : (0:ℝ) ≤ max Dsm 0 := le_max_right _ _
  have hn_Dls : (0:ℝ) ≤ max Dls 0 := le_max_right _ _
  have hn_Dtail : (0:ℝ) ≤ max Dtail 0 := le_max_right _ _
  have hn_Dnear : (0:ℝ) ≤ max Dnear 0 := le_max_right _ _
  have hn_DL1 : (0:ℝ) ≤ max DL1 0 := le_max_right _ _
  have hn_DL2 : (0:ℝ) ≤ max DL2 0 := le_max_right _ _
  have hn_Cκ : (0:ℝ) ≤ max (Cκ ^ (2 / p.η) + 1) 0 := le_max_right _ _
  have hexpnn : (0:ℝ) ≤ Real.exp (4 * (Cdet + Ctail)) := Real.exp_nonneg _
  have h16 : (16:ℝ) ≤ Dbig := by rw [hDbig]; linarith only [hexpnn, hn_DA, hn_DQ, hn_Ddet, hn_Dcr, hn_Dsm, hn_Dls, hn_Dtail, hn_Dnear, hn_DL1, hn_DL2, hn_Cκ]
  have hexp_le : Real.exp (4 * (Cdet + Ctail)) ≤ Dbig := by rw [hDbig]; linarith only [hexpnn, hn_DA, hn_DQ, hn_Ddet, hn_Dcr, hn_Dsm, hn_Dls, hn_Dtail, hn_Dnear, hn_DL1, hn_DL2, hn_Cκ]
  have hDA : DA ≤ Dbig := by rw [hDbig]; linarith only [hm_DA, hexpnn, hn_DA, hn_DQ, hn_Ddet, hn_Dcr, hn_Dsm, hn_Dls, hn_Dtail, hn_Dnear, hn_DL1, hn_DL2, hn_Cκ]
  have hDQ : DQ ≤ Dbig := by rw [hDbig]; linarith only [hm_DQ, hexpnn, hn_DA, hn_DQ, hn_Ddet, hn_Dcr, hn_Dsm, hn_Dls, hn_Dtail, hn_Dnear, hn_DL1, hn_DL2, hn_Cκ]
  have hDdet : Ddet ≤ Dbig := by rw [hDbig]; linarith only [hm_Ddet, hexpnn, hn_DA, hn_DQ, hn_Ddet, hn_Dcr, hn_Dsm, hn_Dls, hn_Dtail, hn_Dnear, hn_DL1, hn_DL2, hn_Cκ]
  have hDcr : Dcr ≤ Dbig := by rw [hDbig]; linarith only [hm_Dcr, hexpnn, hn_DA, hn_DQ, hn_Ddet, hn_Dcr, hn_Dsm, hn_Dls, hn_Dtail, hn_Dnear, hn_DL1, hn_DL2, hn_Cκ]
  have hDsm : Dsm ≤ Dbig := by rw [hDbig]; linarith only [hm_Dsm, hexpnn, hn_DA, hn_DQ, hn_Ddet, hn_Dcr, hn_Dsm, hn_Dls, hn_Dtail, hn_Dnear, hn_DL1, hn_DL2, hn_Cκ]
  have hDls : Dls ≤ Dbig := by rw [hDbig]; linarith only [hm_Dls, hexpnn, hn_DA, hn_DQ, hn_Ddet, hn_Dcr, hn_Dsm, hn_Dls, hn_Dtail, hn_Dnear, hn_DL1, hn_DL2, hn_Cκ]
  have hDtail : Dtail ≤ Dbig := by rw [hDbig]; linarith only [hm_Dtail, hexpnn, hn_DA, hn_DQ, hn_Ddet, hn_Dcr, hn_Dsm, hn_Dls, hn_Dtail, hn_Dnear, hn_DL1, hn_DL2, hn_Cκ]
  have hDnear : Dnear ≤ Dbig := by rw [hDbig]; linarith only [hm_Dnear, hexpnn, hn_DA, hn_DQ, hn_Ddet, hn_Dcr, hn_Dsm, hn_Dls, hn_Dtail, hn_Dnear, hn_DL1, hn_DL2, hn_Cκ]
  have hDL1 : DL1 ≤ Dbig := by rw [hDbig]; linarith only [hm_DL1, hexpnn, hn_DA, hn_DQ, hn_Ddet, hn_Dcr, hn_Dsm, hn_Dls, hn_Dtail, hn_Dnear, hn_DL1, hn_DL2, hn_Cκ]
  have hDL2 : DL2 ≤ Dbig := by rw [hDbig]; linarith only [hm_DL2, hexpnn, hn_DA, hn_DQ, hn_Ddet, hn_Dcr, hn_Dsm, hn_Dls, hn_Dtail, hn_Dnear, hn_DL1, hn_DL2, hn_Cκ]
  have hCκ_le : Cκ ^ (2 / p.η) + 1 ≤ Dbig := by rw [hDbig]; linarith only [hm_Cκ, hexpnn, hn_DA, hn_DQ, hn_Ddet, hn_Dcr, hn_Dsm, hn_Dls, hn_Dtail, hn_Dnear, hn_DL1, hn_DL2, hn_Cκ]
  clear_value Dbig Cκ
  refine ⟨4 * C_A * C_Q * CK + K / 2, by
    have h4 := mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hCA) hCQ) hCK
    linarith only [h4, hK], Dbig, ?_, ?_⟩
  · rw [hDbig]; positivity
  · intro q hq _inst T σ hT hDb hpσ hσ1 m χ ρ hχ1 hzm hσ hρ1 him hnexc hsep
    have hDA' : DA ≤ scale q T := le_trans hDA hDb
    have hDQ' : DQ ≤ scale q T := le_trans hDQ hDb
    have hDdet' : Ddet ≤ scale q T := le_trans hDdet hDb
    have hDcr' : Dcr ≤ scale q T := le_trans hDcr hDb
    have hDsm' : Dsm ≤ scale q T := le_trans hDsm hDb
    have hDls' : Dls ≤ scale q T := le_trans hDls hDb
    have hDtail' : Dtail ≤ scale q T := le_trans hDtail hDb
    have hDnear' : Dnear ≤ scale q T := le_trans hDnear hDb
    have hDL1' : DL1 ≤ scale q T := le_trans hDL1 hDb
    have hDL2' : DL2 ≤ scale q T := le_trans hDL2 hDb
    have hCκ' : Cκ ^ (2 / p.η) + 1 ≤ scale q T := le_trans hCκ_le hDb
    have hexp_le' : Real.exp (4 * (Cdet + Ctail)) ≤ scale q T := le_trans hexp_le hDb
    have h16' : (16:ℝ) ≤ scale q T := le_trans h16 hDb
    -- basic facts about `D = scale q T` and `L = Lscale q T`
    have hDpos : 0 < scale q T := lt_of_lt_of_le (by norm_num) h16'
    have hD1 : 1 ≤ scale q T := le_trans (by norm_num) h16'
    have hLeq : Lscale q T = Real.log (scale q T) := rfl
    have hL1 : 1 ≤ Lscale q T := by
      rw [hLeq]
      calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (scale q T) := Real.log_le_log (Real.exp_pos 1)
            (le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith only [h16']))
    have hLpos : 0 < Lscale q T := lt_of_lt_of_le one_pos hL1
    have hlog_nonneg : 0 ≤ Lscale q T := le_of_lt hLpos
    -- the mollifier parameters
    have hW1 : 1 < Dpow q T p.w := by
      rw [Dpow]
      exact Real.one_lt_rpow (by linarith only [h16']) p.hw
    have hL2U : Real.exp (4 * (Cdet + Ctail)) ≤ scale q T := hexp_le'
    have hVf : 3/4 ≤ 1 - (Cdet + Ctail) / Lscale q T := by
      rw [show (1:ℝ) - (Cdet + Ctail) / Lscale q T = 1 - (Cdet + Ctail) / Lscale q T from rfl,
        le_sub_iff_add_le]
      have h3 : (Cdet + Ctail) / Lscale q T ≤ 1/4 := by
        rw [div_le_iff₀ hLpos]
        have hlog4 : 4 * (Cdet + Ctail) ≤ Real.log (scale q T) :=
          (Real.le_log_iff_exp_le hDpos).mpr hexp_le'
        rw [← hLeq] at hlog4
        linarith only [hlog4]
      linarith only [h3]
    -- the split into the bulk and the near-line part
    set I₁ : Finset (Fin m) := Finset.univ.filter (fun i => c₁ ≤ (1 - (ρ i).re) * Lscale q T)
      with hI1
    set I₂ : Finset (Fin m) := Finset.univ.filter (fun i => ¬ (c₁ ≤ (1 - (ρ i).re) * Lscale q T))
      with hI2
    have hcard_nat : I₁.card + I₂.card = m := by
      rw [hI1, hI2]
      simpa [Finset.card_univ, Fintype.card_fin] using
        (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
          (p := fun i => c₁ ≤ (1 - (ρ i).re) * Lscale q T))
    have hcard : (m : ℝ) = (I₁.card : ℝ) + (I₂.card : ℝ) := by
      have := congrArg (fun k : ℕ => (k : ℝ)) hcard_nat
      push_cast at this
      linarith only [this]
    -- the near-line part
    have hnearb : (I₂.card : ℝ) ≤ K := by
      have hcard2 : Fintype.card ↥I₂ = I₂.card := Fintype.card_coe I₂
      rw [← hcard2]
      set e : ↥I₂ ≃ Fin (Fintype.card ↥I₂) := Fintype.equivFin ↥I₂ with he
      refine hnear q hq T σ hT hDnear' hpσ (Fintype.card ↥I₂)
        (fun k => χ (e.symm k).1) (fun k => ρ (e.symm k).1)
        (fun k => hχ1 _) (fun k => hzm _) (fun k => hσ _) (fun k => hρ1 _)
        (fun k => him _) (fun k => ?_) (fun k l hkl hchi => ?_)
      · have hk : (e.symm k).1 ∈ Finset.univ.filter
            (fun i => ¬ (c₁ ≤ (1 - (ρ i).re) * Lscale q T)) := hI2 ▸ (e.symm k).2
        exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hk).2)
      · exact hsep _ _ (fun hh => hkl (e.symm.injective (Subtype.ext hh))) hchi
    -- the bulk part: the Halász frame
    have hbulk : (I₁.card : ℝ) ≤ 4 * C_A * C_Q * CK * (2 + log2 (1 + (1 - σ) * Lscale q T))
        * Dpow q T (2 * p.x * (1 - σ)) := by
      have hLnn : 0 ≤ Lscale q T := le_of_lt hLpos
      have hDnn : 0 ≤ scale q T := le_of_lt hDpos
      have hpow_nn : ∀ a : ℝ, 0 ≤ Lscale q T ^ a := fun a => Real.rpow_nonneg hLnn a
      have hDpow_nn : ∀ a : ℝ, 0 ≤ Dpow q T a := fun a => Real.rpow_nonneg hDnn a
      have hCκnn : 0 ≤ Cκ := by
        rw [hCκ]
        exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hCA))
          (le_trans (le_of_lt hCcr) (le_max_left _ _))
      have h1σ : 0 ≤ 1 - σ := by linarith only [hσ1]
      have hlam1 : 1 ≤ 1 + (1 - σ) * Lscale q T := by linarith only [mul_nonneg h1σ hLnn]
      have hlog2nn : 0 ≤ log2 (1 + (1 - σ) * Lscale q T) := by
        rw [log2]
        exact div_nonneg (Real.log_nonneg hlam1) (Real.log_pos one_lt_two).le
      have h2log : 2 ≤ 2 + log2 (1 + (1 - σ) * Lscale q T) := by linarith only [hlog2nn]
      have h2log0 : 0 ≤ 2 + log2 (1 + (1 - σ) * Lscale q T) := by linarith only [hlog2nn]
      have hDp1 : 1 ≤ Dpow q T (2 * p.x * (1 - σ)) := by
        rw [Dpow]
        exact Real.one_le_rpow hD1 (mul_nonneg (by linarith only [p.hw, p.hwu, p.huv, p.hvx]) h1σ)
      -- `16 C_A · max Ccr Csm ≤ D^{η/2}`
      have h8 : max Ccr Csm ≤ Dpow q T (p.η / 2) / (16 * C_A) := by
        have h3 : Cκ ^ (2 / p.η) ≤ scale q T := by linarith only [hCκ']
        have h4 : Cκ ≤ Dpow q T (p.η / 2) := by
          have hexp : Cκ = (Cκ ^ (2 / p.η)) ^ (p.η / 2) := by
            have hexp1 : 2 / p.η * (p.η / 2) = 1 := by
              rw [div_mul_div_comm, mul_comm p.η 2]
              exact div_self (ne_of_gt (by linarith only [p.hη] : (0:ℝ) < 2 * p.η))
            rw [← Real.rpow_mul hCκnn, hexp1, Real.rpow_one]
          rw [hexp]
          exact Real.rpow_le_rpow (Real.rpow_nonneg hCκnn _) h3 (by linarith only [p.hη])
        rw [le_div_iff₀ (by linarith only [hCA])]
        rw [hCκ] at h4
        linarith only [h4]
      have hLpow_le : Lscale q T ^ (max Ecr Esm) ≤ Dpow q T (p.η / 2) := by
        rw [hLeq]
        exact hlog1 (scale q T) hDL1'
      have hprod : Dpow q T (p.η / 2) * Dpow q T (p.η / 2) * Dpow q T (-p.η) = 1 := by
        simp only [Dpow]
        rw [← Real.rpow_add hDpos, ← Real.rpow_add hDpos,
          show p.η / 2 + p.η / 2 + -p.η = 0 by ring, Real.rpow_zero]
      have hκ_small : (max (Ccr * Lscale q T ^ Ecr * Dpow q T (-p.η))
          (Csm * Lscale q T ^ Esm * Dpow q T (-p.η))) ≤ 1 / (16 * C_A) := by
        have hmax0 : 0 ≤ max Ccr Csm := le_trans (le_of_lt hCcr) (le_max_left _ _)
        refine max_le ?_ ?_
        · have h1 : Ccr ≤ max Ccr Csm := le_max_left _ _
          have h2 : Lscale q T ^ Ecr ≤ Lscale q T ^ (max Ecr Esm) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)
          have h3 : Ccr * Lscale q T ^ Ecr * Dpow q T (-p.η)
              ≤ max Ccr Csm * Dpow q T (p.η / 2) * Dpow q T (-p.η) :=
            mul_le_mul_of_nonneg_right (mul_le_mul h1 (h2.trans hLpow_le) (hpow_nn _) hmax0)
              (hDpow_nn _)
          refine h3.trans ?_
          calc max Ccr Csm * Dpow q T (p.η / 2) * Dpow q T (-p.η)
              ≤ (Dpow q T (p.η / 2) / (16 * C_A)) * Dpow q T (p.η / 2) * Dpow q T (-p.η) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h8 (hDpow_nn _))
                  (hDpow_nn _)
            _ = 1 / (16 * C_A) := by
                rw [show (Dpow q T (p.η / 2) / (16 * C_A)) * Dpow q T (p.η / 2)
                      * Dpow q T (-p.η)
                    = (Dpow q T (p.η / 2) * Dpow q T (p.η / 2) * Dpow q T (-p.η))
                      / (16 * C_A) by ring, hprod, one_div]
        · have h1 : Csm ≤ max Ccr Csm := le_max_right _ _
          have h2 : Lscale q T ^ Esm ≤ Lscale q T ^ (max Ecr Esm) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right _ _)
          have h3 : Csm * Lscale q T ^ Esm * Dpow q T (-p.η)
              ≤ max Ccr Csm * Dpow q T (p.η / 2) * Dpow q T (-p.η) :=
            mul_le_mul_of_nonneg_right (mul_le_mul h1 (h2.trans hLpow_le) (hpow_nn _) hmax0)
              (hDpow_nn _)
          refine h3.trans ?_
          calc max Ccr Csm * Dpow q T (p.η / 2) * Dpow q T (-p.η)
              ≤ (Dpow q T (p.η / 2) / (16 * C_A)) * Dpow q T (p.η / 2) * Dpow q T (-p.η) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h8 (hDpow_nn _))
                  (hDpow_nn _)
            _ = 1 / (16 * C_A) := by
                rw [show (Dpow q T (p.η / 2) / (16 * C_A)) * Dpow q T (p.η / 2)
                      * Dpow q T (-p.η)
                    = (Dpow q T (p.η / 2) * Dpow q T (p.η / 2) * Dpow q T (-p.η))
                      / (16 * C_A) by ring, hprod, one_div]
      -- the pole residue is nonnegative (`Q(1)` in diagonalized form)
      have hQ0 : 0 ≤ poleResidue (Dpow q T p.w) := by
        have hd : 0 ≤ poleDiag (Dpow q T p.w) := by
          rw [poleDiag]
          exact Finset.sum_nonneg (fun l _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
        have hmul := poleResidue_mul_log_sq (Dpow q T p.w) hW1
        have hpos : 0 < (Real.log (Dpow q T p.w)) ^ 2 := by
          have h0 : 0 < Real.log (Dpow q T p.w) := Real.log_pos hW1
          exact pow_pos h0 2
        have hm : 0 ≤ poleResidue (Dpow q T p.w) * (Real.log (Dpow q T p.w)) ^ 2 := by
          rw [hmul]; exact hd
        have hm2 : 0 ≤ (Real.log (Dpow q T p.w)) ^ 2 * poleResidue (Dpow q T p.w) := by
          rw [mul_comm]; exact hm
        exact nonneg_of_mul_nonneg_right hm2 hpos
      -- the mollifier scale `U' = U/L²`
      have hU'pos : 0 < halaszU' p q T :=
        div_pos (Real.rpow_pos_of_pos hDpos p.u) (pow_pos hLpos 2)
      have hU'X : halaszU' p q T ≤ Dpow q T p.x := by
        have hUp : p.u ≤ p.x := le_of_lt (lt_trans p.huv p.hvx)
        have hDu : Dpow q T p.u ≤ Dpow q T p.x := Real.rpow_le_rpow_of_exponent_le hD1 hUp
        have hDu0 : 0 ≤ Dpow q T p.u := (Real.rpow_pos_of_pos hDpos p.u).le
        have hL2 : (1 : ℝ) ≤ (Lscale q T) ^ 2 := by nlinarith only [hL1]
        calc halaszU' p q T = Dpow q T p.u / (Lscale q T) ^ 2 := rfl
          _ ≤ Dpow q T p.u := div_le_self hDu0 hL2
          _ ≤ Dpow q T p.x := hDu
      have hgfun_nn : ∀ n : ℕ, 0 ≤ gfun (Dpow q T p.x) (halaszU' p q T) n :=
        fun n => gfun_nonneg hU'pos hU'X n
      -- the auxiliary quantities of the frame
      set V : ℝ := 1 - (Cdet + Ctail) / Lscale q T with hVdef
      have hV34 : 3 / 4 ≤ V := by rw [hVdef]; exact hVf
      have hV0 : 0 ≤ V := le_trans (by norm_num) hV34
      set κ : ℝ := max (Ccr * Lscale q T ^ Ecr * Dpow q T (-p.η))
        (Csm * Lscale q T ^ Esm * Dpow q T (-p.η)) with hκdef
      have hκ0 : 0 ≤ κ := by
        rw [hκdef]
        exact le_trans (mul_nonneg (mul_nonneg (le_of_lt hCcr) (hpow_nn _)) (hDpow_nn _))
          (le_max_left _ _)
      have hκC : 2 * C_A * κ ≤ 1 / 8 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 8)]
        have h := hκ_small
        rw [le_div_iff₀ (by linarith only [hCA] : (0:ℝ) < 16 * C_A)] at h
        linarith only [h]
      set CKq : ℝ := CK * (2 + log2 (1 + (1 - σ) * Lscale q T)) * Lscale q T
        * Dpow q T (2 * p.x * (1 - σ)) with hCKq
      have hCKq0 : 0 ≤ CKq := by
        rw [hCKq]
        exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCK) h2log0) hLnn) (hDpow_nn _)
      set Bf : ℝ := poleResidue (Dpow q T p.w) * CKq + 2 * κ * (I₁.card : ℝ) with hBfdef
      have hBf0 : 0 ≤ Bf := by
        rw [hBfdef]
        exact add_nonneg (mul_nonneg hQ0 hCKq0)
          (mul_nonneg (mul_nonneg (by norm_num) hκ0) (Nat.cast_nonneg _))
      have hcarduniv : ((Finset.univ : Finset ↥I₁).card : ℝ) = (I₁.card : ℝ) := by
        rw [Finset.card_univ, Fintype.card_coe]
      -- the `c₁`-condition on the bulk indices
      have hc1 : ∀ i : ↥I₁, c₁ ≤ (1 - (ρ i.1).re) * Lscale q T := by
        intro i
        have hi : (i : Fin m) ∈ Finset.univ.filter
            (fun j => c₁ ≤ (1 - (ρ j).re) * Lscale q T) := by
          rw [← hI1]; exact i.2
        exact (Finset.mem_filter.mp hi).2
      -- the detector lower bound
      have hdetv : ∀ i : ↥I₁, V ≤ ‖∑ n ∈ Finset.Icc 1 (halaszN p q T),
          halaszA p q T n * halaszF p q T (χ i.1) (ρ i.1) n‖ := by
        intro i
        have hdeti := hdet' q hq T hT hDdet' (χ i.1) (hχ1 i.1) (ρ i.1) (hzm i.1)
          (le_trans hpσ (hσ i.1)) (hρ1 i.1) (him i.1) (hc1 i)
        have htaili := htail q hq T hT hDtail' (χ i.1) (ρ i.1) (hχ1 i.1) (hzm i.1)
          (le_trans hpσ (hσ i.1)) (hρ1 i.1) (him i.1) (halaszN p q T) le_rfl
        set fs : ℂ := ∑ n ∈ Finset.Icc 1 (halaszN p q T),
            halaszA p q T n * halaszF p q T (χ i.1) (ρ i.1) n with hfsdef
        set dd : ℂ := Work.LinnikAreas.Density4.detSum q (Dpow q T p.u) (Dpow q T p.v)
            (Dpow q T p.w) (Dpow q T p.x) (Lscale q T) (χ i.1) (ρ i.1) with hdddef
        set tr : ℂ := ∑ n ∈ Finset.Icc 1 (halaszN p q T),
              ((psiSum (Dpow q T p.u) (Dpow q T p.v) n : ℝ) : ℂ)
              * ((thetaS (Dpow q T p.w) n : ℝ) : ℂ) * χ i.1 (n : ZMod q)
              * ((n : ℂ) ^ (-(ρ i.1)))
              * (((gfun (Dpow q T p.x) (Dpow q T p.u / (Lscale q T) ^ 2) n : ℝ) : ℂ))
            with htrdef
        have hid : fs = tr := by
          rw [hfsdef, htrdef]
          refine Finset.sum_congr rfl (fun n hn => ?_)
          have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
          exact halasz_prod_eq p q T (χ i.1) (ρ i.1) n hn1 (hgfun_nn n)
        have hdd' : 1 - Cdet / Lscale q T ≤ ‖dd‖ := hdeti
        have htt : ‖dd - tr‖ ≤ Ctail / Lscale q T := by
          rw [norm_sub_rev] at htaili
          exact htaili
        have hsub : ‖dd - fs‖ ≤ Ctail / Lscale q T := by
          have h := htt
          rwa [← hid] at h
        have hnorm : 1 - Cdet / Lscale q T - Ctail / Lscale q T ≤ ‖fs‖ := by
          have h4 : ‖dd‖ ≤ ‖fs‖ + Ctail / Lscale q T := by
            calc ‖dd‖ = ‖fs + (dd - fs)‖ := by
                  rw [show fs + (dd - fs) = dd by ring]
              _ ≤ ‖fs‖ + ‖dd - fs‖ := norm_add_le fs (dd - fs)
              _ ≤ ‖fs‖ + Ctail / Lscale q T := by linarith only [hsub]
          linarith only [hdd', h4]
        rw [hVdef]
        rw [show (1 : ℝ) - (Cdet + Ctail) / Lscale q T
            = 1 - Cdet / Lscale q T - Ctail / Lscale q T by ring]
        exact hnorm
      -- the bilinear form
      have hbilin : ∀ η : ↥I₁ → ℂ, (∑ i, ‖η i‖ ^ 2) ≤ 1 →
          (∑ n ∈ Finset.Icc 1 (halaszN p q T),
              (1 : ℝ) * ‖∑ i, η i * halaszF p q T (χ i.1) (ρ i.1) n‖ ^ 2) ≤ Bf := by
        intro η hη1
        have hρI : ∀ i ∈ (Finset.univ : Finset ↥I₁), 1 / 2 < (ρ i.1).re :=
          fun i _ => lt_of_lt_of_le p.hσ₀ (le_trans hpσ (hσ i.1))
        have hCblk : ∀ (m' : ℕ) (ρ' : Fin m' → ℂ) (z' : Fin m' → ℂ),
            (∀ i, σ ≤ (ρ' i).re) → (∀ i, (ρ' i).re < 1) → (∀ i, |(ρ' i).im| ≤ T) →
            (∀ i j, i ≠ j → 1 / Lscale q T ≤ |(ρ' i).im - (ρ' j).im|) →
            (poleGram m' (Dpow q T p.x) (halaszU' p q T) ρ' z').re
              ≤ CKq * ∑ i, ‖z' i‖ ^ 2 := by
          intro m' ρ' z' hσ' hlt' him' hsep'
          have h := hls' q hq T σ hT hDls' hpσ hσ1 m' ρ' z' hσ' hlt' him' hsep'
          rw [hCKq]
          exact h
        have hpole : ∀ u ∈ (Finset.univ : Finset ↥I₁).powerset,
            (∀ i ∈ u, ∀ j ∈ u, χ i.1 = χ j.1) →
            (∑ i ∈ u, ∑ j ∈ u, η i * (starRingEnd ℂ) (η j)
                * poleK (Dpow q T p.x) (halaszU' p q T) (ρ i.1) (ρ j.1)).re
              ≤ CKq * ∑ i ∈ u, ‖η i‖ ^ 2 := by
          intro u _ hcu
          exact pole_all_blocks (q := q) (fun i : ↥I₁ => χ i.1) (fun i : ↥I₁ => ρ i.1)
            (Dpow q T p.x) (halaszU' p q T) (Lscale q T) T CKq σ hCblk
            (fun i => hσ i.1) (fun i => hρ1 i.1) (fun i => him i.1)
            (fun i j hij hchi => hsep i.1 j.1 (fun h => hij (Subtype.ext h)) hchi) u hcu η
        have hbl := halasz_bilinear (s := (Finset.univ : Finset ↥I₁)) (fun i : ↥I₁ => χ i.1)
          (fun i : ↥I₁ => ρ i.1) hρI η hη1 (Dpow q T p.w) (Dpow q T p.x) (halaszU' p q T)
          hW1 (Real.rpow_pos_of_pos hDpos p.x) hU'pos hU'X κ CKq hκ0 hCKq0 hQ0
          (fun i _ j _ hne => by
            rw [hκdef]
            exact le_trans (hcr q hq T hT hDcr' (χ i.1) (χ j.1) (ρ i.1) (ρ j.1)
              (hχ1 i.1) (hχ1 j.1) hne (hzm i.1) (hzm j.1) (le_trans hpσ (hσ i.1)) (hρ1 i.1)
              (le_trans hpσ (hσ j.1)) (hρ1 j.1) (him i.1) (him j.1) (hc1 i) (hc1 j))
              (le_max_left _ _))
          (fun i _ j _ _ => by
            rw [hκdef]
            exact le_trans (hsm q hq T hT hDsm' (ρ i.1) (ρ j.1) (le_trans hpσ (hσ i.1))
              (hρ1 i.1) (le_trans hpσ (hσ j.1)) (hρ1 j.1) (him i.1) (him j.1)
              (hc1 i) (hc1 j)) (le_max_right _ _))
          hpole
        calc (∑ n ∈ Finset.Icc 1 (halaszN p q T),
              (1 : ℝ) * ‖∑ i, η i * halaszF p q T (χ i.1) (ρ i.1) n‖ ^ 2)
            = ∑ n ∈ Finset.Icc 1 (halaszN p q T),
                gramWeight (Dpow q T p.w) (Dpow q T p.x) (halaszU' p q T) n
                  * ‖∑ i, η i * (χ i.1 (n : ZMod q))
                      * ((n : ℂ) ^ ((1 / 2 : ℂ) - ρ i.1))‖ ^ 2 := by
              refine Finset.sum_congr rfl (fun n _ => ?_)
              rw [one_mul]
              exact norm_sum_halaszF p q T Finset.univ (fun i : ↥I₁ => χ i.1)
                (fun i : ↥I₁ => ρ i.1) η (hgfun_nn n)
          _ ≤ ∑' n, gramWeight (Dpow q T p.w) (Dpow q T p.x) (halaszU' p q T) n
                  * ‖∑ i, η i * (χ i.1 (n : ZMod q))
                      * ((n : ℂ) ^ ((1 / 2 : ℂ) - ρ i.1))‖ ^ 2 :=
              Summable.sum_le_tsum (Finset.Icc 1 (halaszN p q T))
                (fun n _ => mul_nonneg (gramWeight_nonneg hU'pos hU'X n) (sq_nonneg _))
                (summable_gramWeight_normSq (s := (Finset.univ : Finset ↥I₁))
                  (χ := fun i : ↥I₁ => χ i.1) (ρ := fun i : ↥I₁ => ρ i.1) hρI η
                  (Dpow q T p.w) (Dpow q T p.x) (halaszU' p q T) hW1
                  (Real.rpow_pos_of_pos hDpos p.x) hU'pos hU'X)
          _ ≤ poleResidue (Dpow q T p.w) * CKq
                + 2 * κ * (Finset.univ : Finset ↥I₁).card := hbl
          _ = Bf := by rw [hBfdef, hcarduniv]
      have hframe := Work.ZeroDensity.Jutila.halaszDualityFrame (ι := ↥I₁) (N := halaszN p q T)
        (halaszA p q T) (fun _ => (1 : ℝ)) (fun n _ => one_pos)
        (fun i n => halaszF p q T (χ i.1) (ρ i.1) n) V Bf hV0 hdetv hbilin hBf0
      -- the `ℓ²` mass of `a`
      have hAsum : (∑ n ∈ Finset.Icc 1 (halaszN p q T), ‖halaszA p q T n‖ ^ 2 / (1 : ℝ))
          ≤ C_A := by
        have h0 := hA' q hq T hT hDA' (halaszN p q T)
        have hidA : ∀ n ∈ Finset.Icc 1 (halaszN p q T),
            ‖halaszA p q T n‖ ^ 2 / (1 : ℝ)
              = (psiSum (Dpow q T p.u) (Dpow q T p.v) n) ^ 2 * ((n : ℝ))⁻¹
                * gfun (Dpow q T p.x) (halaszU' p q T) n := by
          intro n _
          have hg := hgfun_nn n
          rw [div_one, halaszA, norm_mul, norm_mul, mul_pow, mul_pow]
          simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
          rw [Real.sq_sqrt hg, norm_cpow_neg_half_sq]
        rw [Finset.sum_congr rfl hidA]
        exact h0
      -- the final chain
      have h1 : (I₁.card : ℝ) * V ^ 2 ≤ C_A * Bf := by
        calc (I₁.card : ℝ) * V ^ 2 = (Fintype.card ↥I₁ : ℝ) * V ^ 2 := by rw [Fintype.card_coe]
          _ ≤ (∑ n ∈ Finset.Icc 1 (halaszN p q T), ‖halaszA p q T n‖ ^ 2 / (1 : ℝ)) * Bf :=
              hframe
          _ ≤ C_A * Bf := mul_le_mul_of_nonneg_right hAsum hBf0
      have h2 : (I₁.card : ℝ) * (V ^ 2 - 2 * C_A * κ)
          ≤ C_A * poleResidue (Dpow q T p.w) * CKq := by
        rw [hBfdef] at h1
        nlinarith only [h1]
      have h3 : 1 / 4 ≤ V ^ 2 - 2 * C_A * κ := by
        have hV2 : 9 / 16 ≤ V ^ 2 := by nlinarith only [hV34]
        linarith only [hV2, hκC]
      have h4 : C_A * poleResidue (Dpow q T p.w) * CKq
          ≤ C_A * C_Q * CK * (2 + log2 (1 + (1 - σ) * Lscale q T))
              * Dpow q T (2 * p.x * (1 - σ)) := by
        have hQ'x := hQ' q hq T hT hDQ'
        have hLne : Lscale q T ≠ 0 := ne_of_gt hLpos
        have hLpos' : 0 < Lscale q T := hLpos
        calc C_A * poleResidue (Dpow q T p.w) * CKq
            ≤ C_A * (C_Q / Lscale q T) * CKq :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hQ'x (le_of_lt hCA)) hCKq0
          _ = C_A * C_Q * CK * (2 + log2 (1 + (1 - σ) * Lscale q T))
                * Dpow q T (2 * p.x * (1 - σ)) := by
              rw [hCKq]
              field_simp
      have hcnn : (0 : ℝ) ≤ (I₁.card : ℝ) := Nat.cast_nonneg _
      have hstep : (I₁.card : ℝ) * (1 / 4) ≤ C_A * poleResidue (Dpow q T p.w) * CKq :=
        le_trans (mul_le_mul_of_nonneg_left h3 hcnn) h2
      have hstep2 : (I₁.card : ℝ) / 4
          ≤ C_A * C_Q * CK * (2 + log2 (1 + (1 - σ) * Lscale q T))
              * Dpow q T (2 * p.x * (1 - σ)) := by
        have hh := hstep.trans h4
        linarith only [hh]
      linarith only [hstep2]

    have hDi : 0 ≤ 1 - σ := by linarith only [hσ1]
    have hx0 : 0 < p.x := by linarith only [p.hw, p.hwu, p.huv, p.hvx]
    have hR2 : 2 ≤ 2 + log2 (1 + (1 - σ) * Lscale q T) := by
      have hl : 1 ≤ 1 + (1 - σ) * Lscale q T := by
        linarith only [mul_nonneg hDi hlog_nonneg]
      rw [log2]
      have h0 : 0 ≤ Real.log (1 + (1 - σ) * Lscale q T) := Real.log_nonneg hl
      have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      have h3 := div_nonneg h0 h2.le
      linarith only [h3]
    have hDp1 : 1 ≤ Dpow q T (2 * p.x * (1 - σ)) := by
      rw [Dpow]
      exact Real.one_le_rpow hD1 (mul_nonneg (by linarith only [hx0]) hDi)
    have hKineq : K ≤ (K / 2) * (2 + log2 (1 + (1 - σ) * Lscale q T))
        * Dpow q T (2 * p.x * (1 - σ)) := by
      have hxy : 2 * 1 ≤ (2 + log2 (1 + (1 - σ) * Lscale q T))
          * Dpow q T (2 * p.x * (1 - σ)) :=
        mul_le_mul hR2 hDp1 (by norm_num) (le_trans (by norm_num) hR2)
      have hK2 : 0 ≤ K / 2 := by linarith only [hK]
      have hstep : (K / 2) * (2 * 1)
          ≤ (K / 2) * ((2 + log2 (1 + (1 - σ) * Lscale q T)) * Dpow q T (2 * p.x * (1 - σ))) :=
        mul_le_mul_of_nonneg_left hxy hK2
      linarith only [hstep]
    have hmain : (m : ℝ) ≤ 4 * C_A * C_Q * CK * (2 + log2 (1 + (1 - σ) * Lscale q T))
        * Dpow q T (2 * p.x * (1 - σ)) + K := by linarith only [hcard, hbulk, hnearb]
    have hgoal : (m : ℝ) ≤ (4 * C_A * C_Q * CK + K / 2)
        * (2 + log2 (1 + (1 - σ) * Lscale q T)) * Dpow q T (2 * p.x * (1 - σ)) := by
      linarith only [hmain, hKineq]
    exact hgoal



end Work.ZeroDensity.LogFree
