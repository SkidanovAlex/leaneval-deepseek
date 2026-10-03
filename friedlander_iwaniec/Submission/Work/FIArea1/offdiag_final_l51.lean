import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace Work.FIArea1

/-- A generic `mul_le_mul` for four factors. -/
lemma FI_mul4 {a b c d a' b' c' d' : ℝ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hd : d ≤ d')
    (hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (hd0 : 0 ≤ d)
    (ha'0 : 0 ≤ a') (hb'0 : 0 ≤ b') (hc'0 : 0 ≤ c') :
    a * b * c * d ≤ a' * b' * c' * d' := by
  have h1 : a * b ≤ a' * b' := mul_le_mul ha hb hb0 ha'0
  have h2 : a * b * c ≤ a' * b' * c' := mul_le_mul h1 hc hc0 (mul_nonneg ha'0 hb'0)
  exact mul_le_mul h2 hd hd0 (mul_nonneg (mul_nonneg ha'0 hb'0) hc'0)

/-- **Final numerical comparison for the off-diagonal `FI` Lemma 5.1 count.** -/
theorem offdiag_final_l51 :
    ∀ (R : ℤ) (N : ℝ) (C0 M : ℕ) (Ct Ch Cr : ℝ),
    1 ≤ R → 2 ≤ N → 2 * Real.sqrt N ≤ (R : ℝ) →
    1 ≤ C0 → ((C0 : ℝ) + 1) ≤ 2 * Real.sqrt ((R.natAbs : ℝ) * Real.sqrt N) + 3 →
    ((M : ℝ) + 1) ≤ 3 * Real.sqrt N + 3 →
    0 < Ct → 0 < Ch → 0 < Cr →
    2 * Ct * ((C0 : ℝ) + 1) ^ 2 * (Real.log (2 * ((C0 : ℝ) + 2))) ^ 510 *
        (2 * (M : ℝ) * Ch * ((M : ℝ) + 1) * (Real.log ((M : ℝ) + 2)) ^ 2 + 4 * (M : ℝ) ^ 2)
      + Cr * ((M : ℝ) + 1) * ((M : ℝ) + 2 + (C0 : ℝ)) * (2 * (M : ℝ) + 1) ^ 2
    ≤ ((2 : ℝ) ^ 540 * (Ct + 1) * (Ch + 1) * (Cr + 1) + 2) *
        ((R.natAbs : ℝ) * N ^ ((3 : ℝ) / 2)) *
        (Real.log (2 * ((R.natAbs : ℝ) + N + 2))) ^ 514 := by
  intro R N C0 M Ct Ch Cr hR hN hRN hC0 hC0b hM hCt hCh hCr
  have hNpos : 0 < N := by linarith
  have hNnonneg : 0 ≤ N := le_of_lt hNpos
  set Rn : ℝ := (R.natAbs : ℝ) with hRndef
  set s : ℝ := Real.sqrt N with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Real.sqrt_nonneg N
  have hs1 : 1 ≤ s := by rw [hsdef, Real.one_le_sqrt]; linarith
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs1
  have hssq : s^2 = N := by rw [hsdef]; exact Real.sq_sqrt hNnonneg
  have hRn_le : (R : ℝ) ≤ Rn := by
    rw [hRndef, @Nat.cast_natAbs ℝ _ R, Int.cast_abs]; exact le_abs_self _
  have hRn2 : 2 * s ≤ Rn := by linarith
  have hRn2' : 2 ≤ Rn := by linarith
  have hRnpos : 0 < Rn := lt_of_lt_of_le two_pos hRn2'
  have hs_le_Rn : s ≤ Rn := by linarith
  set u : ℝ := Real.sqrt (Rn * s) with hudef
  have hRnspos : 0 < Rn * s := mul_pos hRnpos hspos
  have hRns4 : 4 ≤ Rn * s := by
    have h1 : (2*s)*s ≤ Rn*s := mul_le_mul_of_nonneg_right hRn2 hs0
    nlinarith only [h1, hssq, hN]
  have hu_sq : u^2 = Rn * s := by rw [hudef]; exact Real.sq_sqrt (le_of_lt hRnspos)
  have hu2 : 2 ≤ u := by
    rw [hudef, Real.le_sqrt (by norm_num) (le_of_lt hRnspos)]
    nlinarith only [hRns4]
  have hu_nonneg : 0 ≤ u := by rw [hudef]; exact Real.sqrt_nonneg _
  have hC0_plus1_pos : 0 < (C0 : ℝ) + 1 := by positivity
  have hsq1 : ((C0 : ℝ) + 1)^2 ≤ (2*u+3)^2 :=
    pow_le_pow_left₀ (le_of_lt hC0_plus1_pos) hC0b 2
  have h2u3_sq : (2*u+3)^2 ≤ 13 * u^2 := by nlinarith only [hu2, sq_nonneg (u-2)]
  have hC0sq : ((C0 : ℝ) + 1)^2 ≤ 13 * (Rn * s) := by
    calc ((C0 : ℝ) + 1)^2 ≤ (2*u+3)^2 := hsq1
      _ ≤ 13*u^2 := h2u3_sq
      _ = 13*(Rn*s) := by rw [hu_sq]
  have hC0_le : (C0 : ℝ) ≤ 2*u+2 := by linarith
  have hC0_2 : (C0 : ℝ) + 2 ≤ 4*u := by linarith
  have hu_le_Rns : u ≤ Rn*s := by
    rw [hudef, Real.sqrt_le_left (le_of_lt hRnspos)]
    nlinarith only [hRns4]
  have h8u : 2*((C0 : ℝ)+2) ≤ 8*u := by linarith
  have h8u_Rns : 8*u ≤ 8*(Rn*s) := by linarith
  have h4Rn2 : 8*(Rn*s) ≤ 4*Rn^2 := by
    have h := mul_le_mul_of_nonneg_left hRn2 (by positivity : (0:ℝ) ≤ 4*Rn)
    nlinarith only [h]
  have hbig : 8*u ≤ (2*(Rn+N+2))^2 := by
    have hle : Rn ≤ Rn+N+2 := by linarith only [hNnonneg]
    have hsq : Rn^2 ≤ (Rn+N+2)^2 := pow_le_pow_left₀ (le_of_lt hRnpos) hle 2
    linarith only [h8u_Rns, h4Rn2, hsq]
  set L : ℝ := Real.log (2*(Rn+N+2)) with hLdef
  set LogC : ℝ := Real.log (2*((C0:ℝ)+2)) with hLogCdef
  set LogM : ℝ := Real.log ((M:ℝ)+2) with hLogMdef
  set Nr : ℝ := N^((3:ℝ)/2) with hNrdef
  have hs3 : s^3 = s*N := by rw [pow_succ, hssq]; ring
  have hNr_eq : Nr = s^3 := by
    rw [hNrdef, show (3:ℝ)/2 = 1/2 + 1 by norm_num, Real.rpow_add hNpos, Real.rpow_one,
        ← Real.sqrt_eq_rpow, ← hsdef]
    rw [hs3]
  have hNr_nonneg : 0 ≤ Nr := by rw [hNrdef]; exact Real.rpow_nonneg hNnonneg _
  have hL_ge1 : 1 ≤ L := by
    rw [hLdef]
    have h12 : (12:ℝ) ≤ 2*(Rn+N+2) := by linarith
    have hlog12 : (1:ℝ) ≤ Real.log 12 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 12)]
      linarith only [Real.exp_one_lt_three]
    exact le_trans hlog12 (Real.log_le_log (by norm_num) h12)
  have hL_nonneg : 0 ≤ L := le_trans zero_le_one hL_ge1
  have hlogC : LogC ≤ 2*L := by
    rw [hLogCdef, hLdef]
    have h1 : 2*((C0:ℝ)+2) ≤ (2*(Rn+N+2))^2 := le_trans h8u hbig
    have hpos : 0 < 2*((C0:ℝ)+2) := by positivity
    calc Real.log (2*((C0:ℝ)+2)) ≤ Real.log ((2*(Rn+N+2))^2) := Real.log_le_log hpos h1
      _ = 2 * Real.log (2*(Rn+N+2)) := by rw [Real.log_pow]; norm_num
  have hLogC_nonneg : 0 ≤ LogC := by
    rw [hLogCdef]; apply Real.log_nonneg
    have hx : (1:ℝ) ≤ C0 := by exact_mod_cast hC0
    linarith only [hx]
  have hLogCpow : LogC^510 ≤ 2^510 * L^510 := by
    have h := pow_le_pow_left₀ hLogC_nonneg hlogC 510
    rwa [mul_pow] at h
  have hM_ge0 : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have hM_le_5s : (M:ℝ) ≤ 5*s := by linarith only [hM, hs1]
  have hM1_le_6s : (M:ℝ)+1 ≤ 6*s := by linarith only [hM, hs1]
  have h2M : 2*(M:ℝ)*((M:ℝ)+1) ≤ 60*s^2 := by
    have h3 : (M:ℝ)*((M:ℝ)+1) ≤ (5*s)*(6*s) := by
      calc (M:ℝ)*((M:ℝ)+1) ≤ (5*s)*((M:ℝ)+1) :=
              mul_le_mul_of_nonneg_right hM_le_5s (by positivity)
        _ ≤ (5*s)*(6*s) := mul_le_mul_of_nonneg_left hM1_le_6s (by positivity)
    nlinarith only [h3]
  have h4M2 : 4*(M:ℝ)^2 ≤ 100*s^2 := by
    have h := pow_le_pow_left₀ hM_ge0 hM_le_5s 2
    nlinarith only [h]
  have h2M1_le : 2*(M:ℝ)+1 ≤ 11*s := by linarith only [hM, hs1]
  have h2M1sq : (2*(M:ℝ)+1)^2 ≤ 121*s^2 := by
    have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 2*(M:ℝ)+1) h2M1_le 2
    nlinarith only [h]
  have hlogM : LogM ≤ L := by
    rw [hLogMdef, hLdef]
    apply Real.log_le_log (by positivity)
    linarith only [hM, hRn2, hs0, hNnonneg]
  have hLogM_nonneg : 0 ≤ LogM := by
    rw [hLogMdef]; apply Real.log_nonneg; linarith only [hM_ge0]
  have hLogMsq : LogM^2 ≤ L^2 := pow_le_pow_left₀ hLogM_nonneg hlogM 2
  have hu_le_Rn : u ≤ Rn := by
    have hsq : u^2 ≤ Rn^2 := by
      rw [hu_sq]
      have h := mul_le_mul_of_nonneg_left hs_le_Rn (le_of_lt hRnpos)
      nlinarith only [h]
    have h2 : |u| ≤ |Rn| := (sq_le_sq).mp hsq
    rwa [abs_of_nonneg hu_nonneg, abs_of_nonneg (le_of_lt hRnpos)] at h2
  have hC0_le_4Rn : (C0:ℝ) ≤ 4*Rn := by linarith only [hC0_le, hu_le_Rn, hRn2']
  have hMle : (M:ℝ) ≤ 3*s+2 := by linarith only [hM]
  have hMC0 : (M:ℝ)+2+(C0:ℝ) ≤ 11*Rn := by
    linarith only [hMle, hs_le_Rn, hC0_le_4Rn, hRn2']
  have hL2 : 1 ≤ L^2 := by nlinarith only [hL_ge1]
  have hL512_514 : L^512 ≤ L^514 := pow_le_pow_right₀ hL_ge1 (by norm_num)
  have hL514_ge1 : 1 ≤ L^514 := one_le_pow₀ hL_ge1
  -- bracket bound
  have hbracket : 2*(M:ℝ)*Ch*((M:ℝ)+1)*LogM^2 + 4*(M:ℝ)^2 ≤ (Ch+1)*(160*s^2*L^2) := by
    have hA : 2*(M:ℝ)*Ch*((M:ℝ)+1)*LogM^2 ≤ (Ch+1)*(2*(M:ℝ)*((M:ℝ)+1)*LogM^2) := by
      have hnn : 0 ≤ 2*(M:ℝ)*((M:ℝ)+1)*LogM^2 := by positivity
      have h := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (zero_le_one : (0:ℝ) ≤ 1) : Ch ≤ Ch + 1) hnn
      have e1 : 2*(M:ℝ)*Ch*((M:ℝ)+1)*LogM^2 = (2*(M:ℝ)*((M:ℝ)+1)*LogM^2)*Ch := by ring
      have e2 : (Ch+1)*(2*(M:ℝ)*((M:ℝ)+1)*LogM^2) = (2*(M:ℝ)*((M:ℝ)+1)*LogM^2)*(Ch+1) := by ring
      rw [e1, e2]; exact h
    have hB : (Ch+1)*(2*(M:ℝ)*((M:ℝ)+1)*LogM^2) ≤ (Ch+1)*(60*s^2*L^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc 2*(M:ℝ)*((M:ℝ)+1)*LogM^2 ≤ 2*(M:ℝ)*((M:ℝ)+1)*L^2 := by
            apply mul_le_mul_of_nonneg_left hLogMsq; positivity
        _ ≤ 60*s^2*L^2 := mul_le_mul_of_nonneg_right h2M (by positivity)
    have hC1 : 4*(M:ℝ)^2 ≤ (Ch+1)*(4*(M:ℝ)^2) :=
      le_mul_of_one_le_left (by positivity) (by linarith only [hCh])
    have hC2 : (Ch+1)*(4*(M:ℝ)^2) ≤ (Ch+1)*(100*s^2*L^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc 4*(M:ℝ)^2 ≤ 100*s^2 := h4M2
        _ ≤ 100*s^2*L^2 := le_mul_of_one_le_right (by positivity) hL2
    have hterm1 : 2*(M:ℝ)*Ch*((M:ℝ)+1)*LogM^2 ≤ (Ch+1)*(60*s^2*L^2) := le_trans hA hB
    have hterm2 : 4*(M:ℝ)^2 ≤ (Ch+1)*(100*s^2*L^2) := le_trans hC1 hC2
    calc 2*(M:ℝ)*Ch*((M:ℝ)+1)*LogM^2 + 4*(M:ℝ)^2
        ≤ (Ch+1)*(60*s^2*L^2) + (Ch+1)*(100*s^2*L^2) := add_le_add hterm1 hterm2
      _ = (Ch+1)*(160*s^2*L^2) := by ring
  have hBnn : 0 ≤ 2*(M:ℝ)*Ch*((M:ℝ)+1)*LogM^2 + 4*(M:ℝ)^2 := by positivity
  have h13nn : 0 ≤ 13*(Rn*s) := by positivity
  have h2Ct_nn : 0 ≤ 2*Ct := by linarith only [hCt]
  have hA2_nn : 0 ≤ ((C0:ℝ)+1)^2 := sq_nonneg _
  have hLogCpow_nn : 0 ≤ LogC^510 := pow_nonneg hLogC_nonneg 510
  have h2L510nn : 0 ≤ 2^510 * L^510 := mul_nonneg (by positivity) (pow_nonneg hL_nonneg 510)
  have hstep1 : 2*Ct*((C0:ℝ)+1)^2*LogC^510*(2*(M:ℝ)*Ch*((M:ℝ)+1)*LogM^2 + 4*(M:ℝ)^2)
      ≤ 2*Ct*(13*(Rn*s))*(2^510*L^510)*((Ch+1)*(160*s^2*L^2)) :=
    FI_mul4 le_rfl hC0sq hLogCpow hbracket hA2_nn hLogCpow_nn hBnn h2Ct_nn h13nn h2L510nn
  have hctch : Ct*(Ch+1) ≤ (Ct+1)*(Ch+1)*(Cr+1) := by
    have h1 : Ct ≤ Ct+1 := by linarith only []
    have h2 : (1:ℝ) ≤ Cr+1 := by linarith only [hCr]
    have hCh1nn' : (0:ℝ) ≤ Ch+1 := by linarith only [hCh]
    have step1 : Ct*(Ch+1) ≤ (Ct+1)*(Ch+1) := mul_le_mul_of_nonneg_right h1 hCh1nn'
    have step2 : (Ct+1)*(Ch+1) ≤ (Ct+1)*(Ch+1)*(Cr+1) := by
      have hnn : 0 ≤ (Ct+1)*(Ch+1) := mul_nonneg (by linarith only [hCt]) hCh1nn'
      have hh := mul_le_mul_of_nonneg_left h2 hnn
      simpa using hh
    linarith only [step1, step2]
  have hstep2 : 2*Ct*(13*(Rn*s))*(2^510*L^510)*((Ch+1)*(160*s^2*L^2))
      ≤ 4160*(2:ℝ)^510*((Ct+1)*(Ch+1)*(Cr+1)*Rn*Nr*L^514) := by
    have heq : 2*Ct*(13*(Rn*s))*(2^510*L^510)*((Ch+1)*(160*s^2*L^2))
        = 4160*(2:ℝ)^510*(Ct*(Ch+1))*Rn*s^3*L^512 := by ring
    rw [heq, hNr_eq]
    have hpfull_nonneg : 0 ≤ (Ct+1)*(Ch+1)*(Cr+1) := by positivity
    have hL512nn : 0 ≤ L^512 := pow_nonneg hL_nonneg 512
    have hmono1 : (Ct*(Ch+1))*L^512 ≤ ((Ct+1)*(Ch+1)*(Cr+1))*L^512 :=
      mul_le_mul_of_nonneg_right hctch hL512nn
    have hmono2 : ((Ct+1)*(Ch+1)*(Cr+1))*L^512 ≤ ((Ct+1)*(Ch+1)*(Cr+1))*L^514 :=
      mul_le_mul_of_nonneg_left hL512_514 hpfull_nonneg
    have hmono : (Ct*(Ch+1))*L^512 ≤ ((Ct+1)*(Ch+1)*(Cr+1))*L^514 := le_trans hmono1 hmono2
    have hrest : 0 ≤ 4160*(2:ℝ)^510*Rn*s^3 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (le_of_lt hRnpos))
        (pow_nonneg hs0 3)
    have hprod := mul_le_mul_of_nonneg_right hmono hrest
    nlinarith only [hprod]
  have hLHS1 : 2*Ct*((C0:ℝ)+1)^2*LogC^510*(2*(M:ℝ)*Ch*((M:ℝ)+1)*LogM^2 + 4*(M:ℝ)^2)
      ≤ 4160*(2:ℝ)^510*((Ct+1)*(Ch+1)*(Cr+1)*Rn*Nr*L^514) := le_trans hstep1 hstep2
  have h2a : Cr*((M:ℝ)+1)*((M:ℝ)+2+(C0:ℝ))*(2*(M:ℝ)+1)^2 ≤ Cr*(6*s)*(11*Rn)*(121*s^2) :=
    FI_mul4 le_rfl hM1_le_6s hMC0 h2M1sq (by positivity) (by positivity) (sq_nonneg _)
      (by linarith only [hCr]) (by positivity) (by positivity)
  have h2b : Cr*(6*s)*(11*Rn)*(121*s^2) = 7986*Cr*Rn*s^3 := by ring
  have h2c : 7986*Cr*Rn*s^3 ≤ 7986*Cr*Rn*s^3*L^514 :=
    le_mul_of_one_le_right (by positivity) hL514_ge1
  have hCrp : Cr ≤ (Ct+1)*(Ch+1)*(Cr+1) := by
    have h1 : (1:ℝ) ≤ Ct+1 := by linarith only [hCt]
    have h2 : (1:ℝ) ≤ Ch+1 := by linarith only [hCh]
    have h3 : Cr ≤ Cr+1 := by linarith only []
    have hprod1 : (1:ℝ) ≤ (Ct+1)*(Ch+1) := by nlinarith only [h1, h2]
    have hstep : (1:ℝ)*(Cr+1) ≤ ((Ct+1)*(Ch+1))*(Cr+1) :=
      mul_le_mul_of_nonneg_right hprod1 (by linarith only [hCr])
    linarith only [hstep, h3]
  have h2d : 7986*Cr*Rn*s^3*L^514 ≤ 7986*((Ct+1)*(Ch+1)*(Cr+1))*Rn*s^3*L^514 := by
    have hle : 7986*Cr ≤ 7986*((Ct+1)*(Ch+1)*(Cr+1)) :=
      mul_le_mul_of_nonneg_left hCrp (by norm_num)
    have hfac : 0 ≤ Rn*s^3*L^514 :=
      mul_nonneg (mul_nonneg (le_of_lt hRnpos) (pow_nonneg hs0 3)) (pow_nonneg hL_nonneg 514)
    have hh := mul_le_mul_of_nonneg_right hle hfac
    nlinarith only [hh]
  have h2e : 7986*((Ct+1)*(Ch+1)*(Cr+1))*Rn*s^3*L^514
      = 7986*((Ct+1)*(Ch+1)*(Cr+1)*Rn*Nr*L^514) := by rw [hNr_eq]; ring
  have hLHS2 : Cr*((M:ℝ)+1)*((M:ℝ)+2+(C0:ℝ))*(2*(M:ℝ)+1)^2
      ≤ 7986*((Ct+1)*(Ch+1)*(Cr+1)*Rn*Nr*L^514) := by
    calc Cr*((M:ℝ)+1)*((M:ℝ)+2+(C0:ℝ))*(2*(M:ℝ)+1)^2 ≤ Cr*(6*s)*(11*Rn)*(121*s^2) := h2a
      _ = 7986*Cr*Rn*s^3 := h2b
      _ ≤ 7986*Cr*Rn*s^3*L^514 := h2c
      _ ≤ 7986*((Ct+1)*(Ch+1)*(Cr+1))*Rn*s^3*L^514 := h2d
      _ = 7986*((Ct+1)*(Ch+1)*(Cr+1)*Rn*Nr*L^514) := h2e
  have hconst : (4160:ℝ)*(2:ℝ)^510 + 7986 ≤ 2^540 := by
    set_option exponentiation.threshold 600 in norm_num
  have hPnn : 0 ≤ (Ct+1)*(Ch+1)*(Cr+1)*Rn*Nr*L^514 := by
    have hh : 0 ≤ (Ct+1)*(Ch+1)*(Cr+1) := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg hh (le_of_lt hRnpos)) hNr_nonneg)
      (pow_nonneg hL_nonneg 514)
  have step3 : 2^540 * ((Ct+1)*(Ch+1)*(Cr+1)*Rn*Nr*L^514)
      ≤ (2^540*(Ct+1)*(Ch+1)*(Cr+1)+2)*(Rn*Nr)*L^514 := by
    have hle : 2^540 * ((Ct+1)*(Ch+1)*(Cr+1)) ≤ 2^540*((Ct+1)*(Ch+1)*(Cr+1))+2 :=
      by linarith only []
    have hnn : 0 ≤ (Rn*Nr)*L^514 :=
      mul_nonneg (mul_nonneg (le_of_lt hRnpos) hNr_nonneg) (pow_nonneg hL_nonneg 514)
    have hh := mul_le_mul_of_nonneg_right hle hnn
    nlinarith only [hh]
  calc 2*Ct*((C0:ℝ)+1)^2*LogC^510*(2*(M:ℝ)*Ch*((M:ℝ)+1)*LogM^2 + 4*(M:ℝ)^2)
        + Cr*((M:ℝ)+1)*((M:ℝ)+2+(C0:ℝ))*(2*(M:ℝ)+1)^2
      _ ≤ 4160*(2:ℝ)^510*((Ct+1)*(Ch+1)*(Cr+1)*Rn*Nr*L^514)
            + 7986*((Ct+1)*(Ch+1)*(Cr+1)*Rn*Nr*L^514) := add_le_add hLHS1 hLHS2
      _ = (4160*(2:ℝ)^510 + 7986)*((Ct+1)*(Ch+1)*(Cr+1)*Rn*Nr*L^514) := by ring
      _ ≤ 2^540*((Ct+1)*(Ch+1)*(Cr+1)*Rn*Nr*L^514) := mul_le_mul_of_nonneg_right hconst hPnn
      _ ≤ (2^540*(Ct+1)*(Ch+1)*(Cr+1)+2)*(Rn*Nr)*L^514 := step3

end Work.FIArea1
