import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.EtailE.Basic
import Submission.Work.Asymptotics.ETailE_one
import Submission.Work.Asymptotics.KPlus_funnel_tail_eight
import Submission.Work.Asymptotics.KMinus_funnel_tail_eight
import Submission.Work.Asymptotics.KPlus_funnel_tail_twentyfour
import Submission.Work.Asymptotics.KMinus_funnel_tail_twentyfour
import Submission.Work.Kernels.All
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Kernels.KernelFacts.KMinus_Sopm
import Submission.Work.Asymptotics.Compact.gfun_eq

noncomputable section

open UpperHalfPlane ModularGroup
open Work.Kernels

namespace Work.Asymptotics

/-! ## The arithmetic of combining the two componentwise tails

The two deviations `D₊ = K₊ - 𝒢₊` and `D₋ = K₋ - 𝒢₋` are each bounded on the funnel by
`C (scale τ)^N (1+t)^M e^{-π(t-Im τ)}`; after the `S`-transport the prefactor `‖S•w‖^{2·(d/2)}`
contributes `(scale w)^{2·(d/2)}` and `scale (S•w)` costs a factor `3`.  This lemma performs the
resulting bookkeeping: from `u ≤ s`, `sτ ≤ 3s`, `1 ≤ s`, `1 ≤ tt`, it bounds the average of the
two transported expressions. -/
private lemma combine_two {u s sτ tt e CP NP MP CM NM MM : ℝ} {j : ℕ}
    (hu0 : 0 ≤ u) (hu : u ≤ s) (hs1 : 1 ≤ s) (hsτ0 : 0 ≤ sτ) (hsτ : sτ ≤ 3 * s)
    (hNP0 : 0 ≤ NP) (hNM0 : 0 ≤ NM)
    (htt1 : 1 ≤ tt) (he0 : 0 ≤ e) (hCP : 0 ≤ CP) (hCM : 0 ≤ CM) :
    (u ^ j * (CP * sτ ^ NP * tt ^ MP * e) + u ^ j * (CM * sτ ^ NM * tt ^ MM * e)) / 2
      ≤ ((CP + CM) * 3 ^ (max NP NM) + 1) * s ^ (max NP NM + (j:ℝ)) * tt ^ (max MP MM) * e := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs1
  set K := max NP NM with hK
  set L := max MP MM with hL
  have h3s1 : (1:ℝ) ≤ 3 * s := by linarith
  have huj : u ^ j ≤ s ^ j := pow_le_pow_left₀ hu0 hu j
  have hbase : ∀ NX, 0 ≤ NX → NX ≤ K → sτ ^ NX ≤ 3 ^ K * s ^ K := by
    intro NX hNX0 hNX
    have a : sτ ^ NX ≤ (3*s) ^ NX := Real.rpow_le_rpow hsτ0 hsτ hNX0
    have b : (3*s) ^ NX ≤ (3*s) ^ K := Real.rpow_le_rpow_of_exponent_le h3s1 hNX
    have c : (3*s) ^ K = 3 ^ K * s ^ K := Real.mul_rpow (by norm_num) (le_of_lt hs0)
    linarith [a, b, c]
  have key : ∀ (CX NX MX : ℝ), 0 ≤ CX → 0 ≤ NX → NX ≤ K → MX ≤ L →
      u ^ j * (CX * sτ ^ NX * tt ^ MX * e) ≤ CX * 3 ^ K * s ^ (K + (j:ℝ)) * tt ^ L * e := by
    intro CX NX MX hCX hNX0 hNX hMX
    have ha : sτ ^ NX * tt ^ MX ≤ (3 ^ K * s ^ K) * tt ^ L :=
      mul_le_mul (hbase NX hNX0 hNX) (Real.rpow_le_rpow_of_exponent_le htt1 hMX)
        (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ tt) MX)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) K) (Real.rpow_nonneg hs0.le K))
    have hb : u ^ j * (sτ ^ NX * tt ^ MX) ≤ s ^ j * ((3 ^ K * s ^ K) * tt ^ L) :=
      mul_le_mul huj ha
        (mul_nonneg (Real.rpow_nonneg hsτ0 NX) (Real.rpow_nonneg (by linarith) MX))
        (pow_nonneg hs0.le j)
    have hspl : s ^ j * s ^ K = s ^ (K + (j:ℝ)) := by
      rw [← Real.rpow_natCast s j, mul_comm, ← Real.rpow_add hs0, add_comm]
    calc u ^ j * (CX * sτ ^ NX * tt ^ MX * e)
        = CX * (u ^ j * (sτ ^ NX * tt ^ MX)) * e := by ring
      _ ≤ CX * (s ^ j * ((3 ^ K * s ^ K) * tt ^ L)) * e :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hCX) he0
      _ = CX * 3 ^ K * s ^ (K + (j:ℝ)) * tt ^ L * e := by
            rw [show CX * (s ^ j * ((3 ^ K * s ^ K) * tt ^ L)) * e
                = CX * 3 ^ K * (s ^ j * s ^ K) * tt ^ L * e from by ring, hspl]
  have t1 := key CP NP MP hCP hNP0 (le_max_left _ _) (le_max_left _ _)
  have t2 := key CM NM MM hCM hNM0 (le_max_right _ _) (le_max_right _ _)
  have hsum := add_le_add t1 t2
  have hR : (0:ℝ) ≤ s ^ (K + (j:ℝ)) * tt ^ L * e :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) (Real.rpow_nonneg (by linarith) _)) he0
  have h2K : (0:ℝ) ≤ (CP + CM) * 3 ^ K :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (by norm_num) K)
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  have hcomb2 : CP * 3 ^ K * s ^ (K + (j:ℝ)) * tt ^ L * e
        + CM * 3 ^ K * s ^ (K + (j:ℝ)) * tt ^ L * e
      ≤ ((CP + CM) * 3 ^ K + 1) * s ^ (K + (j:ℝ)) * tt ^ L * e * 2 := by
    nlinarith [hR, h2K, mul_nonneg h2K hR]
  linarith [hsum, hcomb2]

/-- **The sharp cusp-`i∞` deviation bound on the cusp-`0` tile `E = KEpsilon`.**

For `w ∈ E` and `t ≥ Im (S • w) + 1` the CKMRV kernel differs from its cusp-`i∞` model
`Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d)` by
`O((scale w)^N (1+t)^M e^{-π (t - Im (S • w))})` — the rate is measured *from the pole height*
`Im (S • w)`, not from `0`.

This is derivable from the componentwise tails
`Work.Asymptotics.KPlus_funnel_tail_eight` (rate `e^{-π(t - Im τ)}`),
`KMinus_funnel_tail_eight`, and their `d = 24` analogues, by the `S`-transport of
`Work.Kernels.KernelFacts.KPlus_S_smul` (which uses `Gplus_S_smul`, `Gminus_S_smul`,
`E_norm_S_le_scale`, `E_scale_S_le`), *without* the conversion `e^{-π(t - Im τ)} ↦ e^{-πt}`
that forces `t ≥ 2 Im τ`.  The combination for `Kfun = (K₊ + K₋)/2` and
`Aexp (Gcusp ℓ d) = (𝒢₊ + 𝒢₋)/2` (valid up to the sign convention of `Compact.Gminus`, fixed by
`Compact.gfun_eq`) keeps the *slower* of the two rates.

Since `Im (S • w) + 1 ≤ scale w` (`Work.Asymptotics.im_S_smul_add_one_le_scale`), this also gives
the tail for `t ≥ scale w`. -/
theorem E_deviation_sharp (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        (ModularGroup.S • w).im + 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) := by
  rcases hd with h8 | h24
  · subst h8
    obtain ⟨CP, NP, MP, hCP, hNP, hMP, hPt⟩ := KPlus_funnel_tail_eight
    obtain ⟨CM, NM, MM, hCM, hNM, hMM, hMt⟩ := KMinus_funnel_tail_eight ℓ
    refine ⟨(CP + CM) * 3 ^ (max NP NM) + 1, max NP NM + 4, max MP MM,
      by positivity, ?_, ?_, ?_⟩
    · have := le_trans hNP (le_max_left (NP:ℝ) NM); linarith
    · exact le_trans hMP (le_max_left (MP:ℝ) MM)
    · intro w t hw hwt
      have hτF : Funnel (ModularGroup.S • w) := S_smul_mem_funnel hw
      have h2im : (2:ℝ) ≤ (ModularGroup.S • w).im := hw.2
      have ht0 : (0:ℝ) < t := by linarith
      set z : ℍ := imagAxis t ht0 with hzdef
      have hz : (z : ℂ) = (t : ℂ) * Complex.I := rfl
      have hP := hPt (ModularGroup.S • w) z t hτF hwt hz
      have hM := hMt (ModularGroup.S • w) z t hτF hwt hz
      -- the four `S`-laws, at `τ = S • w`
      have hKw : KPlus 8 w z = -(((ModularGroup.S • w : ℍ)) : ℂ) ^ 4
          * KPlus 8 (ModularGroup.S • w) z := by
        have h := Work.Kernels.KernelFacts.KPlus_S_smul 8 (Or.inl rfl) z (ModularGroup.S • w)
        rwa [S_smul_S_smul] at h
      have hGpw : Compact.Gplus 8 w z = -(((ModularGroup.S • w : ℍ)) : ℂ) ^ 4
          * Compact.Gplus 8 (ModularGroup.S • w) z := by
        have h := Gplus_S_smul 8 (Or.inl rfl) (ModularGroup.S • w) z
        rwa [S_smul_S_smul] at h
      have hKw' : KMinus ℓ 8 w z = (((ModularGroup.S • w : ℍ)) : ℂ) ^ 4
          * KMinus ℓ 8 (ModularGroup.S • w) z := by
        have h := Work.Kernels.KernelFacts.KMinus_S_smul ℓ 8 (Or.inl rfl) z (ModularGroup.S • w)
        rwa [S_smul_S_smul] at h
      have hGmw : Compact.Gminus 8 ℓ w z = (((ModularGroup.S • w : ℍ)) : ℂ) ^ 4
          * Compact.Gminus 8 ℓ (ModularGroup.S • w) z := by
        have h := Gminus_S_smul ℓ 8 (Or.inl rfl) (ModularGroup.S • w) z
        rwa [S_smul_S_smul] at h
      -- the two deviations as `S`-transports
      have hPnorm : ‖KPlus 8 w z - Compact.Gplus 8 w z‖
          = ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 4
              * ‖KPlus 8 (ModularGroup.S • w) z - Compact.Gplus 8 (ModularGroup.S • w) z‖ := by
        rw [show KPlus 8 w z - Compact.Gplus 8 w z
            = -(((ModularGroup.S • w : ℍ)) : ℂ) ^ 4
                * (KPlus 8 (ModularGroup.S • w) z - Compact.Gplus 8 (ModularGroup.S • w) z)
              from by rw [hKw, hGpw]; ring,
          norm_mul, norm_neg, norm_pow]
      have hMnorm : ‖KMinus ℓ 8 w z - Compact.Gminus 8 ℓ w z‖
          = ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 4
              * ‖KMinus ℓ 8 (ModularGroup.S • w) z - Compact.Gminus 8 ℓ (ModularGroup.S • w) z‖ := by
        rw [show KMinus ℓ 8 w z - Compact.Gminus 8 ℓ w z
            = (((ModularGroup.S • w : ℍ)) : ℂ) ^ 4
                * (KMinus ℓ 8 (ModularGroup.S • w) z - Compact.Gminus 8 ℓ (ModularGroup.S • w) z)
              from by rw [hKw', hGmw]; ring,
          norm_mul, norm_pow]
      -- `Aexp (Gcusp ℓ 8) = Gfun = (𝒢₊ + 𝒢₋)/2`
      have hGfun : Compact.Gfun 8 ℓ w z
          = (Compact.Gplus 8 w z + Compact.Gminus 8 ℓ w z) / 2 := by
        have h := Compact.gfun_eq ℓ 8 (Or.inl rfl) w z
        rw [eq_div_iff (by norm_num : (2:ℂ) ≠ 0), mul_comm]
        exact h.symm
      have hKax : Kaxis (Kfun ℓ 8) w t = Kfun ℓ 8 w z := by rw [Kaxis, dif_pos ht0]
      have hAex : Aexp (Gcusp ℓ 8) w t = Compact.Gfun 8 ℓ w z :=
        Aexp_Gcusp_eq_Gfun ℓ 8 w t ht0
      have hsplit : Kaxis (Kfun ℓ 8) w t - Aexp (Gcusp ℓ 8) w t
          = ((KPlus 8 w z - Compact.Gplus 8 w z)
              + (KMinus ℓ 8 w z - Compact.Gminus 8 ℓ w z)) / 2 := by
        simp only [hKax, hAex, hGfun, Kfun]
        ring
      have htri : ‖Kaxis (Kfun ℓ 8) w t - Aexp (Gcusp ℓ 8) w t‖
          ≤ (‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 4
                * ‖KPlus 8 (ModularGroup.S • w) z - Compact.Gplus 8 (ModularGroup.S • w) z‖
              + ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 4
                * ‖KMinus ℓ 8 (ModularGroup.S • w) z
                    - Compact.Gminus 8 ℓ (ModularGroup.S • w) z‖) / 2 := by
        rw [hsplit, norm_div, show ‖(2:ℂ)‖ = 2 by norm_num]
        refine le_trans (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)) ?_
        rw [hPnorm, hMnorm]
      refine le_trans htri ?_
      have hcomb := combine_two (u := ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖)
        (s := Work.Kernels.scale w) (sτ := Work.Kernels.scale (ModularGroup.S • w))
        (tt := 1 + t) (e := Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))))
        (CP := CP) (NP := NP) (MP := MP) (CM := CM) (NM := NM) (MM := MM) (j := 4)
        (norm_nonneg _) (EtailE.E_norm_S_le_scale w) (one_le_scale w) ((scale_pos _).le)
        (EtailE.E_scale_S_le hw) hNP hNM (by linarith [ht0]) (Real.exp_pos _).le hCP.le hCM.le
      refine le_trans ?_ hcomb
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      exact add_le_add (mul_le_mul_of_nonneg_left hP (by positivity))
        (mul_le_mul_of_nonneg_left hM (by positivity))
  · subst h24
    obtain ⟨CP, NP, MP, hCP, hNP, hMP, hPt⟩ := KPlus_funnel_tail_twentyfour
    obtain ⟨CM, NM, MM, hCM, hNM, hMM, hMt⟩ := KMinus_funnel_tail_twentyfour ℓ
    refine ⟨(CP + CM) * 3 ^ (max NP NM) + 1, max NP NM + 12, max MP MM,
      by positivity, ?_, ?_, ?_⟩
    · have := le_trans hNP (le_max_left (NP:ℝ) NM); linarith
    · exact le_trans hMP (le_max_left (MP:ℝ) MM)
    · intro w t hw hwt
      have hτF : Funnel (ModularGroup.S • w) := S_smul_mem_funnel hw
      have h2im : (2:ℝ) ≤ (ModularGroup.S • w).im := hw.2
      have ht0 : (0:ℝ) < t := by linarith
      set z : ℍ := imagAxis t ht0 with hzdef
      have hz : (z : ℂ) = (t : ℂ) * Complex.I := rfl
      have hP := hPt (ModularGroup.S • w) z t hτF hwt hz
      have hM := hMt (ModularGroup.S • w) z t hτF hwt hz
      have hKw : KPlus 24 w z = -(((ModularGroup.S • w : ℍ)) : ℂ) ^ 12
          * KPlus 24 (ModularGroup.S • w) z := by
        have h := Work.Kernels.KernelFacts.KPlus_S_smul 24 (Or.inr rfl) z (ModularGroup.S • w)
        rwa [S_smul_S_smul] at h
      have hGpw : Compact.Gplus 24 w z = -(((ModularGroup.S • w : ℍ)) : ℂ) ^ 12
          * Compact.Gplus 24 (ModularGroup.S • w) z := by
        have h := Gplus_S_smul 24 (Or.inr rfl) (ModularGroup.S • w) z
        rwa [S_smul_S_smul] at h
      have hKw' : KMinus ℓ 24 w z = (((ModularGroup.S • w : ℍ)) : ℂ) ^ 12
          * KMinus ℓ 24 (ModularGroup.S • w) z := by
        have h := Work.Kernels.KernelFacts.KMinus_S_smul ℓ 24 (Or.inr rfl) z (ModularGroup.S • w)
        rwa [S_smul_S_smul] at h
      have hGmw : Compact.Gminus 24 ℓ w z = (((ModularGroup.S • w : ℍ)) : ℂ) ^ 12
          * Compact.Gminus 24 ℓ (ModularGroup.S • w) z := by
        have h := Gminus_S_smul ℓ 24 (Or.inr rfl) (ModularGroup.S • w) z
        rwa [S_smul_S_smul] at h
      have hPnorm : ‖KPlus 24 w z - Compact.Gplus 24 w z‖
          = ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 12
              * ‖KPlus 24 (ModularGroup.S • w) z - Compact.Gplus 24 (ModularGroup.S • w) z‖ := by
        rw [show KPlus 24 w z - Compact.Gplus 24 w z
            = -(((ModularGroup.S • w : ℍ)) : ℂ) ^ 12
                * (KPlus 24 (ModularGroup.S • w) z - Compact.Gplus 24 (ModularGroup.S • w) z)
              from by rw [hKw, hGpw]; ring,
          norm_mul, norm_neg, norm_pow]
      have hMnorm : ‖KMinus ℓ 24 w z - Compact.Gminus 24 ℓ w z‖
          = ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 12
              * ‖KMinus ℓ 24 (ModularGroup.S • w) z - Compact.Gminus 24 ℓ (ModularGroup.S • w) z‖ := by
        rw [show KMinus ℓ 24 w z - Compact.Gminus 24 ℓ w z
            = (((ModularGroup.S • w : ℍ)) : ℂ) ^ 12
                * (KMinus ℓ 24 (ModularGroup.S • w) z - Compact.Gminus 24 ℓ (ModularGroup.S • w) z)
              from by rw [hKw', hGmw]; ring,
          norm_mul, norm_pow]
      have hGfun : Compact.Gfun 24 ℓ w z
          = (Compact.Gplus 24 w z + Compact.Gminus 24 ℓ w z) / 2 := by
        have h := Compact.gfun_eq ℓ 24 (Or.inr rfl) w z
        rw [eq_div_iff (by norm_num : (2:ℂ) ≠ 0), mul_comm]
        exact h.symm
      have hKax : Kaxis (Kfun ℓ 24) w t = Kfun ℓ 24 w z := by rw [Kaxis, dif_pos ht0]
      have hAex : Aexp (Gcusp ℓ 24) w t = Compact.Gfun 24 ℓ w z :=
        Aexp_Gcusp_eq_Gfun ℓ 24 w t ht0
      have hsplit : Kaxis (Kfun ℓ 24) w t - Aexp (Gcusp ℓ 24) w t
          = ((KPlus 24 w z - Compact.Gplus 24 w z)
              + (KMinus ℓ 24 w z - Compact.Gminus 24 ℓ w z)) / 2 := by
        simp only [hKax, hAex, hGfun, Kfun]
        ring
      have htri : ‖Kaxis (Kfun ℓ 24) w t - Aexp (Gcusp ℓ 24) w t‖
          ≤ (‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 12
                * ‖KPlus 24 (ModularGroup.S • w) z - Compact.Gplus 24 (ModularGroup.S • w) z‖
              + ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 12
                * ‖KMinus ℓ 24 (ModularGroup.S • w) z
                    - Compact.Gminus 24 ℓ (ModularGroup.S • w) z‖) / 2 := by
        rw [hsplit, norm_div, show ‖(2:ℂ)‖ = 2 by norm_num]
        refine le_trans (div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)) ?_
        rw [hPnorm, hMnorm]
      refine le_trans htri ?_
      have hcomb := combine_two (u := ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖)
        (s := Work.Kernels.scale w) (sτ := Work.Kernels.scale (ModularGroup.S • w))
        (tt := 1 + t) (e := Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))))
        (CP := CP) (NP := NP) (MP := MP) (CM := CM) (NM := NM) (MM := MM) (j := 12)
        (norm_nonneg _) (EtailE.E_norm_S_le_scale w) (one_le_scale w) ((scale_pos _).le)
        (EtailE.E_scale_S_le hw) hNP hNM (by linarith [ht0]) (Real.exp_pos _).le hCP.le hCM.le
      refine le_trans ?_ hcomb
      refine div_le_div_of_nonneg_right ?_ (by norm_num)
      exact add_le_add (mul_le_mul_of_nonneg_left hP (by positivity))
        (mul_le_mul_of_nonneg_left hM (by positivity))

end Work.Asymptotics
