import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Core.analyticAt_bottcher
import Submission.Work.Bottcher.Series.summable_bottcherTerm
import Submission.Work.Bottcher.Contraction.FarFoundation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000

open scoped ComplexConjugate

namespace Work.Bottcher.Contraction

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The leading term of the Böttcher series at infinity -/

private lemma head_log_le (c z : ℂ) (hc : ‖c‖ ≤ 2) (hz : 3 / 2 * (1 + ‖c‖) ≤ ‖z‖) :
    ‖(1 / 4 : ℂ) * (Complex.log (1 + Work.Bottcher.Core.nfG c z)
        - Work.Bottcher.Core.nfG c z + (Work.Bottcher.Core.nfG c z) ^ 2 / 2)‖
      ≤ (3 / 5) * ‖c‖ / ‖z‖ ^ 4 := by
  have hb : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hzpos : (0 : ℝ) < ‖z‖ := by
    have : (1 : ℝ) ≤ 1 + ‖c‖ := by linarith
    nlinarith
  have hR4 : (0 : ℝ) < ‖z‖ ^ 4 := by positivity
  have hu_small : ‖Work.Bottcher.Core.nfG c z‖ ≤ 1 / 2 := by
    refine (norm_nfG_le_div c z).trans ?_
    rw [div_le_iff₀ (by positivity)]
    have h3 : (9 / 4) * (1 + ‖c‖) ^ 2 - 2 * ‖c‖ ≤ ‖z‖ ^ 2 - 2 * ‖c‖ := by
      nlinarith
    have h4 : 0 ≤ (9 / 4) * (1 + ‖c‖) ^ 2 - 2 * ‖c‖ := by nlinarith
    have h5 : ((9 / 4) * (1 + ‖c‖) ^ 2 - 2 * ‖c‖) ^ 2 ≤ (‖z‖ ^ 2 - 2 * ‖c‖) ^ 2 :=
      pow_le_pow_left₀ h4 h3 2
    have h6 : 6 * ‖c‖ ^ 2 + 2 * ‖c‖ ≤ ((9 / 4) * (1 + ‖c‖) ^ 2 - 2 * ‖c‖) ^ 2 := by
      nlinarith [sq_nonneg ((9 / 4) * (1 + ‖c‖) ^ 2 - 2 * ‖c‖), hb, hc]
    nlinarith [h5, h6]
  have hn : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [norm_mul, hn]
  have hlog := norm_log_one_add_sub_self_add_sq_le hu_small
  have h2 : (1 / 4) * ‖Work.Bottcher.Core.nfG c z‖ ^ 3 ≤ (3 / 5) * ‖c‖ / ‖z‖ ^ 4 := by
    have h3 : ‖Work.Bottcher.Core.nfG c z‖
        ≤ (2 * ‖c‖ * ‖z‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖) / ‖z‖ ^ 4 := norm_nfG_le_div c z
    have h4 : ‖Work.Bottcher.Core.nfG c z‖ ^ 3
        ≤ ((2 * ‖c‖ * ‖z‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖) / ‖z‖ ^ 4) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg _) h3 3
    have h4' : ‖Work.Bottcher.Core.nfG c z‖ ^ 3
        ≤ (2 * ‖c‖ * ‖z‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖) ^ 3 / ‖z‖ ^ 12 := by
      refine h4.trans ?_
      rw [div_pow]
      have : (‖z‖ ^ 4) ^ 3 = ‖z‖ ^ 12 := by ring
      rw [this]
    have h5 := pow_three_le_twelve_fifths ‖c‖ ‖z‖ hb hc hz
    have hz12pos : (0 : ℝ) < ‖z‖ ^ 12 := by positivity
    have hm1 : (1 / 4) * ‖Work.Bottcher.Core.nfG c z‖ ^ 3
        ≤ (1 / 4) * ((2 * ‖c‖ * ‖z‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖) ^ 3 / ‖z‖ ^ 12) :=
      mul_le_mul_of_nonneg_left h4' (by norm_num)
    have hm2 : (1 / 4) * ((2 * ‖c‖ * ‖z‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖) ^ 3 / ‖z‖ ^ 12)
        ≤ (3 / 5) * ‖c‖ / ‖z‖ ^ 4 := by
      rw [show (1 / 4) * ((2 * ‖c‖ * ‖z‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖) ^ 3 / ‖z‖ ^ 12)
            = ((1 / 4) * (2 * ‖c‖ * ‖z‖ ^ 2 + ‖c‖ ^ 2 + ‖c‖) ^ 3) / ‖z‖ ^ 12 by ring]
      rw [div_le_div_iff₀ hz12pos hR4]
      have hm := mul_le_mul_of_nonneg_right h5 (by positivity : (0 : ℝ) ≤ (1 / 4) * ‖z‖ ^ 4)
      nlinarith [hm, hR4]
    linarith
  exact (mul_le_mul_of_nonneg_left hlog (by norm_num)).trans h2

private lemma head_z4_le (c z : ℂ) (hc : ‖c‖ ≤ 2) (hz : 3 / 2 * (1 + ‖c‖) ≤ ‖z‖) :
    ‖(c - (conj c) ^ 2) / (4 * z ^ 4)‖ ≤ (3 / 4) * ‖c‖ / ‖z‖ ^ 4 := by
  have hb : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have hz1 : (1:ℝ) ≤ ‖z‖ := by
    have : (1:ℝ) ≤ 1 + ‖c‖ := by linarith
    nlinarith
  have h1 : ‖c - (conj c) ^ 2‖ ≤ ‖c‖ + ‖c‖ ^ 2 := by
    calc ‖c - (conj c) ^ 2‖ ≤ ‖c‖ + ‖(conj c) ^ 2‖ := norm_sub_le _ _
      _ = ‖c‖ + ‖c‖ ^ 2 := by rw [norm_pow, Complex.norm_conj]
  have hD : ‖(4 * z ^ 4 : ℂ)‖ = 4 * ‖z‖ ^ 4 := by rw [norm_mul, norm_pow]; norm_num
  rw [norm_div, hD, div_le_div_iff₀ (by positivity) (by positivity)]
  have hmul : ‖c - (conj c) ^ 2‖ * ‖z‖ ^ 4 ≤ (‖c‖ + ‖c‖ ^ 2) * ‖z‖ ^ 4 :=
    mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ ‖z‖ ^ 4)
  have h3 : ‖c‖ + ‖c‖ ^ 2 ≤ 3 * ‖c‖ := by nlinarith [hc, hb, sq_nonneg ‖c‖]
  have hmul2 : (‖c‖ + ‖c‖ ^ 2) * ‖z‖ ^ 4 ≤ (3 * ‖c‖) * ‖z‖ ^ 4 :=
    mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ ‖z‖ ^ 4)
  linarith [hmul, hmul2]

private lemma head_z6_le (c z : ℂ) (hc : ‖c‖ ≤ 2) (hz : 3/2*(1+‖c‖) ≤ ‖z‖) :
    ‖conj c * ((conj c) ^ 2 + c) / (2 * z ^ 6)‖ ≤ (2 / 9) * ‖c‖ / ‖z‖ ^ 4 := by
  have hb : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have hzsq : (9/4)*(1+‖c‖)^2 ≤ ‖z‖^2 := by nlinarith
  have h1 : ‖conj c * ((conj c) ^ 2 + c)‖ ≤ ‖c‖ ^ 2 + ‖c‖ ^ 3 := by
    calc ‖conj c * ((conj c) ^ 2 + c)‖ = ‖c‖ * ‖(conj c) ^ 2 + c‖ := by
          rw [norm_mul, Complex.norm_conj]
      _ ≤ ‖c‖ * (‖c‖ ^ 2 + ‖c‖) := by
          gcongr
          calc ‖(conj c) ^ 2 + c‖ ≤ ‖(conj c) ^ 2‖ + ‖c‖ := norm_add_le _ _
            _ = ‖c‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]
      _ = ‖c‖ ^ 2 + ‖c‖ ^ 3 := by ring
  have hzp : (0:ℝ) < ‖z‖ := by linarith [norm_nonneg c]
  have hD : ‖(2 * z ^ 6 : ℂ)‖ = 2 * ‖z‖ ^ 6 := by rw [norm_mul, norm_pow]; norm_num
  rw [norm_div, hD, div_le_div_iff₀ (by positivity) (by positivity)]
  have hmul : ‖conj c * ((conj c) ^ 2 + c)‖ * ‖z‖ ^ 4
      ≤ (‖c‖ ^ 2 + ‖c‖ ^ 3) * ‖z‖ ^ 4 :=
    mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ ‖z‖ ^ 4)
  have hz4 : (9/4)*(1+‖c‖)^2 * ‖z‖^4 ≤ ‖z‖^2 * ‖z‖^4 :=
    mul_le_mul_of_nonneg_right hzsq (by positivity : (0:ℝ) ≤ ‖z‖^4)
  nlinarith [hmul, hz4, hb, hc, sq_nonneg ‖c‖, pow_nonneg (norm_nonneg z) 4,
    mul_nonneg hb (pow_nonneg (norm_nonneg z) 4)]

private lemma head_z8_le (c z : ℂ) (hc : ‖c‖ ≤ 2) (hz : 3/2*(1+‖c‖) ≤ ‖z‖) :
    ‖((conj c) ^ 2 + c) ^ 2 / (8 * z ^ 8)‖ ≤ (1 / 20) * ‖c‖ / ‖z‖ ^ 4 := by
  have hb : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have hzsq : (9/4)*(1+‖c‖)^2 ≤ ‖z‖^2 := by nlinarith
  have h1 : ‖((conj c) ^ 2 + c) ^ 2‖ ≤ (‖c‖ ^ 2 + ‖c‖) ^ 2 := by
    rw [norm_pow]
    have h2 : ‖(conj c) ^ 2 + c‖ ≤ ‖c‖ ^ 2 + ‖c‖ := by
      calc ‖(conj c) ^ 2 + c‖ ≤ ‖(conj c) ^ 2‖ + ‖c‖ := norm_add_le _ _
        _ = ‖c‖ ^ 2 + ‖c‖ := by rw [norm_pow, Complex.norm_conj]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hzp : (0:ℝ) < ‖z‖ := by linarith [norm_nonneg c]
  have hD : ‖(8 * z ^ 8 : ℂ)‖ = 8 * ‖z‖ ^ 8 := by rw [norm_mul, norm_pow]; norm_num
  rw [norm_div, hD, div_le_div_iff₀ (by positivity) (by positivity)]
  have hmul : ‖((conj c) ^ 2 + c) ^ 2‖ * ‖z‖ ^ 4 ≤ (‖c‖ ^ 2 + ‖c‖) ^ 2 * ‖z‖ ^ 4 :=
    mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ ‖z‖ ^ 4)
  have hz4 : ((9/4)*(1+‖c‖)^2)^2 * ‖z‖^4 ≤ (‖z‖^2)^2 * ‖z‖^4 :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hzsq 2)
      (by positivity : (0:ℝ) ≤ ‖z‖^4)
  nlinarith [hmul, hz4, hb, hc, sq_nonneg ‖c‖, pow_nonneg (norm_nonneg z) 4,
    mul_nonneg hb (pow_nonneg (norm_nonneg z) 4)]

private lemma tail_le (c z : ℂ) (hc : ‖c‖ ≤ 2) (hz : 3/2*(1+‖c‖) ≤ ‖z‖) :
    ‖∑' n : ℕ, Work.Bottcher.bottcherTerm c (n+1) z‖ ≤ (1/4)*‖c‖/‖z‖^4 := by
  have hb : (0:ℝ) ≤ ‖c‖ := norm_nonneg c
  have hzsq : (9/4)*(1+‖c‖)^2 ≤ ‖z‖^2 := by nlinarith
  have hzpos : (0:ℝ) < ‖z‖ := by
    have : (1:ℝ) ≤ 1+‖c‖ := by linarith
    nlinarith
  have hsum := summable_bottcherTerm_far c z hz
  have hsumshift : Summable (fun n : ℕ => Work.Bottcher.bottcherTerm c (n+1) z) :=
    (summable_nat_add_iff 1).mpr hsum
  have hterm_bound : ∀ n : ℕ, ‖Work.Bottcher.bottcherTerm c (n+1) z‖
      ≤ (1/4:ℝ)^(n+2) * ((3/2)*(8*‖c‖/‖z‖^8 + 16*(‖c‖^2+‖c‖)/‖z‖^16)) := by
    intro n
    have hvb := pow_four_div_two_le_norm_pMap_iterate c z hz (n+1) (by omega)
    have hvbpos : 0 < ‖(Work.Bottcher.pMap c)^[n+1] z‖ := by
      have : (0:ℝ) < ‖z‖^4/2 := by positivity
      linarith
    have hhalf := norm_nfG_le_half_of_far_iterate c z hz n
    have hnfv : Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n+1] z)
        = 1 + Work.Bottcher.Core.nfG c ((Work.Bottcher.pMap c)^[n+1] z) :=
      Work.Bottcher.Core.normFactor_eq_one_add_nfG c _ (norm_pos_iff.mp hvbpos)
    have hlog : ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n+1] z))‖
        ≤ (3/2) * ‖Work.Bottcher.Core.nfG c ((Work.Bottcher.pMap c)^[n+1] z)‖ := by
      rw [hnfv]; exact Complex.norm_log_one_add_half_le_self hhalf
    have hnf := norm_nfG_le_div c ((Work.Bottcher.pMap c)^[n+1] z)
    have hv2 : ‖z‖^8/4 ≤ ‖(Work.Bottcher.pMap c)^[n+1] z‖^2 := by
      have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ‖z‖^4/2) hvb 2
      have he : (‖z‖^4/2)^2 = ‖z‖^8/4 := by ring
      rwa [he] at h
    have hv4 : ‖z‖^16/16 ≤ ‖(Work.Bottcher.pMap c)^[n+1] z‖^4 := by
      have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ‖z‖^4/2) hvb 4
      have he : (‖z‖^4/2)^4 = ‖z‖^16/16 := by ring
      rwa [he] at h
    have hlead : ‖Work.Bottcher.Core.nfG c ((Work.Bottcher.pMap c)^[n+1] z)‖
        ≤ 8*‖c‖/‖z‖^8 + 16*(‖c‖^2+‖c‖)/‖z‖^16 := by
      refine hnf.trans ?_
      have hA : 2*‖c‖/‖(Work.Bottcher.pMap c)^[n+1] z‖^2 ≤ 8*‖c‖/‖z‖^8 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hv2, hb]
      have hBc : (‖c‖^2+‖c‖)/‖(Work.Bottcher.pMap c)^[n+1] z‖^4 ≤ 16*(‖c‖^2+‖c‖)/‖z‖^16 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hv4, hb]
      have hsplit : (2*‖c‖*‖(Work.Bottcher.pMap c)^[n+1] z‖^2 + ‖c‖^2+‖c‖)/‖(Work.Bottcher.pMap c)^[n+1] z‖^4
          = 2*‖c‖/‖(Work.Bottcher.pMap c)^[n+1] z‖^2 + (‖c‖^2+‖c‖)/‖(Work.Bottcher.pMap c)^[n+1] z‖^4 := by
        field_simp
        ring
      rw [hsplit]; linarith
    have hbt : ‖Work.Bottcher.bottcherTerm c (n+1) z‖
        = (1/4:ℝ)^(n+2) * ‖Complex.log (Work.Bottcher.normFactor c ((Work.Bottcher.pMap c)^[n+1] z))‖ := by
      rw [Work.Bottcher.bottcherTerm, norm_mul]
      congr 1
      have h2 : ‖(↑(1/4:ℝ) : ℂ)‖ = (1/4:ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs]; norm_num
      rw [norm_pow, h2]
    rw [hbt]
    refine mul_le_mul_of_nonneg_left (hlog.trans ?_) (by positivity : (0:ℝ) ≤ (1/4:ℝ)^(n+2))
    linarith [hlead]
  set K : ℝ := (3/2)*(8*‖c‖/‖z‖^8 + 16*(‖c‖^2+‖c‖)/‖z‖^16) with hK
  have hmaj : Summable (fun n : ℕ => (1/4:ℝ)^(n+2) * K) := by
    have h0 : Summable (fun n : ℕ => (1/4:ℝ)^(n+2)) := by
      have hgeo : Summable (fun n : ℕ => (1/4:ℝ)^n) :=
        summable_geometric_of_lt_one (by norm_num) (by norm_num)
      refine (hgeo.mul_right ((1/4:ℝ)^2)).congr (fun n => ?_)
      rw [pow_add]
    exact h0.mul_right K
  have hnormsum : Summable (fun n : ℕ => ‖Work.Bottcher.bottcherTerm c (n+1) z‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm_bound hmaj
  have h12 : (∑' n : ℕ, (1/4:ℝ)^(n+2)) = 1/12 := by
    have h1 : (∑' n : ℕ, (1/4:ℝ)^(n+1)) = 1/3 := by
      have h0 : HasSum (fun n : ℕ => (1/4:ℝ)^n) ((1:ℝ) - 1/4)⁻¹ :=
        hasSum_geometric_of_norm_lt_one (by norm_num)
      have h1' : HasSum (fun n : ℕ => (1/4:ℝ) * (1/4:ℝ)^n)
          ((1/4:ℝ) * ((1:ℝ) - 1/4)⁻¹) := h0.mul_left (1/4:ℝ)
      have h2' : (∑' n : ℕ, (1/4:ℝ)^(n+1)) = (1/4:ℝ) * ((1:ℝ) - 1/4)⁻¹ := by
        rw [← h1'.tsum_eq]
        exact tsum_congr (fun n => by rw [pow_succ'])
      rw [h2']; norm_num
    have h2 : (∑' n : ℕ, (1/4:ℝ)^(n+2)) = (1/4:ℝ) * (∑' n : ℕ, (1/4:ℝ)^(n+1)) := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun n => by rw [pow_succ, mul_comm])
    rw [h2, h1]; norm_num
  have hkey : 1/‖z‖^4 + 2*(1+‖c‖)/‖z‖^12 ≤ 1/4 := by
    have h1 : (81/16 : ℝ) ≤ ‖z‖^4 := by
      have h4 : ((9/4)*(1+‖c‖)^2)^2 ≤ (‖z‖^2)^2 := pow_le_pow_left₀ (by positivity) hzsq 2
      have h5 : ((9/4)*(1+‖c‖)^2)^2 = (81/16)*(1+‖c‖)^4 := by ring
      have hb1 : (1:ℝ) ≤ 1+‖c‖ := by linarith
      have h6 : (1:ℝ) ≤ (1+‖c‖)^4 := one_le_pow₀ hb1
      have h7 : (81/16 : ℝ) ≤ (81/16)*(1+‖c‖)^4 := by nlinarith
      rw [h5] at h4
      nlinarith [h4, h7]
    have h2 : 1/‖z‖^4 ≤ 16/81 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [h1]
    have h3 : 2*(1+‖c‖)/‖z‖^12 ≤ 8192/531441 := by
      have h4 : ((81/16 : ℝ))^3 * (1+‖c‖)^12 ≤ ‖z‖^12 := by
        have h5 : (((9/4)*(1+‖c‖)^2))^6 ≤ (‖z‖^2)^6 := pow_le_pow_left₀ (by positivity) hzsq 6
        have h6 : (((9/4)*(1+‖c‖)^2))^6 = ((81/16 : ℝ))^3 * (1+‖c‖)^12 := by ring_nf
        have h7 : (‖z‖^2)^6 = ‖z‖^12 := by ring
        rwa [h6, h7] at h5
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hb1 : (1:ℝ) ≤ 1+‖c‖ := by linarith
      have h9 : 2*(1+‖c‖)*531441 ≤ 8192*(((81/16:ℝ))^3*(1+‖c‖)^12) := by
        have h11 : (1+‖c‖) ≤ (1+‖c‖)^12 := by
          simpa using pow_le_pow_right₀ hb1 (by norm_num : (1:ℕ) ≤ 12)
        nlinarith [h11, hb1]
      nlinarith [h4, h9]
    have hnum : (16:ℝ)/81 + 8192/531441 ≤ 1/4 := by norm_num
    linarith [h2, h3, hnum]
  calc ‖∑' n : ℕ, Work.Bottcher.bottcherTerm c (n+1) z‖
      ≤ ∑' n : ℕ, ‖Work.Bottcher.bottcherTerm c (n+1) z‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, (1/4:ℝ)^(n+2) * K := hnormsum.tsum_le_tsum hterm_bound hmaj
    _ = K * (∑' n : ℕ, (1/4:ℝ)^(n+2)) := by rw [tsum_mul_right, mul_comm]
    _ = K * (1/12) := by rw [h12]
    _ ≤ (1/4)*‖c‖/‖z‖^4 := by
        rw [hK]
        rw [show (3/2)*(8*‖c‖/‖z‖^8 + 16*(‖c‖^2+‖c‖)/‖z‖^16) * (1/12)
              = ‖c‖/‖z‖^8 + 2*‖c‖*(1+‖c‖)/‖z‖^16 by ring]
        rw [le_div_iff₀ (by positivity : (0:ℝ) < ‖z‖^4)]
        have he : (‖c‖/‖z‖^8 + 2*‖c‖*(1+‖c‖)/‖z‖^16) * ‖z‖^4
            = ‖c‖ * (1/‖z‖^4 + 2*(1+‖c‖)/‖z‖^12) := by
          field_simp
        rw [he]
        have := mul_le_mul_of_nonneg_left hkey hb
        linarith [this]


/-- **Leading term of the Böttcher series.**  For `‖c‖ ≤ 2` and `‖z‖ ≥ (3/2)(1 + ‖c‖)`
the Böttcher series differs from its leading term `c̄/(2z²)` by at most
`2‖c‖/‖z‖⁴`. -/
theorem bottcherSeries_sub_leading_le (c z : ℂ) (hc : ‖c‖ ≤ 2)
    (hz : 3 / 2 * (1 + ‖c‖) ≤ ‖z‖) :
    ‖Work.Bottcher.bottcherSeries c z - conj c / (2 * z ^ 2)‖ ≤ 2 * ‖c‖ / ‖z‖ ^ 4 := by
  have hb : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hzpos : (0 : ℝ) < ‖z‖ := by
    have : (1 : ℝ) ≤ 1 + ‖c‖ := by linarith
    nlinarith
  have hzne : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hzpos; exact lt_irrefl 0 hzpos
  have hR4 : (0 : ℝ) < ‖z‖ ^ 4 := by positivity
  have hnf : Work.Bottcher.normFactor c z = 1 + Work.Bottcher.Core.nfG c z :=
    Work.Bottcher.Core.normFactor_eq_one_add_nfG c z hzne
  have hterm0 : Work.Bottcher.bottcherTerm c 0 z
      = (1 / 4 : ℂ) * Complex.log (Work.Bottcher.normFactor c z) := by
    simp [Work.Bottcher.bottcherTerm, Function.iterate_zero_apply]
  have hident : (1 / 4 : ℂ) * Complex.log (1 + Work.Bottcher.Core.nfG c z)
        - conj c / (2 * z ^ 2)
      = (1 / 4) * (Complex.log (1 + Work.Bottcher.Core.nfG c z)
          - Work.Bottcher.Core.nfG c z + (Work.Bottcher.Core.nfG c z) ^ 2 / 2)
        + ((c - (conj c) ^ 2) / (4 * z ^ 4)
            - conj c * ((conj c) ^ 2 + c) / (2 * z ^ 6)
            - ((conj c) ^ 2 + c) ^ 2 / (8 * z ^ 8)) := by
    rw [Work.Bottcher.Core.nfG]
    field_simp
    ring
  have hsum := summable_bottcherTerm_far c z hz
  have hsplit : Work.Bottcher.bottcherSeries c z
      = Work.Bottcher.bottcherTerm c 0 z
        + ∑' n : ℕ, Work.Bottcher.bottcherTerm c (n + 1) z :=
    hsum.tsum_eq_zero_add
  have hB : ‖(c - (conj c) ^ 2) / (4 * z ^ 4)
        - conj c * ((conj c) ^ 2 + c) / (2 * z ^ 6)
        - ((conj c) ^ 2 + c) ^ 2 / (8 * z ^ 8)‖
      ≤ (3 / 4) * ‖c‖ / ‖z‖ ^ 4 + (2 / 9) * ‖c‖ / ‖z‖ ^ 4 + (1 / 20) * ‖c‖ / ‖z‖ ^ 4 := by
    refine (norm_sub_le _ _).trans ?_
    have h3 := norm_sub_le ((c - (conj c) ^ 2) / (4 * z ^ 4))
      (conj c * ((conj c) ^ 2 + c) / (2 * z ^ 6))
    linarith [h3, head_z4_le c z hc hz, head_z6_le c z hc hz, head_z8_le c z hc hz]
  rw [hsplit, hterm0, hnf]
  rw [show (1 / 4 : ℂ) * Complex.log (1 + Work.Bottcher.Core.nfG c z)
        + (∑' n : ℕ, Work.Bottcher.bottcherTerm c (n + 1) z) - conj c / (2 * z ^ 2)
      = ((1 / 4) * (Complex.log (1 + Work.Bottcher.Core.nfG c z)
            - Work.Bottcher.Core.nfG c z + (Work.Bottcher.Core.nfG c z) ^ 2 / 2)
          + ((c - (conj c) ^ 2) / (4 * z ^ 4)
              - conj c * ((conj c) ^ 2 + c) / (2 * z ^ 6)
              - ((conj c) ^ 2 + c) ^ 2 / (8 * z ^ 8)))
        + ∑' n : ℕ, Work.Bottcher.bottcherTerm c (n + 1) z
      by rw [← hident]; ring]
  have htri : ‖(1 / 4 : ℂ) * (Complex.log (1 + Work.Bottcher.Core.nfG c z)
          - Work.Bottcher.Core.nfG c z + (Work.Bottcher.Core.nfG c z) ^ 2 / 2)
        + ((c - (conj c) ^ 2) / (4 * z ^ 4)
            - conj c * ((conj c) ^ 2 + c) / (2 * z ^ 6)
            - ((conj c) ^ 2 + c) ^ 2 / (8 * z ^ 8))
        + ∑' n : ℕ, Work.Bottcher.bottcherTerm c (n + 1) z‖
      ≤ ‖(1 / 4 : ℂ) * (Complex.log (1 + Work.Bottcher.Core.nfG c z)
          - Work.Bottcher.Core.nfG c z + (Work.Bottcher.Core.nfG c z) ^ 2 / 2)‖
        + ‖(c - (conj c) ^ 2) / (4 * z ^ 4)
            - conj c * ((conj c) ^ 2 + c) / (2 * z ^ 6)
            - ((conj c) ^ 2 + c) ^ 2 / (8 * z ^ 8)‖
        + ‖∑' n : ℕ, Work.Bottcher.bottcherTerm c (n + 1) z‖ := by
    have h1 := norm_add_le ((1 / 4 : ℂ) * (Complex.log (1 + Work.Bottcher.Core.nfG c z)
            - Work.Bottcher.Core.nfG c z + (Work.Bottcher.Core.nfG c z) ^ 2 / 2)
        + ((c - (conj c) ^ 2) / (4 * z ^ 4)
            - conj c * ((conj c) ^ 2 + c) / (2 * z ^ 6)
            - ((conj c) ^ 2 + c) ^ 2 / (8 * z ^ 8)))
      (∑' n : ℕ, Work.Bottcher.bottcherTerm c (n + 1) z)
    have h2 := norm_add_le ((1 / 4 : ℂ) * (Complex.log (1 + Work.Bottcher.Core.nfG c z)
            - Work.Bottcher.Core.nfG c z + (Work.Bottcher.Core.nfG c z) ^ 2 / 2))
      ((c - (conj c) ^ 2) / (4 * z ^ 4)
          - conj c * ((conj c) ^ 2 + c) / (2 * z ^ 6)
          - ((conj c) ^ 2 + c) ^ 2 / (8 * z ^ 8))
    linarith [h1, h2]
  refine htri.trans ?_
  have hsum2 : (3 / 5 : ℝ) * ‖c‖ / ‖z‖ ^ 4
        + ((3 / 4) * ‖c‖ / ‖z‖ ^ 4 + (2 / 9) * ‖c‖ / ‖z‖ ^ 4 + (1 / 20) * ‖c‖ / ‖z‖ ^ 4)
        + (1 / 4) * ‖c‖ / ‖z‖ ^ 4 ≤ 2 * ‖c‖ / ‖z‖ ^ 4 := by
    rw [show (3 / 5 : ℝ) * ‖c‖ / ‖z‖ ^ 4
          + ((3 / 4) * ‖c‖ / ‖z‖ ^ 4 + (2 / 9) * ‖c‖ / ‖z‖ ^ 4 + (1 / 20) * ‖c‖ / ‖z‖ ^ 4)
          + (1 / 4) * ‖c‖ / ‖z‖ ^ 4
        = ((3 / 5) + (3 / 4) + (2 / 9) + (1 / 20) + (1 / 4)) * ‖c‖ / ‖z‖ ^ 4 by ring]
    rw [div_le_div_iff₀ hR4 hR4]
    nlinarith [hb]
  linarith [head_log_le c z hc hz, hB, tail_le c z hc hz, hsum2]

end Work.Bottcher.Contraction
