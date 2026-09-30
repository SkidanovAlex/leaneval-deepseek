import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num19_half
import Submission.Work.BW.num_T
import Submission.Work.BW.num_blaschke_eta
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.num_xi
import Submission.Work.BW.halfJ_pos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.BW

/-! ## Local numeric helpers for the outer-circle (𝒥) half-integer step, level `J`

`ξ = pxi r = 1 - 0.536/r ∈ (0,1)`, and the two crude bounds on `log 7.2` used below. -/

/-- BW §19 outer-circle (𝒥) numerics, negative side: the `(2S'+1)`-type factor minus the
`log`/`3(T'+1)` losses exceeds `2^r S₀ D (12.43ξ^{r-1} − 0.105)`.  `X > 2^{r-1}Ξ^{-J}S₀ - 1` and
`T'+1 > (1−ξ)ξ^{r-1}Ξ^JT₀` (the floors), and the `J`-dependence cancels because
`Ξ^{-J}Ξ^{J} = 1`; then `(1−ξ)T₀ ≥ 6.297D` with `24.86 ≤ 2·6.297·log 7.2` (`num_blaschke_eta`)
gives the leading `12.43ξ^{r-1}`, while `T'_ideal ≤ 6.3D` and `D ≥ 1` absorb the corrections
(`log(7.2X/δ) ≤ log 2` by `δ ≥ 3.6X`). -/
private lemma hj_pxi_pos {r : ℕ} (hr : 2 ≤ r) : 0 < pxi r := by
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hlt : (0.536:ℝ)/(r:ℝ) < 1 := by rw [div_lt_one hr0]; linarith
  simp only [pxi]; linarith

private lemma hj_pxi_lt_one {r : ℕ} (hr : 2 ≤ r) : pxi r < 1 := by
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hlt : (0:ℝ) < 0.536/(r:ℝ) := div_pos (by norm_num) hr0
  simp only [pxi]; linarith

private lemma hj_pxi_le_one (r : ℕ) : pxi r ≤ 1 := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; norm_num [pxi]
  · have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast h
    have : (0:ℝ) < 0.536/(r:ℝ) := div_pos (by norm_num) hr0
    simp only [pxi]; linarith

private lemma hj_log72_le_three : Real.log 7.2 ≤ 3 := by
  have h1 : Real.log 7.2 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
  have h3 : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 2)]
    linarith [Real.exp_one_gt_two]
  linarith

private lemma hj_log2_le_one : Real.log 2 ≤ 1 := by
  rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 2)]
  linarith [Real.exp_one_gt_two]

private lemma hj_log4_ge_one : (1:ℝ) ≤ Real.log 4 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 4)]
  linarith [Real.exp_one_lt_three]

private theorem halfJ_neg_self {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (J : ℕ)
    {ξ Ξ S₀ Dm T₀ δ : ℝ} {X Tp : ℕ}
    (hξ : ξ = pxi r) (hΞ : Ξ = ξ ^ r)
    (hS608 : 608 ≤ S₀) (hDpos : 0 < Dm) (hT0nn : 0 ≤ T₀)
    (hDlow : 2 * (r:ℝ)^r * 32^(r+1) * (d:ℝ) * Real.log (2*(r:ℝ)*(d:ℝ)) ≤ Dm)
    (hT1 : 6.297 * Dm ≤ (1-ξ) * T₀) (hT2 : (1-ξ) * T₀ ≤ 6.3 * Dm)
    (hXle : (X:ℝ) ≤ 2^(r-1) * (Ξ⁻¹)^J * S₀)
    (hXlt : 2^(r-1) * (Ξ⁻¹)^J * S₀ < (X:ℝ) + 1)
    (hTple : (Tp:ℝ) ≤ (1-ξ) * ξ^(r-1) * (Ξ^J * T₀))
    (hTplt : (1-ξ) * ξ^(r-1) * (Ξ^J * T₀) < (Tp:ℝ) + 1)
    (hδgen : 3.6 * (X:ℝ) ≤ δ) (hδpos : 0 < δ) :
    2^r * S₀ * Dm * (12.43 * ξ^(r-1) - 0.105) <
      (2 * (X:ℝ) + 1) * ((Tp:ℝ) + 1) * Real.log 7.2 - 3 * ((Tp:ℝ) + 1)
        - Real.log (7.2 * (X:ℝ) / δ) - Real.log 2 := by
  have hr1 : 1 ≤ r := by omega
  have hξpos : 0 < ξ := by rw [hξ]; exact hj_pxi_pos hr
  have hξnonneg : 0 ≤ ξ := le_of_lt hξpos
  have hξle1 : ξ ≤ 1 := by rw [hξ]; exact hj_pxi_le_one r
  have hξlt1 : ξ < 1 := by rw [hξ]; exact hj_pxi_lt_one hr
  have h1mξ : 0 < 1 - ξ := by linarith
  have hΞpos : 0 < Ξ := by rw [hΞ]; exact pow_pos hξpos r
  have hΞnonneg : 0 ≤ Ξ := le_of_lt hΞpos
  have hΞle1 : Ξ ≤ 1 := by rw [hΞ]; exact pow_le_one₀ hξnonneg hξle1
  have hSpos : 0 < S₀ := by linarith
  have hSnonneg : 0 ≤ S₀ := le_of_lt hSpos
  have hlog72pos : 0 < Real.log 7.2 := Real.log_pos (by norm_num)
  have hlog72le3 : Real.log 7.2 ≤ 3 := hj_log72_le_three
  -- Tid bookkeeping
  have hTid_nn : 0 ≤ (1-ξ) * ξ^(r-1) * (Ξ^J * T₀) :=
    mul_nonneg (mul_nonneg (le_of_lt h1mξ) (pow_nonneg hξnonneg _))
      (mul_nonneg (pow_nonneg hΞnonneg _) hT0nn)
  have hTid_le : (1-ξ) * ξ^(r-1) * (Ξ^J * T₀) ≤ 6.3 * Dm := by
    have hξpow : ξ^(r-1) ≤ 1 := pow_le_one₀ hξnonneg hξle1
    have hΞpow : Ξ^J ≤ 1 := pow_le_one₀ hΞnonneg hΞle1
    have hstep : ξ^(r-1) * (Ξ^J * T₀) ≤ T₀ := by
      have h1 := mul_le_mul_of_nonneg_right hΞpow hT0nn
      have h2 := mul_le_mul_of_nonneg_right hξpow (mul_nonneg (pow_nonneg hΞnonneg J) hT0nn)
      linarith [h1, h2]
    have h2 : (1-ξ) * (ξ^(r-1) * (Ξ^J * T₀)) ≤ (1-ξ) * T₀ :=
      mul_le_mul_of_nonneg_left hstep (le_of_lt h1mξ)
    calc (1-ξ) * ξ^(r-1) * (Ξ^J * T₀) = (1-ξ) * (ξ^(r-1) * (Ξ^J * T₀)) := by ring
      _ ≤ (1-ξ) * T₀ := h2
      _ ≤ 6.3 * Dm := hT2
  have hTr1_gt : (1-ξ) * ξ^(r-1) * (Ξ^J * T₀) < (Tp:ℝ) + 1 := hTplt
  have hTr1_le : (Tp:ℝ) + 1 ≤ (1-ξ) * ξ^(r-1) * (Ξ^J * T₀) + 1 := by linarith [hTple]
  have hTr1_nn : 0 ≤ (Tp:ℝ) + 1 := by positivity
  -- positivity of X
  have hΞinv1 : 1 ≤ Ξ⁻¹ := (one_le_inv₀ hΞpos).mpr hΞle1
  have hΞinvJ : 1 ≤ (Ξ⁻¹)^J := one_le_pow₀ hΞinv1
  have h2r1 : (1:ℝ) ≤ 2^(r-1) := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
  have hXid : 608 ≤ 2^(r-1) * (Ξ⁻¹)^J * S₀ := by
    have h1 : (1:ℝ) ≤ 2^(r-1) * (Ξ⁻¹)^J := by
      have h := mul_le_mul h2r1 hΞinvJ (by norm_num) (by positivity)
      simpa using h
    have h2 : (1:ℝ) * 608 ≤ (2^(r-1) * (Ξ⁻¹)^J) * S₀ :=
      mul_le_mul h1 hS608 (by norm_num) (by positivity)
    linarith [h2]
  have hXpos : 0 < (X:ℝ) := by linarith [hXlt, hXid]
  have hXnonneg : 0 ≤ (X:ℝ) := le_of_lt hXpos
  have hXr_ge : 2^(r-1) * (Ξ⁻¹)^J * S₀ - 1 ≤ (X:ℝ) := by linarith [hXlt]
  -- floor step: 2 log 7.2 ((X_ideal - 1) T'_ideal) <= 2 X (Tp+1) log 7.2
  have hA : 2 * Real.log 7.2 * ((2^(r-1) * (Ξ⁻¹)^J * S₀ - 1) * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀)))
      ≤ 2 * (X:ℝ) * ((Tp:ℝ) + 1) * Real.log 7.2 := by
    have h1 : (2^(r-1) * (Ξ⁻¹)^J * S₀ - 1) * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀))
        ≤ (X:ℝ) * ((Tp:ℝ) + 1) :=
      mul_le_mul hXr_ge (le_of_lt hTplt) hTid_nn hXnonneg
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 2 * Real.log 7.2)
    linarith [h2]
  -- the ideal product identity
  have hcan : (Ξ⁻¹)^J * Ξ^J = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hΞpos), one_pow]
  have hXidTid : (2^(r-1) * (Ξ⁻¹)^J * S₀) * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀))
      = 2^(r-1) * S₀ * ((1-ξ) * (ξ^(r-1) * T₀)) := by
    rw [show (2^(r-1) * (Ξ⁻¹)^J * S₀) * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀))
        = (2^(r-1) * S₀ * ((1-ξ) * (ξ^(r-1) * T₀))) * ((Ξ⁻¹)^J * Ξ^J) by ring, hcan, mul_one]
  have hpow2 : (2:ℝ) * 2^(r-1) = 2^r := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel hr1]
  -- the main lower bound
  have hlogge : 12.43 ≤ 6.297 * Real.log 7.2 := by
    have h := (num_blaschke_eta 608 (le_refl 608) 0).2.2.2.2
    linarith
  have hB : 2^r * S₀ * Dm * (12.43 * ξ^(r-1))
      ≤ 2 * Real.log 7.2 * ((2^(r-1) * (Ξ⁻¹)^J * S₀) * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀))) := by
    have hfac : (0:ℝ) ≤ 2 * Real.log 7.2 * 2^(r-1) * S₀ * ξ^(r-1) := by positivity
    have hstep : 2 * Real.log 7.2 * 2^(r-1) * S₀ * ξ^(r-1) * (6.297 * Dm)
        ≤ 2 * Real.log 7.2 * 2^(r-1) * S₀ * ξ^(r-1) * ((1-ξ) * T₀) :=
      mul_le_mul_of_nonneg_left hT1 hfac
    have hval : 2 * Real.log 7.2 * 2^(r-1) * S₀ * ξ^(r-1) * (6.297 * Dm)
        = 2^r * S₀ * Dm * ξ^(r-1) * (6.297 * Real.log 7.2) := by
      rw [← hpow2]; ring
    calc 2^r * S₀ * Dm * (12.43 * ξ^(r-1))
        ≤ 2^r * S₀ * Dm * ξ^(r-1) * (6.297 * Real.log 7.2) := by
          have h := mul_le_mul_of_nonneg_left hlogge (by positivity : (0:ℝ) ≤ 2^r * S₀ * Dm * ξ^(r-1))
          linarith [h]
      _ = 2 * Real.log 7.2 * 2^(r-1) * S₀ * ξ^(r-1) * (6.297 * Dm) := hval.symm
      _ ≤ 2 * Real.log 7.2 * 2^(r-1) * S₀ * ξ^(r-1) * ((1-ξ) * T₀) := hstep
      _ = 2 * Real.log 7.2 * ((2^(r-1) * (Ξ⁻¹)^J * S₀) * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀))) := by
          rw [hXidTid]; ring
  have hid : 2 * Real.log 7.2 * ((2^(r-1) * (Ξ⁻¹)^J * S₀ - 1) * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀)))
      = 2 * Real.log 7.2 * ((2^(r-1) * (Ξ⁻¹)^J * S₀) * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀)))
        - 2 * Real.log 7.2 * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀)) := by ring
  have hmid : 2 * Real.log 7.2 * ((2^(r-1) * (Ξ⁻¹)^J * S₀ - 1) * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀)))
      ≥ 2^r * S₀ * Dm * (12.43 * ξ^(r-1)) - 2 * Real.log 7.2 * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀)) := by
    linarith [hid, hB]
  have s2 : 2 * Real.log 7.2 * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀)) ≤ 6 * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀)) := by
    have h := mul_le_mul_of_nonneg_right hlog72le3 hTid_nn
    linarith [h]
  have s3 : 6 * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀)) ≤ 6 * (6.3 * Dm) := by linarith [hTid_le]
  have s4 : ((Tp:ℝ) + 1) * (Real.log 7.2 - 3) ≥ -3 * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀) + 1) := by
    have h1 : ((Tp:ℝ) + 1) * (Real.log 7.2 - 3)
        = ((Tp:ℝ) + 1) * Real.log 7.2 - 3 * ((Tp:ℝ) + 1) := by ring
    have h2 : 0 ≤ ((Tp:ℝ) + 1) * Real.log 7.2 := mul_nonneg hTr1_nn (le_of_lt hlog72pos)
    linarith [h1, h2, hTr1_le]
  have hF : Real.log (7.2 * (X:ℝ) / δ) ≤ Real.log 2 := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hδpos]
    linarith [hδgen]
  -- the Kummer-free conclusion
  have hkey : 2^r * S₀ * Dm * (12.43 * ξ^(r-1) - 0.105) <
      2 * (X:ℝ) * ((Tp:ℝ) + 1) * Real.log 7.2 + ((Tp:ℝ) + 1) * (Real.log 7.2 - 3)
        - Real.log (7.2 * (X:ℝ) / δ) - Real.log 2 := by
    have hQ : 2^r * S₀ * Dm * (12.43 * ξ^(r-1) - 0.105)
        = 2^r * S₀ * Dm * (12.43 * ξ^(r-1)) - 0.105 * (2^r * S₀ * Dm) := by ring
    have hDm1 : 1 ≤ Dm := by
      have hr4 : (4:ℝ) ≤ (r:ℝ)^r := by
        have h1 : (2:ℝ)^2 ≤ (r:ℝ)^2 := pow_le_pow_left₀ (by norm_num) (by exact_mod_cast hr) 2
        have h2 : (r:ℝ)^2 ≤ (r:ℝ)^r := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ r)) hr
        norm_num at h1
        linarith
      have h32 : (32768:ℝ) ≤ (32:ℝ)^(r+1) := by
        have h1 : (32:ℝ)^3 ≤ (32:ℝ)^(r+1) := pow_le_pow_right₀ (by norm_num) (by omega)
        norm_num at h1
        linarith
      have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hlog4 : (1:ℝ) ≤ Real.log (2*(r:ℝ)*(d:ℝ)) := by
        have h4 : (4:ℝ) ≤ 2*(r:ℝ)*(d:ℝ) := by
          have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
          nlinarith
        exact le_trans hj_log4_ge_one (Real.log_le_log (by norm_num) h4)
      have hone : (1:ℝ) ≤ 2 * (r:ℝ)^r * 32^(r+1) * (d:ℝ) * Real.log (2*(r:ℝ)*(d:ℝ)) := by
        have hA : (1:ℝ) ≤ 2 * (r:ℝ)^r := by linarith
        have hB : (1:ℝ) ≤ (32:ℝ)^(r+1) := by linarith
        have hC : (1:ℝ) ≤ (d:ℝ) := hd1
        have hD : (1:ℝ) ≤ Real.log (2*(r:ℝ)*(d:ℝ)) := hlog4
        have hAB : (1:ℝ) ≤ 2 * (r:ℝ)^r * 32^(r+1) := by
          have h := mul_le_mul hA hB (by norm_num) (by positivity)
          linarith [h]
        have hABC : (1:ℝ) ≤ 2 * (r:ℝ)^r * 32^(r+1) * (d:ℝ) := by
          have h := mul_le_mul hAB hC (by norm_num) (by positivity)
          linarith [h]
        have h := mul_le_mul hABC hD (by norm_num) (by positivity)
        linarith [h]
      linarith [hDlow, hone]
    have hG : 56.7 * Dm + 3 + 2 * Real.log 2 < 0.105 * 2^r * S₀ * Dm := by
      have h2r : (4:ℝ) ≤ 2^r := by
        have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hr
        norm_num at h
        exact h
      have h255 : (255.36:ℝ) * Dm ≤ 0.105 * 2^r * S₀ * Dm := by
        have hprod : (2432:ℝ) ≤ 2^r * S₀ := by
          have h := mul_le_mul h2r hS608 (by norm_num) (by positivity)
          norm_num at h
          linarith [h]
        have h := mul_le_mul_of_nonneg_right hprod (le_of_lt hDpos)
        nlinarith [h]
      have h2log2 : 2 * Real.log 2 ≤ 2 := by linarith [hj_log2_le_one]
      nlinarith [h255, hDm1, h2log2]
    have s5 : -3 * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀) + 1) ≥ -(18.9 * Dm + 3) := by
      linarith [hTid_le]
    have hstepA : 2^r * S₀ * Dm * (12.43 * ξ^(r-1))
          - 2 * Real.log 7.2 * ((1-ξ) * ξ^(r-1) * (Ξ^J * T₀))
        ≤ 2 * (X:ℝ) * ((Tp:ℝ) + 1) * Real.log 7.2 := by
      linarith [hA, hmid]
    have hstepB : 2^r * S₀ * Dm * (12.43 * ξ^(r-1)) - (56.7 * Dm + 3 + 2 * Real.log 2)
        ≤ 2 * (X:ℝ) * ((Tp:ℝ) + 1) * Real.log 7.2 + ((Tp:ℝ) + 1) * (Real.log 7.2 - 3)
          - Real.log (7.2 * (X:ℝ) / δ) - Real.log 2 := by
      linarith [hstepA, s2, s3, s4, s5, hF]
    linarith [hstepB, hQ, hG]
  have hsub : (2 * (X:ℝ) + 1) * ((Tp:ℝ) + 1) * Real.log 7.2 - 3 * ((Tp:ℝ) + 1)
      = 2 * (X:ℝ) * ((Tp:ℝ) + 1) * Real.log 7.2 + ((Tp:ℝ) + 1) * (Real.log 7.2 - 3) := by ring
  linarith [hkey, hsub]
/-- BW §19, outer-circle (𝒥) numerics for the half-integer step: with `S' ≥ 2^{r-1}ξ^{-rJ}S₀-1`, `T' = [(1−ξ)ξ^{r-1}ξ^{rJ}T₀]`, `R = 7.2S'`, `δ ≥ R/2`, `D ≥ 2r^r32^{r+1}d log(2rd)` and `J ≤ 50 log(2rd)`, the numerics of p. 53–56 give the 𝒥-contradiction. Uses `num19_half`. -/
theorem half_num_J {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (J : ℕ)
    (hJ : (J:ℝ) ≤ 50 * Real.log (2*(r:ℝ)*(d:ℝ)))
    {ξ Ξ S₀ Dm T₀ hh δ : ℝ} {X Tp : ℕ}
    (hξ : ξ = pxi r) (hΞ : Ξ = ξ ^ r)
    (hS608 : 608 ≤ S₀) (hDpos : 0 < Dm) (hT0nn : 0 ≤ T₀) (hh19 : 19 ≤ hh)
    (hDlow : 2 * (r:ℝ)^r * 32^(r+1) * (d:ℝ) * Real.log (2*(r:ℝ)*(d:ℝ)) ≤ Dm)
    (hT1 : 6.297 * Dm ≤ (1-ξ) * T₀) (hT2 : (1-ξ) * T₀ ≤ 6.3 * Dm)
    (hT3 : (d:ℝ) * hh * T₀ ≤ 0.735 * S₀ * Dm)
    (hξS : (1-ξ) * S₀ = 8.576 * (d:ℝ) * hh)
    (hXle : (X:ℝ) ≤ 2^(r-1) * (Ξ⁻¹)^J * S₀)
    (hXlt : 2^(r-1) * (Ξ⁻¹)^J * S₀ < (X:ℝ) + 1)
    (hTple : (Tp:ℝ) ≤ (1-ξ) * ξ^(r-1) * (Ξ^J * T₀))
    (hTplt : (1-ξ) * ξ^(r-1) * (Ξ^J * T₀) < (Tp:ℝ) + 1)
    (hδgen : 3.6 * (X:ℝ) ≤ δ) (hδpos : 0 < δ) :
    Real.log (7.2 * (X:ℝ) / δ) + 2^r * ((d:ℝ) * hh * (Ξ^(J+1) * T₀) + 1.087 * S₀ * Dm +
        1.008 * ((7.2 * (X:ℝ) / 2^r + 2 * (Ξ⁻¹)^J * S₀) / 2^J) * Dm +
        0.044 * J / Real.log (2*(r:ℝ)*(d:ℝ)) * S₀ * Dm)
      - ((2 * (X:ℝ) + 1) * ((Tp:ℝ) + 1) * Real.log 7.2 - 3 * ((Tp:ℝ) + 1))
      < -Real.log 2 := by
  -- positive bracket ≤ `2^r S₀ D (12.43ξ^{r-1} − 0.105)` (this is `num19_half`, term by term)
  have hpos := halfJ_pos hr hd J hJ hξ hΞ hS608 hDpos hT0nn hh19 hDlow hT3 hXle
  -- the (floored) negative term beats the same quantity
  have hneg := halfJ_neg_self (d := d) hr hd J hξ hΞ hS608 hDpos hT0nn hDlow hT1 hT2 hXle hXlt
    hTple hTplt hδgen hδpos
  linarith [hpos, hneg]

end Work.BW
