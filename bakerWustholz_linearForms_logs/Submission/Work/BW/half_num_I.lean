import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.num19_half
import Submission.Work.BW.num_T
import Submission.Work.BW.num_blaschke_eta
import Submission.Work.BW.num_D_lower
import Submission.Work.BW.num_xi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 4000000

namespace Work.BW

/-! ### Elementary numeric helpers -/

private lemma exp_neg_536_ge_I : (0.5847 : ℝ) ≤ Real.exp (-0.536) := by
  have h := Real.exp_bound (x := (-0.536:ℝ)) (by norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

private lemma log608_le_I : Real.log 608 ≤ 6.5 := by
  have h1 : Real.log 608 = 9 * Real.log 2 + Real.log (19/16) := by
    have h512 : (608:ℝ) = 512*(19/16) := by norm_num
    rw [h512, Real.log_mul (by norm_num) (by norm_num),
      show (512:ℝ) = 2^9 by norm_num, Real.log_pow]
    norm_num
  have h2 : Real.log (19/16) ≤ 19/16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  linarith [Real.log_two_lt_d9, h1, h2]

private lemma log_le_lin_I (x : ℝ) (hx : 608 ≤ x) : Real.log x ≤ 5.5 + x/608 := by
  have hx0 : 0 < x / 608 := by positivity
  have hprod : x = 608 * (x / 608) := by field_simp
  rw [hprod, Real.log_mul (by norm_num) (ne_of_gt hx0)]
  have hdiv : Real.log (x / 608) ≤ x / 608 - 1 := Real.log_le_sub_one_of_pos hx0
  have h608 := log608_le_I
  linarith

private lemma log_two_le_I : Real.log 2 ≤ 0.6932 := by linarith [Real.log_two_lt_d9]

private lemma log_eight_le_I : Real.log 8 ≤ 2.0795 := by
  have h : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_lt_d9, h]

private lemma c0_eq_I : (2*Real.pi*(1/3:ℝ))⁻¹ * (1-1/3)⁻¹^2 = 27/(8*Real.pi) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

private lemma c0_nonneg_I : (0:ℝ) ≤ Real.log ((2*Real.pi*(1/3:ℝ))⁻¹ * (1-1/3)⁻¹^2) := by
  apply Real.log_nonneg
  rw [c0_eq_I, le_div_iff₀ (by positivity)]
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  nlinarith

private lemma c0_le_I : Real.log ((2*Real.pi*(1/3:ℝ))⁻¹ * (1-1/3)⁻¹^2) ≤ 0.1 := by
  rw [c0_eq_I]
  have h1 : Real.log (27/(8*Real.pi)) ≤ 27/(8*Real.pi) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have hpi : (3.14:ℝ) < Real.pi := Real.pi_gt_d2
  have h2 : 27/(8*Real.pi) ≤ 1.075 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  linarith

private lemma pxi_pos_I {r : ℕ} (hr : 2 ≤ r) : 0 < pxi r := by
  have h1 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have h3 : (0:ℝ) < (r:ℝ) := by linarith
  simp only [pxi]
  rw [sub_pos, div_lt_one h3]; linarith

private lemma pxi_le_one_I (r : ℕ) : pxi r ≤ 1 := by
  have : (0:ℝ) ≤ 0.536 / (r:ℝ) := by positivity
  simp only [pxi]; linarith

private lemma r_le_two_pow (n : ℕ) : (n:ℝ) ≤ (2:ℝ)^n := by
  have h : n ≤ 2^n := le_of_lt (Nat.lt_two_pow_self (n := n))
  calc (n:ℝ) ≤ ((2^n : ℕ) : ℝ) := by exact_mod_cast h
    _ = (2:ℝ)^n := by push_cast; ring

/-- BW §19, inner-circle (ℐ) numerics for the half-integer step: same setup as `half_num_J`, plus the non-degeneracy term `q = ξ^{-rJ}/D` with `q ≤ (2ξ^r)^{-J}/r` and `q ≤ ξ^{-rJ}/(2r^r32^{r+1}d log(2rd))`, the Taylor-sum inequality of p. 55–56. Uses `num19_half`. -/
theorem half_num_I {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (J : ℕ)
    (hJ : (J:ℝ) ≤ 50 * Real.log (2*(r:ℝ)*(d:ℝ)))
    {ξ Ξ S₀ Dm T₀ hh q : ℝ} {X Tp : ℕ}
    (hξ : ξ = pxi r) (hΞ : Ξ = ξ ^ r)
    (hS608 : 608 ≤ S₀) (hDpos : 0 < Dm) (hT0nn : 0 ≤ T₀) (hh19 : 19 ≤ hh)
    (hDlow : 2 * (r:ℝ)^r * 32^(r+1) * (d:ℝ) * Real.log (2*(r:ℝ)*(d:ℝ)) ≤ Dm)
    (hT1 : 6.297 * Dm ≤ (1-ξ) * T₀) (hT2 : (1-ξ) * T₀ ≤ 6.3 * Dm)
    (hT3 : (d:ℝ) * hh * T₀ ≤ 0.735 * S₀ * Dm)
    (hq : q = (Ξ⁻¹)^J / Dm) (hq0 : 0 ≤ q)
    (hq1 : q ≤ (2*Ξ)⁻¹^J / (r:ℝ))
    (hq2 : q ≤ (Ξ⁻¹)^J / (2 * (r:ℝ)^r * 32^(r+1) * (d:ℝ) * Real.log (2*(r:ℝ)*(d:ℝ))))
    (hXle : (X:ℝ) ≤ 2^(r-1) * (Ξ⁻¹)^J * S₀)
    (hXlt : 2^(r-1) * (Ξ⁻¹)^J * S₀ < (X:ℝ) + 1)
    (hTple : (Tp:ℝ) ≤ (1-ξ) * ξ^(r-1) * (Ξ^J * T₀))
    (hTplt : (1-ξ) * ξ^(r-1) * (Ξ^J * T₀) < (Tp:ℝ) + 1) :
    Real.log ((2*(X:ℝ)+1) * ((Tp:ℝ) + 1)) + Real.log 2 +
      2^r * ((d:ℝ) * hh * (ξ^(r-1) * (Ξ^J * T₀)) - 7.893 * S₀ * Dm +
        1.01 * (2.5 * (Ξ⁻¹)^J * S₀ / 2^J) * Dm +
        0.044 * J / Real.log (2*(r:ℝ)*(d:ℝ)) * S₀ * Dm)
      + ((Tp:ℝ) + 1) * (2 * (2^(r-1) * (Ξ⁻¹)^J * S₀) + 2 * Real.log (2^(r-1) * (Ξ⁻¹)^J * S₀)
          + Real.log ((2*Real.pi*(1/3:ℝ))⁻¹ * (1-1/3)⁻¹^2) + 3)
      < -Real.log 2 := by
  subst hξ
  subst hΞ
  set ξ : ℝ := pxi r with hξdef
  set Ξ : ℝ := ξ ^ r with hΞdef
  set L : ℝ := Real.log (2*(r:ℝ)*(d:ℝ)) with hLdef
  set k : ℝ := (Ξ⁻¹) ^ J with hkdef
  set A : ℝ := 2^(r-1) * k * S₀ with hAdef
  set x : ℝ := ξ ^ (r-1) with hxdef
  set R1 : ℝ := ((r-1:ℕ):ℝ) with hR1def
  set c₀ : ℝ := Real.log ((2*Real.pi*(1/3:ℝ))⁻¹ * (1-1/3)⁻¹^2) with hc0def
  set C : ℝ := 2*A + 2*Real.log A + c₀ + 3 with hCdef
  set β : ℝ := 6.3*Dm*(x*Ξ^J) with hβdef
  set Z : ℝ := 2^r*S₀*Dm with hZdef
  set Zx : ℝ := 2^r*S₀*Dm*x with hZxdef
  have hrR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hr1 : 1 ≤ r := by omega
  have hZnn : 0 ≤ Z := by rw [hZdef]; positivity
  have hξpos : 0 < ξ := by rw [hξdef]; exact pxi_pos_I hr
  have hξle1 : ξ ≤ 1 := by rw [hξdef]; exact pxi_le_one_I r
  have hξnn : 0 ≤ ξ := le_of_lt hξpos
  have hΞpos : 0 < Ξ := by rw [hΞdef]; positivity
  have hΞle1 : Ξ ≤ 1 := by rw [hΞdef]; exact pow_le_one₀ (le_of_lt hξpos) hξle1
  have hΞnn : 0 ≤ Ξ := le_of_lt hΞpos
  have hxlo : 0.5847 ≤ x := by
    rw [hxdef, hξdef]
    exact le_trans exp_neg_536_ge_I ((num_xi hr).2.2.2.1 (r-1) le_rfl)
  have hxhi : x ≤ 0.732 := by rw [hxdef, hξdef]; exact (num_xi hr).2.2.1
  have hxnn : 0 ≤ x := by linarith only [hxlo]
  have hxle1 : x ≤ 1 := by linarith only [hxhi]
  have hΞge : 0.535 ≤ Ξ := by rw [hΞdef, hξdef]; exact (num_xi hr).2.1
  have hΞJle1 : Ξ^J ≤ 1 := pow_le_one₀ hΞnn hΞle1
  have hΞJnn : 0 ≤ Ξ^J := by positivity
  have hΞinv1 : 1 ≤ Ξ⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hΞpos]; linarith only [hΞle1]
  have hΞinv_le : Ξ⁻¹ ≤ 1.87 := by
    rw [inv_eq_one_div]
    calc (1:ℝ)/Ξ ≤ 1/0.535 := one_div_le_one_div_of_le (by norm_num) hΞge
      _ ≤ 1.87 := by norm_num
  have hk1 : 1 ≤ k := by rw [hkdef]; exact one_le_pow₀ hΞinv1
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk1
  have hknn : 0 ≤ k := le_of_lt hkpos
  have hk_le : k ≤ 1.87^J := by
    rw [hkdef]; exact pow_le_pow_left₀ (by positivity) hΞinv_le J
  have hΞk : Ξ^J * k = 1 := by
    rw [hkdef, ← mul_pow, mul_inv_cancel₀ (ne_of_gt hΞpos), one_pow]
  have hΞJinv : Ξ^J = k⁻¹ := eq_inv_of_mul_eq_one_left hΞk
  have h2r4 : (4:ℝ) ≤ 2^r := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hr
    norm_num at h; exact h
  have h2rpos : (0:ℝ) < 2^r := by positivity
  have h2r : (2:ℝ)^r = 2^(r-1)*2 := by
    rw [← pow_succ, Nat.sub_add_cancel hr1]
  have hR1nn : 0 ≤ R1 := by rw [hR1def]; positivity
  -- L facts
  have hLpos : 0 < L := by
    rw [hLdef]; apply Real.log_pos; nlinarith only [hrR, hdR]
  have hL1386 : (1.386:ℝ) ≤ L := by
    rw [hLdef]
    have h4le : (4:ℝ) ≤ 2*(r:ℝ)*(d:ℝ) := by nlinarith only [hrR, hdR]
    have hlog4 : Real.log 4 = 2*Real.log 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 4) h4le
    linarith only [h, Real.log_two_gt_d9, hlog4]
  have hDlowL : 2*(r:ℝ)^r*32^(r+1)*(d:ℝ)*L ≤ Dm := hDlow
  -- Dm lower bound
  have hrr : (4:ℝ) ≤ (r:ℝ)^r := by
    have h1 : (2:ℝ)^2 ≤ (r:ℝ)^2 := pow_le_pow_left₀ (by norm_num) hrR 2
    have h2 : (r:ℝ)^2 ≤ (r:ℝ)^r := pow_le_pow_right₀ (by linarith only [hrR]) hr
    linarith only [h1, h2]
  have h32 : (32768:ℝ) ≤ 32^(r+1) := by
    have h1 : (32:ℝ)^3 ≤ 32^(r+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith only [h1]
  have hP1 : (262144:ℝ) ≤ 2*(r:ℝ)^r*32^(r+1) := by
    have hA : (8:ℝ) ≤ 2*(r:ℝ)^r := by linarith only [hrr]
    have h := mul_le_mul hA h32 (by norm_num) (by positivity)
    linarith only [h]
  have hP2 : (262144:ℝ) ≤ 2*(r:ℝ)^r*32^(r+1)*(d:ℝ) := by
    have h := mul_le_mul hP1 hdR (by norm_num) (by positivity)
    linarith only [h]
  have hP3 : (363000:ℝ) ≤ 2*(r:ℝ)^r*32^(r+1)*(d:ℝ)*L := by
    have h := mul_le_mul hP2 hL1386 (by norm_num) (by positivity)
    norm_num at h ⊢
    linarith only [h]
  have hDm608 : (608:ℝ) ≤ Dm := by linarith only [hP3, hDlow]
  have hDm1 : (1:ℝ) ≤ Dm := by linarith only [hDm608]
  have hDm363 : (363000:ℝ) ≤ Dm := by linarith only [hP3, hDlow]
  have hKL : 262144*L ≤ Dm := by
    calc 262144*L ≤ (2*(r:ℝ)^r*32^(r+1)*(d:ℝ))*L := mul_le_mul_of_nonneg_right hP2 hLpos.le
      _ ≤ Dm := hDlowL
  have hSDnn : 0 ≤ S₀*Dm := by positivity
  -- log k bound
  have hlogk : Real.log k ≤ 43.5*L := by
    have h187 : Real.log 1.87 ≤ 0.87 := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1.87 by norm_num)
      linarith only [h]
    have h1 : Real.log k ≤ (J:ℝ)*Real.log 1.87 := by
      calc Real.log k ≤ Real.log ((1.87:ℝ)^J) := Real.log_le_log hkpos hk_le
        _ = (J:ℝ)*Real.log 1.87 := Real.log_pow (1.87:ℝ) J
    have hJ' : (J:ℝ) ≤ 50*L := by rw [hLdef]; exact hJ
    have h2 : (J:ℝ)*Real.log 1.87 ≤ (J:ℝ)*0.87 := mul_le_mul_of_nonneg_left h187 (by positivity)
    have h3 : (J:ℝ)*0.87 ≤ (50*L)*0.87 := mul_le_mul_of_nonneg_right hJ' (by norm_num)
    linarith only [h1, h2, h3]
  have hlogS : Real.log S₀ ≤ 5.5 + S₀/608 := log_le_lin_I S₀ hS608
  have hlogSnn : 0 ≤ Real.log S₀ := Real.log_nonneg (by linarith only [hS608])
  -- num19_half
  have hq1' : q ≤ (2 * pxi r ^ r)⁻¹ ^ J / (r:ℝ) := by
    rw [← hξdef, ← hΞdef]; exact hq1
  have hq2' : q ≤ (pxi r ^ r)⁻¹ ^ J /
      (2 * (r:ℝ)^r * 32^(r+1) * (d:ℝ) * Real.log (2*(r:ℝ)*(d:ℝ))) := by
    rw [← hξdef, ← hΞdef, ← hkdef, ← hLdef]; exact hq2
  have hJnum : (J:ℝ) ≤ 50 * Real.log (2*(r:ℝ)*(d:ℝ)) := hJ
  have hnum := (num19_half hr hd J hJnum q hq0 hq1' hq2').2
  have hbracket : 0.735 * ξ^(r-1+r*J) - 7.893 + 2.525*(2*Ξ)⁻¹^J + 0.044*J/L
      ≤ -0.12 - 1.021*(6.3*x + q) := by
    have h := hnum
    rw [← hξdef] at h
    rw [← hΞdef] at h
    rw [← hLdef] at h
    rw [← hxdef] at h
    linarith only [h]
  -- I bound
  have hxe : ξ^(r-1)*Ξ^J = ξ^(r-1+r*J) := by
    rw [hΞdef, ← pow_mul, ← pow_add]
  have hT3' : (d:ℝ)*hh*(ξ^(r-1)*(Ξ^J*T₀)) ≤ 0.735*ξ^(r-1+r*J)*S₀*Dm := by
    have h1 : ((d:ℝ)*hh*T₀)*(ξ^(r-1)*Ξ^J) ≤ (0.735*S₀*Dm)*(ξ^(r-1)*Ξ^J) :=
      mul_le_mul_of_nonneg_right hT3 (by positivity)
    have h2 : ((d:ℝ)*hh*T₀)*(ξ^(r-1)*Ξ^J) = (d:ℝ)*hh*(ξ^(r-1)*(Ξ^J*T₀)) := by ring
    have h3 : (0.735*S₀*Dm)*(ξ^(r-1)*Ξ^J) = 0.735*ξ^(r-1+r*J)*S₀*Dm := by rw [hxe]; ring
    linarith only [h1, h2, h3]
  have hthird_eq : 1.01*(2.5*(Ξ⁻¹)^J*S₀/2^J)*Dm = 2.525*(2*Ξ)⁻¹^J*S₀*Dm := by
    have hbase : Ξ⁻¹ / 2 = (2*Ξ)⁻¹ := by rw [mul_inv]; ring
    have hb : (Ξ⁻¹)^J/2^J = ((2*Ξ)⁻¹)^J := by rw [← div_pow, hbase]
    calc 1.01*(2.5*(Ξ⁻¹)^J*S₀/2^J)*Dm = 2.525*((Ξ⁻¹)^J/2^J)*S₀*Dm := by ring
      _ = 2.525*(2*Ξ)⁻¹^J*S₀*Dm := by rw [hb]
  have hI : (d:ℝ)*hh*(ξ^(r-1)*(Ξ^J*T₀)) - 7.893*S₀*Dm
      + 1.01*(2.5*(Ξ⁻¹)^J*S₀/2^J)*Dm + 0.044*J/L*S₀*Dm
      ≤ S₀*Dm*(-0.12 - 6.4323*x - 1.021*q) := by
    calc (d:ℝ)*hh*(ξ^(r-1)*(Ξ^J*T₀)) - 7.893*S₀*Dm
          + 1.01*(2.5*(Ξ⁻¹)^J*S₀/2^J)*Dm + 0.044*J/L*S₀*Dm
        = (d:ℝ)*hh*(ξ^(r-1)*(Ξ^J*T₀)) - 7.893*S₀*Dm
          + 2.525*(2*Ξ)⁻¹^J*S₀*Dm + 0.044*J/L*S₀*Dm := by rw [hthird_eq]
      _ ≤ S₀*Dm*(0.735*ξ^(r-1+r*J) - 7.893 + 2.525*(2*Ξ)⁻¹^J + 0.044*J/L) := by
          nlinarith only [hT3']
      _ ≤ S₀*Dm*(-0.12 - 6.4323*x - 1.021*q) := by
          apply mul_le_mul_of_nonneg_left _ hSDnn
          linarith only [hbracket]
  have hqk : Dm * q = k := by
    rw [hq]
    field_simp
  have hI2 : 2^r * ((d:ℝ)*hh*(ξ^(r-1)*(Ξ^J*T₀)) - 7.893*S₀*Dm
      + 1.01*(2.5*(Ξ⁻¹)^J*S₀/2^J)*Dm + 0.044*J/L*S₀*Dm)
      ≤ 2^r*S₀*Dm*(-0.12 - 6.4323*x) - 2.042*A := by
    have h1 : 2^r * ((d:ℝ)*hh*(ξ^(r-1)*(Ξ^J*T₀)) - 7.893*S₀*Dm
        + 1.01*(2.5*(Ξ⁻¹)^J*S₀/2^J)*Dm + 0.044*J/L*S₀*Dm)
        ≤ 2^r*(S₀*Dm*(-0.12 - 6.4323*x - 1.021*q)) :=
      mul_le_mul_of_nonneg_left hI h2rpos.le
    have e1 : 2^r*(S₀*Dm*(-0.12 - 6.4323*x - 1.021*q))
        = 2^r*S₀*Dm*(-0.12 - 6.4323*x) - 2^r*1.021*(S₀*(Dm*q)) := by ring
    rw [hqk] at e1
    have e2 : 2^r*1.021*(S₀*k) = 2.042*A := by rw [hAdef, h2r]; ring
    linarith only [h1, e1, e2]
  -- Tp / X bounds
  have hB : (1-ξ)*x*(Ξ^J*T₀) ≤ β := by
    rw [hβdef]
    have h2 : (1-ξ)*x*(Ξ^J*T₀) = ((1-ξ)*T₀)*(x*Ξ^J) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right hT2 (by positivity)
  have hTp1 : (Tp:ℝ) + 1 ≤ β + 1 := by linarith only [hTple, hB]
  have hXleA : (X:ℝ) ≤ A := by rw [hAdef]; exact hXle
  have hlogle : Real.log ((2*(X:ℝ)+1)*((Tp:ℝ)+1)) ≤ Real.log ((2*A+1)*(β+1)) := by
    apply Real.log_le_log (by positivity)
    have h1 : 2*(X:ℝ)+1 ≤ 2*A+1 := by linarith only [hXleA]
    exact mul_le_mul h1 hTp1 (by positivity) (by positivity)
  -- A and C facts
  have hA1 : (1:ℝ) ≤ A := by
    rw [hAdef]
    have h2p : (1:ℝ) ≤ 2^(r-1) := one_le_pow₀ (by norm_num)
    have hS1 : (1:ℝ) ≤ S₀ := by linarith only [hS608]
    have h := mul_le_mul (mul_le_mul h2p hk1 (by norm_num) (by positivity)) hS1
      (by norm_num) (by positivity)
    linarith only [h]
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA1
  have hAnn : 0 ≤ A := le_of_lt hApos
  have hβnn : 0 ≤ β := by rw [hβdef]; positivity
  have hc0nn : 0 ≤ c₀ := by rw [hc0def]; exact c0_nonneg_I
  have hlogAnn : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hCpos : 0 < C := by
    rw [hCdef]; linarith only [hApos, hlogAnn, hc0nn]
  have hTC : ((Tp:ℝ)+1)*C ≤ (β+1)*C := mul_le_mul_of_nonneg_right hTp1 hCpos.le
  have hCexp : (β+1)*C =
      β*(2*A) + β*(2*Real.log A + c₀ + 3) + 2*A + (2*Real.log A + c₀ + 3) := by
    rw [hCdef]; ring
  -- log A facts
  have hlogA : Real.log A = R1*Real.log 2 + Real.log k + Real.log S₀ := by
    rw [hAdef, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, hR1def]
  have hla : Real.log (2*A+1) ≤ 8 + 0.7*R1 + 43.5*L + S₀/608 := by
    have hfac : 2*A+1 = 2*A*(1 + 1/(2*A)) := by field_simp
    rw [hfac, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), hlogA]
    have h1 : Real.log (1 + 1/(2*A)) ≤ 1/(2*A) := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1/(2*A) by positivity)
      linarith only [h]
    have h2 : 1/(2*A) ≤ 1/2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith only [hA1]
    have h5 : R1*Real.log 2 ≤ R1*0.6932 := mul_le_mul_of_nonneg_left log_two_le_I hR1nn
    linarith only [h1, h2, h5, hlogS, hlogk, log_two_le_I, hR1nn]
  have hlb : Real.log (β+1) ≤ 7.6 + Dm/608 := by
    have ha : x*Ξ^J ≤ 1 := by
      have h := mul_le_mul hxle1 hΞJle1 hΞJnn (by norm_num : (0:ℝ) ≤ 1)
      simpa using h
    have hβle : β ≤ 6.3*Dm := by
      rw [hβdef]
      have h := mul_le_mul_of_nonneg_left ha (by positivity : (0:ℝ) ≤ 6.3*Dm)
      linarith only [h]
    have h1 : β + 1 ≤ 8*Dm := by nlinarith only [hβle, hDm1]
    have h2 : Real.log (β+1) ≤ Real.log (8*Dm) := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) (ne_of_gt hDpos)] at h2
    have h3 : Real.log Dm ≤ 5.5 + Dm/608 := log_le_lin_I Dm hDm608
    linarith only [h2, h3, log_eight_le_I]
  have hbet : β*(2*Real.log A + c₀ + 3) ≤ 0.071*Z := by
    rw [hlogA, hβdef]
    have e : 6.3*Dm*(x*Ξ^J)*(2*(R1*Real.log 2 + Real.log k + Real.log S₀) + c₀ + 3)
        = 12.6*Dm*(x*Ξ^J)*R1*Real.log 2 + 12.6*Dm*(x*Ξ^J)*Real.log k
          + 12.6*Dm*(x*Ξ^J)*Real.log S₀ + 6.3*Dm*(x*Ξ^J)*(c₀+3) := by ring
    rw [e]
    have hxe1 : x*Ξ^J ≤ 1 := by
      have h := mul_le_mul hxle1 hΞJle1 hΞJnn (by norm_num : (0:ℝ) ≤ 1)
      simpa using h
    have hΞJlogk : Ξ^J * Real.log k ≤ 1 := by
      rw [hΞJinv, inv_mul_eq_div, div_le_one hkpos]
      linarith only [Real.log_le_sub_one_of_pos hkpos]
    have hxlogk : (x*Ξ^J)*Real.log k ≤ 1 := by
      have h1 : x*Ξ^J ≤ 1*Ξ^J := mul_le_mul_of_nonneg_right hxle1 hΞJnn
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.log_nonneg hk1)
      linarith only [h2, hΞJlogk]
    have t1 : 12.6*Dm*(x*Ξ^J)*R1*Real.log 2 ≤ 12.6*Dm*R1 := by
      have h : (x*Ξ^J)*Real.log 2 ≤ 1 := by
        have h1' : Real.log 2 ≤ 1 := by linarith only [log_two_le_I]
        have h := mul_le_mul hxe1 h1' (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
          (by norm_num : (0:ℝ) ≤ 1)
        linarith only [h]
      calc 12.6*Dm*(x*Ξ^J)*R1*Real.log 2 = 12.6*Dm*R1*((x*Ξ^J)*Real.log 2) := by ring
        _ ≤ 12.6*Dm*R1*1 := mul_le_mul_of_nonneg_left h
              (mul_nonneg (mul_nonneg (by norm_num) hDpos.le) hR1nn)
        _ = 12.6*Dm*R1 := by ring
    have t2 : 12.6*Dm*(x*Ξ^J)*Real.log k ≤ 12.6*Dm := by
      calc 12.6*Dm*(x*Ξ^J)*Real.log k = 12.6*Dm*((x*Ξ^J)*Real.log k) := by ring
        _ ≤ 12.6*Dm*1 := mul_le_mul_of_nonneg_left hxlogk (by positivity)
        _ = 12.6*Dm := by ring
    have hDmZdiv : Dm ≤ Z/2432 := by
      rw [hZdef, le_div_iff₀ (by norm_num : (0:ℝ) < 2432)]
      have h1 : 4*608*Dm ≤ 4*(S₀*Dm) := by
        have h := mul_le_mul_of_nonneg_left hS608 (by linarith only [hDpos] : (0:ℝ) ≤ 4*Dm)
        linarith only [h]
      have h2 : 4*(S₀*Dm) ≤ 2^r*(S₀*Dm) := mul_le_mul_of_nonneg_right h2r4 (by positivity)
      linarith only [h1, h2]
    have hDmS0 : Dm*S₀ ≤ Z/4 := by
      rw [hZdef, le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
      have h0 : (0:ℝ) ≤ S₀*Dm := by positivity
      have h := mul_le_mul_of_nonneg_right h2r4 h0
      linarith only [h]
    have t3 : 12.6*Dm*(x*Ξ^J)*Real.log S₀ ≤ 0.034*Z := by
      have h : (x*Ξ^J)*Real.log S₀ ≤ 5.5 + S₀/608 := by
        calc (x*Ξ^J)*Real.log S₀ ≤ 1*(5.5 + S₀/608) :=
              mul_le_mul hxe1 hlogS hlogSnn (by norm_num)
          _ = 5.5 + S₀/608 := by ring
      have h1 : 12.6*Dm*(x*Ξ^J)*Real.log S₀ ≤ 12.6*Dm*(5.5 + S₀/608) := by
        rw [show 12.6*Dm*(x*Ξ^J)*Real.log S₀ = 12.6*Dm*((x*Ξ^J)*Real.log S₀) by ring]
        exact mul_le_mul_of_nonneg_left h (by positivity)
      have h2 : 12.6*Dm*(5.5 + S₀/608) = 69.3*Dm + (12.6/608)*(Dm*S₀) := by ring
      have h3 : 69.3*Dm ≤ 0.0285*Z := by
        have hc1 : (69.3:ℝ)/2432 ≤ 0.0285 := by norm_num
        calc 69.3*Dm ≤ 69.3*(Z/2432) := mul_le_mul_of_nonneg_left hDmZdiv (by norm_num)
          _ = ((69.3:ℝ)/2432)*Z := by ring
          _ ≤ 0.0285*Z := mul_le_mul_of_nonneg_right hc1 hZnn
      have h4 : (12.6/608)*(Dm*S₀) ≤ 0.0052*Z := by
        have hc1 : ((12.6:ℝ)/608)/4 ≤ 0.0052 := by norm_num
        calc (12.6/608)*(Dm*S₀) ≤ (12.6/608)*(Z/4) :=
              mul_le_mul_of_nonneg_left hDmS0 (by norm_num)
          _ = ((12.6/608)/4)*Z := by ring
          _ ≤ 0.0052*Z := mul_le_mul_of_nonneg_right hc1 hZnn
      linarith only [h1, h2, h3, h4, hZnn]
    have t4 : 6.3*Dm*(x*Ξ^J)*(c₀+3) ≤ 19.6*Dm := by
      have hc : c₀ + 3 ≤ 3.1 := by
        have h := c0_le_I; rw [hc0def]; linarith only [h]
      have h : (x*Ξ^J)*(c₀+3) ≤ 3.1 := by
        have h := mul_le_mul hxe1 hc (by linarith only [hc0nn] : (0:ℝ) ≤ c₀+3) (by norm_num)
        linarith only [h]
      have h2 : 6.3*Dm*((x*Ξ^J)*(c₀+3)) ≤ 6.3*Dm*3.1 :=
        mul_le_mul_of_nonneg_left h (by positivity)
      have h3 : 6.3*Dm*(x*Ξ^J)*(c₀+3) = 6.3*Dm*((x*Ξ^J)*(c₀+3)) := by ring
      have h4 : 6.3*Dm*(3.1:ℝ) = 19.53*Dm := by ring
      linarith only [h2, h3, h4, hDpos]
    have hR1_2r : R1 ≤ 2^r := by
      rw [hR1def]
      calc (((r-1:ℕ)):ℝ) ≤ (r:ℝ) := by
            rw [Nat.cast_sub hr1, Nat.cast_one]; linarith only [hrR]
        _ ≤ (2:ℝ)^r := r_le_two_pow r
    have tR : 12.6*R1*Dm ≤ 0.0208*Z := by
      have h2rDm : 2^r*Dm ≤ Z/608 := by
        rw [hZdef, le_div_iff₀ (by norm_num : (0:ℝ) < 608)]
        have h1 : (608:ℝ)*Dm ≤ S₀*Dm := mul_le_mul_of_nonneg_right hS608 hDpos.le
        have h2 : 2^r*((608:ℝ)*Dm) ≤ 2^r*(S₀*Dm) := mul_le_mul_of_nonneg_left h1 h2rpos.le
        linarith only [h2]
      have hc1 : (12.6:ℝ)/608 ≤ 0.0208 := by norm_num
      calc 12.6*R1*Dm = 12.6*(R1*Dm) := by ring
        _ ≤ 12.6*(2^r*Dm) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hR1_2r hDpos.le)
                (by norm_num)
        _ ≤ 12.6*(Z/608) := mul_le_mul_of_nonneg_left h2rDm (by norm_num)
        _ = ((12.6:ℝ)/608)*Z := by ring
        _ ≤ 0.0208*Z := mul_le_mul_of_nonneg_right hc1 hZnn
    have tD : 32.2*Dm ≤ 0.0133*Z := by
      have hc1 : (32.2:ℝ)/2432 ≤ 0.0133 := by norm_num
      calc 32.2*Dm ≤ 32.2*(Z/2432) := mul_le_mul_of_nonneg_left hDmZdiv (by norm_num)
        _ = ((32.2:ℝ)/2432)*Z := by ring
        _ ≤ 0.0133*Z := mul_le_mul_of_nonneg_right hc1 hZnn
    calc 12.6*Dm*(x*Ξ^J)*R1*Real.log 2 + 12.6*Dm*(x*Ξ^J)*Real.log k
          + 12.6*Dm*(x*Ξ^J)*Real.log S₀ + 6.3*Dm*(x*Ξ^J)*(c₀+3)
        ≤ 12.6*Dm*R1 + 32.2*Dm + 0.034*Z := by linarith only [t1, t2, t3, t4]
      _ ≤ 0.0208*Z + 0.0133*Z + 0.034*Z := by linarith only [tR, tD]
      _ ≤ 0.071*Z := by nlinarith only [hZnn]
  have hrem : 2*Real.log A + c₀ + 3 ≤ 1.4*R1 + 87*L + S₀/300 + 15 := by
    rw [hlogA]
    have h5 : R1*Real.log 2 ≤ R1*0.6932 := mul_le_mul_of_nonneg_left log_two_le_I hR1nn
    have hc : c₀ ≤ 0.1 := by rw [hc0def]; exact c0_le_I
    linarith only [h5, hlogS, hlogk, hc, hS608, hR1nn]
  -- Z facts
  have hZdm : 2432*Dm ≤ Z := by
    rw [hZdef]
    have h1 : (2432:ℝ) ≤ 2^r*S₀ := by
      calc (2432:ℝ) = 4*608 := by norm_num
        _ ≤ 2^r*S₀ := mul_le_mul h2r4 hS608 (by norm_num) (by positivity)
    calc 2432*Dm ≤ (2^r*S₀)*Dm := mul_le_mul_of_nonneg_right h1 hDpos.le
      _ = 2^r*S₀*Dm := by ring
  have hZ8 : (8.8e8:ℝ) ≤ Z := by nlinarith only [hZdm, hDm363]
  have hZx2 : 0.5847*Z ≤ Zx := by
    rw [hZxdef, hZdef]
    have h0 : (0:ℝ) ≤ 2^r*S₀*Dm := by positivity
    nlinarith only [mul_le_mul_of_nonneg_left hxlo h0]
  have hslack : 0.12*Z + 0.1323*Zx ≥ 0.1973*Z := by
    have h1 : 0.1323*(0.5847*Z) ≤ 0.1323*Zx := mul_le_mul_of_nonneg_left hZx2 (by norm_num)
    linarith only [h1, hZnn]
  have hS0Z : S₀ ≤ Z/4 := by
    rw [hZdef, le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    have h0 : (0:ℝ) ≤ S₀ := by linarith only [hS608]
    have h1 : S₀*4 ≤ S₀*2^r := mul_le_mul_of_nonneg_left h2r4 h0
    have h2 : S₀*2^r ≤ 2^r*S₀*Dm := by
      have hx := mul_le_mul_of_nonneg_left hDm1 (by positivity : (0:ℝ) ≤ 2^r*S₀)
      linarith only [hx]
    linarith only [h1, h2]
  have h2rZdiv : 2^r ≤ Z/608 := by
    rw [hZdef, le_div_iff₀ (by norm_num : (0:ℝ) < 608)]
    have h1 : (608:ℝ) ≤ S₀*Dm := by
      have h := mul_le_mul_of_nonneg_left hS608 hDpos.le
      linarith only [h, hDm1]
    nlinarith only [mul_le_mul_of_nonneg_left h1 h2rpos.le]
  have hR1Z : 2.1*R1 ≤ 0.004*Z := by
    have hR1_2r : R1 ≤ 2^r := by
      rw [hR1def]
      calc (((r-1:ℕ)):ℝ) ≤ (r:ℝ) := by
            rw [Nat.cast_sub hr1, Nat.cast_one]; linarith only [hrR]
        _ ≤ (2:ℝ)^r := r_le_two_pow r
    have hc1 : (2.1:ℝ)/608 ≤ 0.004 := by norm_num
    calc 2.1*R1 ≤ 2.1*2^r := mul_le_mul_of_nonneg_left hR1_2r (by norm_num)
      _ ≤ 2.1*(Z/608) := mul_le_mul_of_nonneg_left h2rZdiv (by norm_num)
      _ = ((2.1:ℝ)/608)*Z := by ring
      _ ≤ 0.004*Z := mul_le_mul_of_nonneg_right hc1 hZnn
  have hDmZdiv' : Dm ≤ Z/2432 := by
    rw [hZdef, le_div_iff₀ (by norm_num : (0:ℝ) < 2432)]
    have h1 : 4*608*Dm ≤ 4*(S₀*Dm) := by
      have h := mul_le_mul_of_nonneg_left hS608 (by linarith only [hDpos] : (0:ℝ) ≤ 4*Dm)
      linarith only [h]
    have h2 : 4*(S₀*Dm) ≤ 2^r*(S₀*Dm) := mul_le_mul_of_nonneg_right h2r4 (by positivity)
    linarith only [h1, h2]
  have hLZ : 130.5*L ≤ 0.0005*Z := by
    have h1 : 130.5*L ≤ 0.0005*Dm := by
      have a : L ≤ Dm/262144 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 262144)]; linarith only [hKL]
      calc 130.5*L ≤ 130.5*(Dm/262144) := mul_le_mul_of_nonneg_left a (by norm_num)
        _ = (130.5/262144)*Dm := by ring
        _ ≤ 0.0005*Dm := mul_le_mul_of_nonneg_right (by norm_num) hDpos.le
    calc 130.5*L ≤ 0.0005*Dm := h1
      _ ≤ 0.0005*(Z/2432) := mul_le_mul_of_nonneg_left hDmZdiv' (by norm_num)
      _ = (0.0005/2432)*Z := by ring
      _ ≤ 0.0005*Z := mul_le_mul_of_nonneg_right (by norm_num) hZnn
  have hDmZ : Dm/608 ≤ 0.0007*Z := by
    calc Dm/608 ≤ (Z/2432)/608 := by
          rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
          linarith only [hDmZdiv']
      _ = (1/(2432*608))*Z := by ring
      _ ≤ 0.0007*Z := mul_le_mul_of_nonneg_right (by norm_num) hZnn
  have hconst : 34 ≤ 4e-8*Z := by linarith only [hZ8]
  -- beta*2A
  have hbetaA : β*(2*A) = 6.3*Zx := by
    have h2 : β*(2*A) = 6.3*Dm*x*(Ξ^J*k)*(2*2^(r-1))*S₀ := by rw [hβdef, hAdef]; ring
    rw [hΞk] at h2
    have h3 : 6.3*Dm*x*(1:ℝ)*(2*2^(r-1))*S₀ = 6.3*Dm*x*2^r*S₀ := by
      rw [h2r]; ring
    have h4 : 6.3*Dm*x*2^r*S₀ = 6.3*Zx := by rw [hZxdef]; ring
    linarith only [h2, h3, h4]
  have hZeq1 : 2^r*S₀*Dm*(-0.12 - 6.4323*x) = -0.12*Z - 6.4323*Zx := by
    rw [hZdef, hZxdef]; ring
  have hI2' : 2^r * ((d:ℝ)*hh*(ξ^(r-1)*(Ξ^J*T₀)) - 7.893*S₀*Dm
      + 1.01*(2.5*(Ξ⁻¹)^J*S₀/2^J)*Dm + 0.044*J/L*S₀*Dm)
      ≤ -0.12*Z - 6.4323*Zx - 2.042*A := by linarith only [hI2, hZeq1]
  -- final assembly
  calc Real.log ((2*(X:ℝ)+1) * ((Tp:ℝ) + 1)) + Real.log 2 +
        2^r * ((d:ℝ) * hh * (ξ^(r-1) * (Ξ^J * T₀)) - 7.893 * S₀ * Dm +
          1.01 * (2.5 * (Ξ⁻¹)^J * S₀ / 2^J) * Dm +
          0.044 * J / L * S₀ * Dm)
        + ((Tp:ℝ) + 1) * C
      ≤ Real.log ((2*A+1)*(β+1)) + Real.log 2 + (-0.12*Z - 6.4323*Zx - 2.042*A)
        + (β+1)*C := by linarith only [hlogle, hI2', hTC]
    _ = Real.log ((2*A+1)*(β+1)) + Real.log 2 + (-0.12*Z - 6.4323*Zx - 2.042*A)
        + (β*(2*A) + β*(2*Real.log A + c₀ + 3) + 2*A + (2*Real.log A + c₀ + 3)) := by
        rw [hCexp]
    _ = Real.log (2*A+1) + Real.log (β+1) + Real.log 2 + β*(2*Real.log A + c₀ + 3)
        + (2*Real.log A + c₀ + 3) - 0.12*Z - 0.1323*Zx - 0.042*A := by
        rw [Real.log_mul (by positivity) (by positivity), hbetaA]
        ring
    _ < -Real.log 2 := by
        linarith only [hla, hlb, log_two_le_I, hbet, hrem, hslack, hR1Z, hLZ, hDmZ,
          hconst, hZ8, hS0Z, hAnn]

end Work.BW
