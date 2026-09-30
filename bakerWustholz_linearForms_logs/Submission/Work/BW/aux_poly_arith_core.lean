import Mathlib
import Submission.Work.BW.aux_poly_arith
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.Mu_ge_Me
import Submission.Work.BW.sigma_sum_le
import Submission.Work.BW.split_aux
import Submission.Work.BW.card_AuxEqnIdx_mul_factorial_le
import Submission.Work.BW.Mu_lower_bound
import Submission.Work.BW.D_ge

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

private lemma one_le_mul_real' {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  have h := mul_le_mul ha hb zero_le_one (le_trans zero_le_one ha)
  simpa using h

set_option maxHeartbeats 4000000 in
/-- The three arithmetic terms of `aux_poly_arith` (BW (12)) -- the `log Mu` term, the `d^2` term
and the `rho` term -- are together at most `13.4 r d h D`.  This is exactly the intermediate bound
established inside the (proved) `aux_poly_arith` proof (`0.155 + 0.5 + 0.45 + 12.2 = 13.305`
units of `r d h D`), with the final constant `13.6` of that proof relaxed to `13.4`.  It is the
input to `aux_poly_arith_ball`, which adds the Siegel term `d log(4 d Mu)` on top. -/
theorem aux_poly_arith_core {K : Type*} [Field K] [NumberField K] {r : ℕ} (hr : 2 ≤ r)
    (h : ℕ) (hh : 19 ≤ h) (σ : Fin r → ℝ) (hσ : ∀ j, 1 / (Module.finrank ℚ K : ℝ) ≤ σ j) :
    let d : ℝ := Module.finrank ℚ K
    let D : ℝ := pD r (Module.finrank ℚ K) σ
    let S : ℕ := pS r (Module.finrank ℚ K) h
    let D0 : ℕ := pD0 r (Module.finrank ℚ K) σ
    let Dj : Fin r → ℕ := pDj r (Module.finrank ℚ K) σ
    let Mu : ℕ := h * (D0 + 1) * ∏ j, (Dj j + 1)
    let Me : ℕ := Fintype.card (AuxEqnIdx r S (pT r (Module.finrank ℚ K) σ))
    let rho : ℝ := (Me : ℝ) / ((Mu : ℝ) - Me)
    (1 / 2) * d * rho * Real.log (Mu : ℝ) + d ^ 2 * ((∑ j, σ j) + (1 / 2) * r * Real.log 2)
      + d * rho * (1.7 * (h : ℝ) * (11.75 * r * D)
          + (D / d) * ((S : ℝ) * (S + 1) / (2 * (S : ℝ) + 1)))
      ≤ 13.4 * (r : ℝ) * d * (h : ℝ) * D := by
  dsimp only
  have hdn : 1 ≤ Module.finrank ℚ K := Module.finrank_pos_iff_exists_ne_zero.mpr ⟨1, one_ne_zero⟩
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hd
  set D : ℝ := pD r (Module.finrank ℚ K) σ with hD
  set S : ℝ := (pS r (Module.finrank ℚ K) h : ℝ) with hS
  set Mu : ℝ := ((h * (pD0 r (Module.finrank ℚ K) σ + 1) *
    ∏ j, (pDj r (Module.finrank ℚ K) σ j + 1) : ℕ) : ℝ) with hMu
  set Me : ℝ := (Fintype.card (AuxEqnIdx r (pS r (Module.finrank ℚ K) h)
    (pT r (Module.finrank ℚ K) σ)) : ℝ) with hMe
  set rho : ℝ := Me / (Mu - Me) with hrho
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hh19 : (19:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hd1 : (1:ℝ) ≤ d := by rw [hd]; exact_mod_cast hdn
  have hd0 : (0:ℝ) < d := lt_of_lt_of_le zero_lt_one hd1
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  have hhpos : (0:ℝ) < (h:ℝ) := by linarith
  -- Mu facts
  have hMu_ge1_nat : 1 ≤ h * (pD0 r (Module.finrank ℚ K) σ + 1) *
      ∏ j, (pDj r (Module.finrank ℚ K) σ j + 1) := by
    have h1 : 1 ≤ h := by omega
    have h2 : 1 ≤ pD0 r (Module.finrank ℚ K) σ + 1 := Nat.le_add_left 1 _
    have h3 : 1 ≤ ∏ j, (pDj r (Module.finrank ℚ K) σ j + 1) :=
      Finset.one_le_prod (fun j _ => Nat.le_add_left 1 _)
    calc (1:ℕ) = 1 * 1 * 1 := by norm_num
      _ ≤ h * (pD0 r (Module.finrank ℚ K) σ + 1) * ∏ j, (pDj r (Module.finrank ℚ K) σ j + 1) := by
          gcongr
  have hMu_pos : 0 < Mu := by
    rw [hMu]; exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hMu_ge1_nat)
  have hMu_ge1 : (1:ℝ) ≤ Mu := by rw [hMu]; exact_mod_cast hMu_ge1_nat
  have hlogMu_nn : 0 ≤ Real.log Mu := Real.log_nonneg hMu_ge1
  -- rho bound from Mu >= 3.3 Me
  have hMe3 : (3.3:ℝ) * Me ≤ Mu := by
    rw [hMe, hMu]
    exact (Mu_ge_Me r h hr hh σ hσ).1
  have hsub_pos : 0 < Mu - Me := by nlinarith [hMe3, hMu_pos]
  have hρ : rho ≤ 0.435 := by
    rw [hrho, div_le_iff₀ hsub_pos]
    nlinarith [hMe3, hMu_pos]
  -- S is 16 r d h
  have hSeq : S = 16 * (r:ℝ) * d * (h:ℝ) := by
    rw [hS, hd]; unfold pS; push_cast; ring
  have hSge : (608:ℝ) ≤ S := by
    rw [hSeq]
    have h2 : (2:ℝ) ≤ (r:ℝ) := hr2
    have hd : (1:ℝ) ≤ d := hd1
    have hh2 : (19:ℝ) ≤ (h:ℝ) := hh19
    have hrd : (2*1:ℝ) ≤ (r:ℝ)*d := mul_le_mul h2 hd (by norm_num) (by linarith)
    have hrde : (2*1*19:ℝ) ≤ (r:ℝ)*d*(h:ℝ) := mul_le_mul hrd hh2 (by norm_num) (by positivity)
    linarith [hrde]
  -- D positive and >= d
  have hDpos : 0 < D := by rw [hD]; exact pD_pos hr hdn σ hσ
  have hrr : (4:ℝ) ≤ (r:ℝ)^r := by
    have h1 : (2:ℝ)^2 ≤ (r:ℝ)^2 := pow_le_pow_left₀ (by norm_num) hr2 2
    have h2 : (r:ℝ)^2 ≤ (r:ℝ)^r := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ (r:ℝ)) hr
    calc (4:ℝ) = (2:ℝ)^2 := by norm_num
      _ ≤ (r:ℝ)^2 := h1
      _ ≤ (r:ℝ)^r := h2
  have hlog1 : (1:ℝ) ≤ Real.log (2*(r:ℝ)*d) := by
    rw [Real.le_log_iff_exp_le (by positivity : (0:ℝ) < 2*(r:ℝ)*d)]
    nlinarith [Real.exp_one_lt_d9, hr2, hd1]
  have hD_d : d ≤ D := by
    have hlow := pD_low hr hdn σ hσ
    rw [hD]
    rw [← hd] at hlow
    have h32 : (1:ℝ) ≤ (32:ℝ)^(r+1) := one_le_pow₀ (by norm_num)
    have hfac : (1:ℝ) ≤ 2*(r:ℝ)^r*(32:ℝ)^(r+1)*Real.log (2*(r:ℝ)*d) := by
      have h2 : (1:ℝ) ≤ 2*(r:ℝ)^r*(32:ℝ)^(r+1) :=
        one_le_mul_real' (one_le_mul_real' (by norm_num) (le_trans (by norm_num) hrr)) h32
      exact one_le_mul_real' h2 hlog1
    nlinarith [hlow, hfac, hd1]
  -- the four term bounds
  have hlog : Real.log Mu ≤ 0.7*(r:ℝ)*(h:ℝ)*D := by
    have hDge : 363408*d ≤ D := by rw [hd, hD]; exact D_ge hr σ hσ
    have hD2 : (2:ℝ) ≤ D := by nlinarith [hDge, hd1]
    have hDnn : (0:ℝ) ≤ D := le_of_lt hDpos
    have hD0 : ((pD0 r (Module.finrank ℚ K) σ : ℕ) : ℝ) + 1 ≤ (r:ℝ)*D := by
      have hfl := pD0_le hr hdn σ hσ
      rw [← hD, ← hd] at hfl
      have hrD : (0:ℝ) ≤ (r:ℝ)*D := by positivity
      have h2 : (r:ℝ)*D/(2*Real.log (2*(r:ℝ)*d)) ≤ (r:ℝ)*D/2 :=
        div_le_div_of_nonneg_left hrD (by norm_num) (by linarith [hlog1])
      have h3 : (r:ℝ)*D/2 + 1 ≤ (r:ℝ)*D := by nlinarith [hrD, hD2, hr2]
      linarith [hfl, h2]
    have hDj : ∀ j, ((pDj r (Module.finrank ℚ K) σ j : ℕ) : ℝ) + 1 ≤ D := by
      intro j
      have hfl := pDj_le hr hdn σ hσ j
      rw [← hD, ← hd] at hfl
      have hσj : (1:ℝ) ≤ d*(σ j) := by
        have h := hσ j
        rw [div_le_iff₀ hd0] at h
        linarith [h]
      have hrdσ : (r:ℝ) ≤ (r:ℝ)*d*(σ j) := by nlinarith [hσj, hr2, le_of_lt hd0]
      have h1 : D/((r:ℝ)*d*σ j) ≤ D/(r:ℝ) :=
        div_le_div_of_nonneg_left hDnn hrpos hrdσ
      have h2r : D/(r:ℝ) ≤ D/2 := div_le_div_of_nonneg_left hDnn (by norm_num) (by linarith)
      linarith [hfl, h1, h2r]
    have hMu_le : Mu ≤ (h:ℝ)*((r:ℝ)*D)*D^r := by
      have hpr : ∏ j, (((pDj r (Module.finrank ℚ K) σ j : ℕ) : ℝ) + 1) ≤ D^r := by
        have h1 := prod_le_prod_of_nonneg (s := Finset.univ)
          (f := fun j : Fin r => ((pDj r (Module.finrank ℚ K) σ j : ℕ) : ℝ) + 1)
          (g := fun _ : Fin r => D) (fun j _ => by positivity) (fun j _ => hDj j)
        simpa [Finset.prod_const, Fintype.card_fin] using h1
      have hprodnn : (0:ℝ) ≤ ∏ j, (((pDj r (Module.finrank ℚ K) σ j : ℕ) : ℝ) + 1) :=
        Finset.prod_nonneg (fun j _ => by positivity)
      have hh0 : (0:ℝ) ≤ (h:ℝ) := by positivity
      calc Mu = (h:ℝ)*(((pD0 r (Module.finrank ℚ K) σ : ℕ) : ℝ) + 1)
            * ∏ j, (((pDj r (Module.finrank ℚ K) σ j : ℕ) : ℝ) + 1) := by
            rw [hMu]; push_cast; ring
        _ ≤ (h:ℝ)*((r:ℝ)*D)*D^r :=
            mul_le_mul (mul_le_mul_of_nonneg_left hD0 hh0) hpr hprodnn (by positivity)
    have hlogMu : Real.log Mu ≤ Real.log ((h:ℝ)*((r:ℝ)*D)*D^r) :=
      Real.log_le_log hMu_pos hMu_le
    have heq : Real.log ((h:ℝ)*((r:ℝ)*D)*D^r)
        = Real.log (h:ℝ) + Real.log (r:ℝ) + Real.log D + (r:ℝ)*Real.log D := by
      have h1 : Real.log ((h:ℝ)*((r:ℝ)*D)*D^r)
          = Real.log ((h:ℝ)*((r:ℝ)*D)) + Real.log (D^r) :=
        Real.log_mul (by positivity) (by positivity)
      have h2 : Real.log ((h:ℝ)*((r:ℝ)*D)) = Real.log (h:ℝ) + Real.log ((r:ℝ)*D) :=
        Real.log_mul (ne_of_gt hhpos) (by positivity)
      have h3 : Real.log ((r:ℝ)*D) = Real.log (r:ℝ) + Real.log D :=
        Real.log_mul (ne_of_gt hrpos) (ne_of_gt hDpos)
      have h4 : Real.log (D^r) = (r:ℝ)*Real.log D := Real.log_pow D r
      rw [h1, h2, h3, h4]; ring
    have hbound : Real.log ((h:ℝ)*((r:ℝ)*D)*D^r) ≤ (h:ℝ) + (r:ℝ) + D + (r:ℝ)*D := by
      rw [heq]
      have hlh : Real.log (h:ℝ) ≤ (h:ℝ) := by
        have := Real.log_le_sub_one_of_pos hhpos; linarith
      have hlr : Real.log (r:ℝ) ≤ (r:ℝ) := by
        have := Real.log_le_sub_one_of_pos hrpos; linarith
      have hlD : Real.log D ≤ D := by
        have := Real.log_le_sub_one_of_pos hDpos; linarith
      have hmul : (r:ℝ)*Real.log D ≤ (r:ℝ)*D := mul_le_mul_of_nonneg_left hlD (le_of_lt hrpos)
      linarith [hlh, hlr, hlD, hmul]
    have hfinal1 : (h:ℝ) + (r:ℝ) + D + (r:ℝ)*D ≤ 0.7*(r:ℝ)*(h:ℝ)*D := by
      have hrDpos : 0 < (r:ℝ)*D := mul_pos hrpos hDpos
      have h1 : (h:ℝ) ≤ 0.07*(r:ℝ)*(h:ℝ)*D := by
        have : (1:ℝ) ≤ 0.07*(r:ℝ)*D := by nlinarith [hDge, hr2, hd1]
        nlinarith [this, hh19]
      have h2 : (r:ℝ) ≤ 0.07*(r:ℝ)*(h:ℝ)*D := by
        have : (1:ℝ) ≤ 0.07*(h:ℝ)*D := by nlinarith [hh19, hD2]
        nlinarith [this, hr2]
      have h3 : D ≤ 0.07*(r:ℝ)*(h:ℝ)*D := by
        have : (1:ℝ) ≤ 0.07*(r:ℝ)*(h:ℝ) := by nlinarith [hr2, hh19]
        nlinarith [this, hDnn]
      have h4 : (r:ℝ)*D ≤ 0.42*(r:ℝ)*(h:ℝ)*D := by
        have : (1:ℝ) ≤ 0.42*(h:ℝ) := by nlinarith [hh19]
        nlinarith [this, hrDpos]
      linarith [h1, h2, h3, h4]
    linarith [hlogMu, hbound, hfinal1]
  have hlogterm : (1/2)*d*rho*Real.log Mu ≤ 0.155*(r:ℝ)*d*(h:ℝ)*D := by
    have h1 : rho * Real.log Mu ≤ 0.435 * (0.7*(r:ℝ)*(h:ℝ)*D) := by
      nlinarith [hρ, hlog, hlogMu_nn]
    nlinarith [h1, hd0]
  have hsum : (∑ j, σ j) ≤ (r:ℝ) * d^(r-1) * ∏ j, σ j := by
    have := sigma_sum_le (K := K) σ hσ
    rw [hd]; exact this
  have hSig : d^2 * (∑ j, σ j) ≤ 0.5*(r:ℝ)*d*(h:ℝ)*D := by
    have hprod_nn : 0 ≤ ∏ j, σ j := Finset.prod_nonneg (fun j _ => by
      have hj := hσ j
      have hp : (0:ℝ) < 1/d := one_div_pos.mpr hd0
      linarith)
    have hstep : d^2 * (∑ j, σ j) ≤ d^2 * ((r:ℝ) * d^(r-1) * ∏ j, σ j) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have hpow : d^2 * d^(r-1) = d^(r+1) := by rw [← pow_add]; congr 1; omega
    have hDdef : D = 2*(r:ℝ)^r*(32*d)^(r+1)*Real.log (2*(r:ℝ)*d)*∏ j, σ j := by
      rw [hD, hd]; unfold pD; ring
    have hFac : (1:ℝ) ≤ (h:ℝ)*(r:ℝ)^r*(32:ℝ)^(r+1)*d*Real.log (2*(r:ℝ)*d) := by
      have h32 : (1:ℝ) ≤ (32:ℝ)^(r+1) := one_le_pow₀ (by norm_num)
      have hh1 : (1:ℝ) ≤ (h:ℝ) := by linarith
      exact one_le_mul_real' (one_le_mul_real' (one_le_mul_real' (one_le_mul_real' hh1 (le_trans (by norm_num) hrr)) h32) hd1) hlog1
    have heq : 0.5*(r:ℝ)*d*(h:ℝ)*D
        = ((r:ℝ) * d^(r+1) * ∏ j, σ j) * ((h:ℝ)*(r:ℝ)^r*(32:ℝ)^(r+1)*d*Real.log (2*(r:ℝ)*d)) := by
      rw [hDdef, mul_pow]; ring
    rw [heq]
    calc d^2 * (∑ j, σ j) ≤ d^2 * ((r:ℝ) * d^(r-1) * ∏ j, σ j) := hstep
      _ = (r:ℝ) * d^(r+1) * ∏ j, σ j := by rw [show d^2 * ((r:ℝ) * d^(r-1) * ∏ j, σ j)
            = (r:ℝ) * (d^2 * d^(r-1)) * ∏ j, σ j from by ring, hpow]
      _ ≤ ((r:ℝ) * d^(r+1) * ∏ j, σ j) * ((h:ℝ)*(r:ℝ)^r*(32:ℝ)^(r+1)*d*Real.log (2*(r:ℝ)*d)) :=
          le_mul_of_one_le_right (by positivity) hFac
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
  have hlog2 : d^2 * ((1/2)*(r:ℝ)*Real.log 2) ≤ 0.45*(r:ℝ)*d*(h:ℝ)*D := by
    have hdD : d ≤ 0.9*(h:ℝ)*D := by nlinarith [hh19, hd1, hD_d, hDpos]
    have hkey : Real.log 2 * d^2 ≤ (0.9*(h:ℝ)*D) * d := by
      calc Real.log 2 * d^2 ≤ 1 * d^2 := mul_le_mul_of_nonneg_right hlog2le (by positivity)
        _ = d * d := by ring
        _ ≤ (0.9*(h:ℝ)*D) * d := mul_le_mul_of_nonneg_right hdD (le_of_lt hd0)
    calc d^2 * ((1/2)*(r:ℝ)*Real.log 2) = (1/2)*(r:ℝ) * (Real.log 2 * d^2) := by ring
      _ ≤ (1/2)*(r:ℝ) * ((0.9*(h:ℝ)*D) * d) := mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 0.45*(r:ℝ)*d*(h:ℝ)*D := by ring
  have hSpos : (0:ℝ) < S := by linarith [hSge]
  have hfrac : S*(S+1)/(2*S+1) ≤ 0.501*S := by
    have hpos : (0:ℝ) < 2*S+1 := by linarith [hSge]
    have h501 : (S+1)/(2*S+1) ≤ 0.501 := by
      rw [div_le_iff₀ hpos]; linarith [hSge]
    rw [mul_div_assoc]
    have := mul_le_mul_of_nonneg_left h501 (le_of_lt hSpos)
    linarith [this]
  have hbr : d*rho*(1.7*(h:ℝ)*(11.75*(r:ℝ)*D) + (D/d)*(S*(S+1)/(2*S+1)))
      ≤ 12.2*(r:ℝ)*d*(h:ℝ)*D := by
    set X : ℝ := 1.7*(h:ℝ)*(11.75*(r:ℝ)*D) + (D/d)*(S*(S+1)/(2*S+1)) with hX
    have hXnn : 0 ≤ X := by
      rw [hX]
      apply add_nonneg (by positivity)
      apply mul_nonneg
      · exact div_nonneg (le_of_lt hDpos) (le_of_lt hd0)
      · positivity
    have hdX : d*X = 19.975*(r:ℝ)*d*(h:ℝ)*D + D*(S*(S+1)/(2*S+1)) := by
      rw [hX]; field_simp; ring
    have hX3 : d*X ≤ 27.991*(r:ℝ)*d*(h:ℝ)*D := by
      rw [hdX]
      have h1 : D*(S*(S+1)/(2*S+1)) ≤ D*(0.501*S) :=
        mul_le_mul_of_nonneg_left hfrac (le_of_lt hDpos)
      rw [hSeq] at h1 ⊢
      linarith [h1]
    have hstep1 : d*rho*X ≤ d*(0.435*X) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρ hXnn) (le_of_lt hd0)
    have hstep2 : d*(0.435*X) ≤ 12.2*(r:ℝ)*d*(h:ℝ)*D := by
      have hdX2 : d*(0.435*X) = 0.435*(d*X) := by ring
      rw [hdX2]
      calc 0.435*(d*X) ≤ 0.435*(27.991*(r:ℝ)*d*(h:ℝ)*D) :=
            mul_le_mul_of_nonneg_left hX3 (by norm_num)
        _ = (0.435*27.991)*((r:ℝ)*d*(h:ℝ)*D) := by ring
        _ ≤ 12.2*((r:ℝ)*d*(h:ℝ)*D) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = 12.2*(r:ℝ)*d*(h:ℝ)*D := by ring
    calc d*rho*X ≤ d*(0.435*X) := hstep1
      _ ≤ 12.2*(r:ℝ)*d*(h:ℝ)*D := hstep2
  have hfinal : 1 / 2 * d * rho * Real.log Mu + d ^ 2 * (∑ j, σ j)
      + d ^ 2 * ((1/2)*(r:ℝ)*Real.log 2)
      + d * rho * (1.7 * (h:ℝ) * (11.75 * (r:ℝ) * D) + (D / d) * (S * (S + 1) / (2 * S + 1)))
      ≤ 13.4*(r:ℝ)*d*(h:ℝ)*D := by
    have hnn : (0:ℝ) ≤ (r:ℝ)*d*(h:ℝ)*D := by positivity
    linarith [hlogterm, hSig, hlog2, hbr, hnn]

  calc 1 / 2 * d * rho * Real.log Mu
        + d ^ 2 * ((∑ j, σ j) + (1/2)*(r:ℝ)*Real.log 2)
        + d * rho * (1.7 * (h:ℝ) * (11.75 * (r:ℝ) * D) + (D / d) * (S * (S + 1) / (2 * S + 1)))
      = 1 / 2 * d * rho * Real.log Mu + d ^ 2 * (∑ j, σ j) + d ^ 2 * ((1/2)*(r:ℝ)*Real.log 2)
        + d * rho * (1.7 * (h:ℝ) * (11.75 * (r:ℝ) * D) + (D / d) * (S * (S + 1) / (2 * S + 1))) := by ring
    _ ≤ 13.4*(r:ℝ)*d*(h:ℝ)*D := hfinal

end Work.BW
