import Mathlib
import Submission.Work.Cert.ACSlit.M2eSpec
import Submission.Work.Cert.ACSlit.Shadow
import Submission.Work.ANum3.slit_crude_bound
import Submission.Work.Cert.ACBall.Basic

set_option maxHeartbeats 0

namespace Work.Cert.ACSlit
open Work.Cert

/-- `mu a b ≥ 0` when `a, b ≥ 0`. -/
lemma mu_nonneg' {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ mu a b := by
  have h := Work.Cert.ACBall.mu_ge a b
  have hS : (0:ℝ) < (Work.Cert.S:ℝ) := Work.Cert.ACBall.S_posR
  have : (0:ℝ) ≤ (a:ℝ)*(b:ℝ)/(Work.Cert.S:ℝ) :=
    div_nonneg (mul_nonneg (by exact_mod_cast ha) (by exact_mod_cast hb)) hS.le
  exact_mod_cast (le_trans this h)

/-- `md a b ≥ 0` when `a, b ≥ 0`. -/
lemma md_nonneg' {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ md a b := by
  rw [md, fdiv]
  exact Int.ediv_nonneg (mul_nonneg ha hb) (le_of_lt Work.Cert.ACBall.S_pos)

/-- `mu a b ≥ a·b/S`, in cleared form. -/
lemma mu_ge_mul (a b : ℤ) :
    (a:ℝ)*(b:ℝ) ≤ ((mu a b : ℤ):ℝ)*(Work.Cert.S:ℝ) := by
  have h := Work.Cert.ACBall.mu_ge a b
  rw [div_le_iff₀ Work.Cert.ACBall.S_posR] at h
  exact h

/-- `md a b ≤ a·b/S`, in cleared form. -/
lemma md_le_mul (a b : ℤ) :
    ((md a b : ℤ):ℝ)*(Work.Cert.S:ℝ) ≤ (a:ℝ)*(b:ℝ) := by
  have h := Work.Cert.ACBall.md_le a b
  rw [le_div_iff₀ Work.Cert.ACBall.S_posR] at h
  exact h

/-- `dvu a b ≥ a·S/b`, in cleared form. -/
lemma dvu_ge_mul {a b : ℤ} (hb : 0 < b) :
    (a:ℝ)*(Work.Cert.S:ℝ) ≤ ((dvu a b : ℤ):ℝ)*(b:ℝ) := by
  have h := Work.Cert.ACBall.dvu_ge (a := a) (b := b) hb
  rw [div_le_iff₀ (by exact_mod_cast hb)] at h
  exact h

local notation "SR" => (Work.Cert.S : ℝ)

theorem slitM2e_rounding (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hA : (A : ℝ) = (Work.Cert.S : ℝ) * (1 + r) ^ 2)
    (hE : (E : ℝ) = (Work.Cert.S : ℝ) * (2 * (r - 1) ^ 2))
    (hC1 : (C1 : ℝ) = (Work.Cert.S : ℝ) * (1 + r))
    (hG8 : (G8 : ℝ) = (Work.Cert.S : ℝ) * (8 * r))
    (hA2 : (A2 : ℝ) = (Work.Cert.S : ℝ) * (2 * (1 + r) ^ 2))
    (hrho : 0 ≤ st.rho) (hcU : 0 ≤ w.cU) (hm1U : 0 ≤ w.m1U) (hqU : 0 ≤ w.qU)
    (hsQr : 0 ≤ (Work.Cert.ACSlit.sQ A B2 E C1 G8 A2 ror roi st w).r)
    (hqpU : 0 ≤ w.qpU)
    (hQpr : 0 ≤ (Work.Cert.ACSlit.sQp A B2 E C1 G8 A2 ror roi st w).r)
    (hsL : 0 < w.sL) (hsH : 0 ≤ w.sH)
    (hwlo : 0 < Work.Cert.ACSlit.swlo A B2 E C1 G8 A2 ror roi st w)
    (hdd : 0 < Work.Cert.ACSlit.sdd A B2 E C1 G8 A2 ror roi st w) :
    Work.ANum3.crude r ((1 + r) ^ 2) (2 * (r - 1) ^ 2) (1 + r)
        ((Work.Cert.ACSlit.swhi A B2 E C1 G8 A2 ror roi st w : ℝ) / (Work.Cert.S : ℝ))
        ((Work.Cert.ACSlit.swm1 A B2 E C1 G8 A2 ror roi st w : ℝ) / (Work.Cert.S : ℝ))
        ((Work.Cert.ACSlit.swlo A B2 E C1 G8 A2 ror roi st w : ℝ) / (Work.Cert.S : ℝ))
        ((Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w : ℝ) / (Work.Cert.S : ℝ))
        ((Work.Cert.ACSlit.sQhi A B2 E C1 G8 A2 ror roi st w : ℝ) / (Work.Cert.S : ℝ))
        ((w.sL : ℝ) / (Work.Cert.S : ℝ)) ((w.sH : ℝ) / (Work.Cert.S : ℝ))
      ≤ ((Work.Cert.dvu (Work.Cert.ACSlit.snum A B2 E C1 G8 A2 ror roi st w)
          (Work.Cert.ACSlit.sdd A B2 E C1 G8 A2 ror roi st w) : ℤ) : ℝ)
        / (Work.Cert.S : ℝ) := by
  simp only [Work.ANum3.crude, Work.Cert.ACSlit.swhi, Work.Cert.ACSlit.swm1,
    Work.Cert.ACSlit.swlo, Work.Cert.ACSlit.sQpD, Work.Cert.ACSlit.sQhi,
    Work.Cert.ACSlit.snum, Work.Cert.ACSlit.sdd, Work.Cert.ACSlit.sN0, Work.Cert.ACSlit.sN1,
    Work.Cert.ACSlit.sN2, Work.Cert.ACSlit.sx]
  simp only [Work.Cert.ACSlit.sdd, Work.Cert.ACSlit.swlo] at hdd
  simp only [Work.Cert.ACSlit.swlo] at hwlo
  set Wi : ℤ := w.cU + st.rho + 1 with hWi
  set Wmi : ℤ := w.m1U + st.rho + 1 with hWmi
  set Wloi : ℤ := w.cL - st.rho - 1 with hWloi
  set sLi : ℤ := w.sL with hsLi
  set sHi : ℤ := w.sH with hsHi
  set Qpi : ℤ := w.qpU + (sQp A B2 E C1 G8 A2 ror roi st w).r + mu st.rho A2 + 1 with hQpi
  set Qhii : ℤ := w.qU + (sQ A B2 E C1 G8 A2 ror roi st w).r + mu st.rho Qpi + 1 with hQhii
  set SXi : ℤ := mu (mu (2 * Qhii) A2 + mu Qpi Qpi) (mu C1 Wmi) with hSXi
  set SN1i : ℤ := E + mu A2 Wi + mu C1 sHi + dvu (mu (mu C1 Wmi) Qpi) (2 * sLi) with hSN1i
  set SN2i : ℤ := A2 + dvu (mu C1 Qpi) sLi + dvu (dvu (dvu SXi sLi) sLi) (4 * sLi) with hSN2i
  set SN0i : ℤ := A + mu E Wi + mu A (mu Wi Wi) + mu (mu C1 Wmi) sHi with hSN0i
  set SNUMi : ℤ := mu SN2i (mu Wi Wi) + 2 * mu SN1i Wi + 2 * SN0i with hSNUMi
  set SDDi : ℤ := md G8 (md (md Wloi Wloi) Wloi) with hSDDi
  set W : ℝ := (Wi : ℝ) / SR with hW
  set Wm1 : ℝ := (Wmi : ℝ) / SR with hWm1
  set Wlo : ℝ := (Wloi : ℝ) / SR with hWlo
  set Slo : ℝ := (sLi : ℝ) / SR with hSlo
  set Shi : ℝ := (sHi : ℝ) / SR with hShi
  set Qp : ℝ := (Qpi : ℝ) / SR with hQp
  set Qhi : ℝ := (Qhii : ℝ) / SR with hQhi
  set A1 : ℝ := (2 * (1 + r) ^ 2 + (1 + r) * Qp / Slo +
    (1 + r) * Wm1 * (4 * (1 + r) ^ 2 * Qhi + Qp ^ 2) / (4 * Slo ^ 3)) with hA1d
  set B1 : ℝ := (2 * (r - 1) ^ 2 + 2 * (1 + r) ^ 2 * W + (1 + r) * Shi +
    (1 + r) * Wm1 * Qp / (2 * Slo)) with hB1d
  set C3 : ℝ := ((1 + r) ^ 2 + 2 * (r - 1) ^ 2 * W + (1 + r) ^ 2 * W ^ 2 +
    (1 + r) * Wm1 * Shi) with hC3d
  set NUM : ℝ := A1 * W ^ 2 + 2 * B1 * W + 2 * C3 with hNUM
  set DEN : ℝ := 8 * r * Wlo ^ 3 with hDEN
  clear_value Wi Wmi Wloi sLi sHi Qpi Qhii SXi SN1i SN2i SN0i SNUMi SDDi
    W Wm1 Wlo Slo Shi Qp Qhi A1 B1 C3 NUM DEN
  -- ===== nonnegativity / positivity facts =====
  have hSRpos : (0:ℝ) < SR := Work.Cert.ACBall.S_posR
  have h1r : (0:ℝ) < 1 + r := by linarith
  have hWi0 : (0:ℤ) ≤ Wi := by rw [hWi]; omega
  have hWmi0 : (0:ℤ) ≤ Wmi := by rw [hWmi]; omega
  have hWloi0 : 0 < Wloi := hwlo
  have hsLi0 : (0:ℤ) < sLi := hsL
  have hsHi0 : (0:ℤ) ≤ sHi := hsH
  have hsLiR : (0:ℝ) < (sLi:ℝ) := by exact_mod_cast hsLi0
  have hWiR0 : (0:ℝ) ≤ (Wi:ℝ) := by exact_mod_cast hWi0
  have hWmi0R : (0:ℝ) ≤ (Wmi:ℝ) := by exact_mod_cast hWmi0
  have hsHi0R : (0:ℝ) ≤ (sHi:ℝ) := by exact_mod_cast hsHi0
  have hA2pos : (0:ℤ) < A2 := by
    have h : (0:ℝ) < (A2:ℝ) := by rw [hA2]; positivity
    exact_mod_cast h
  have hQpi0 : (0:ℤ) ≤ Qpi := by
    rw [hQpi]
    have h1 : (0:ℤ) ≤ (sQp A B2 E C1 G8 A2 ror roi st w).r := hQpr
    have h2 : (0:ℤ) ≤ mu st.rho A2 := mu_nonneg' hrho (le_of_lt hA2pos)
    omega
  have hQpi0R : (0:ℝ) ≤ (Qpi:ℝ) := by exact_mod_cast hQpi0
  have hQhii0 : (0:ℤ) ≤ Qhii := by
    rw [hQhii]
    have h1 : (0:ℤ) ≤ (sQ A B2 E C1 G8 A2 ror roi st w).r := hsQr
    have h2 : (0:ℤ) ≤ mu st.rho Qpi := mu_nonneg' hrho hQpi0
    omega
  have hW0 : 0 ≤ W := by rw [hW]; exact div_nonneg hWiR0 hSRpos.le
  have hWm10 : 0 ≤ Wm1 := by
    rw [hWm1]; exact div_nonneg hWmi0R hSRpos.le
  have hWlopos : 0 < Wlo := by
    rw [hWlo]; exact div_pos (by exact_mod_cast hWloi0) hSRpos
  have hSlopos : 0 < Slo := by rw [hSlo]; exact div_pos hsLiR hSRpos
  have hShi0 : 0 ≤ Shi := by rw [hShi]; exact div_nonneg hsHi0R hSRpos.le
  have hQp0 : 0 ≤ Qp := by rw [hQp]; exact div_nonneg hQpi0R hSRpos.le
  have hQhi0 : 0 ≤ Qhi := by
    rw [hQhi]; exact div_nonneg (by exact_mod_cast hQhii0) hSRpos.le
  have hWr : (Wi:ℝ) = SR*W := by rw [hW]; field_simp
  have hWmir : (Wmi:ℝ) = SR*Wm1 := by rw [hWm1]; field_simp
  have hShir : (sHi:ℝ) = SR*Shi := by rw [hShi]; field_simp
  -- ===== component 1 =====
  have s1 : SR * (2*(1+r)^2) ≤ (A2 : ℝ) := le_of_eq hA2.symm
  have s2 : SR * ((1 + r) * Qp / Slo) ≤ ((dvu (mu C1 Qpi) sLi : ℤ) : ℝ) := by
    rw [← mul_le_mul_iff_left₀ hsLiR]
    have h1 := mu_ge_mul C1 Qpi
    have h2 := dvu_ge_mul (a := mu C1 Qpi) (b := sLi) hsL
    have hL : (SR * ((1 + r) * Qp / Slo)) * (sLi : ℝ) = SR * (1 + r) * (Qpi : ℝ) := by
      rw [hQp, hSlo]; field_simp <;> ring
    rw [hL, ← hC1]
    linarith [h1, h2]
  have s3 : SR * ((1+r)*Wm1*(4*(1+r)^2*Qhi + Qp^2)/(4*Slo^3))
      ≤ ((dvu (dvu (dvu SXi sLi) sLi) (4*sLi) : ℤ) : ℝ) := by
    have hL : SR * ((1+r)*Wm1*(4*(1+r)^2*Qhi + Qp^2)/(4*Slo^3))
        = ((4*(1+r)^2*(Qhii:ℝ)*SR + (Qpi:ℝ)^2) * ((1+r)*(Wmi:ℝ))) * SR / (4*(sLi:ℝ)^3) := by
      rw [hWm1, hQhi, hQp, hSlo]; field_simp <;> ring
    rw [hL, div_le_iff₀ (by positivity : (0:ℝ) < 4*(sLi:ℝ)^3)]
    have hSA' : 4*(1+r)^2*(Qhii:ℝ)*SR + (Qpi:ℝ)^2
        ≤ ((mu (2*Qhii) A2 + mu Qpi Qpi:ℤ):ℝ)*SR := by
      have h1 := mu_ge_mul (2*Qhii) A2
      have h2 := mu_ge_mul Qpi Qpi
      have e : 4*(1+r)^2*(Qhii:ℝ)*SR = ((2*Qhii:ℤ):ℝ)*((A2:ℤ):ℝ) := by
        rw [hA2]; push_cast; ring
      rw [Int.cast_add, e]
      nlinarith [h1, h2]
    have hSB : (1+r)*(Wmi:ℝ) ≤ ((mu C1 Wmi:ℤ):ℝ) := by
      rw [← mul_le_mul_iff_left₀ hSRpos]
      have h3 := mu_ge_mul C1 Wmi
      have e : (1+r)*(Wmi:ℝ)*SR = ((C1:ℤ):ℝ)*((Wmi:ℤ):ℝ) := by rw [hC1]; ring
      rw [e]; exact h3
    have hPp0 : 0 ≤ 4*(1+r)^2*(Qhii:ℝ)*SR + (Qpi:ℝ)^2 := by positivity
    have hQb0 : 0 ≤ (1+r)*(Wmi:ℝ) := by positivity
    have hSA0 : 0 ≤ ((mu (2*Qhii) A2 + mu Qpi Qpi:ℤ):ℝ) := by
      have h1 : (0:ℤ) ≤ mu (2*Qhii) A2 := mu_nonneg' (by omega) (le_of_lt hA2pos)
      have h2 : (0:ℤ) ≤ mu Qpi Qpi := mu_nonneg' hQpi0 hQpi0
      exact_mod_cast (by omega : (0:ℤ) ≤ mu (2*Qhii) A2 + mu Qpi Qpi)
    have hsx : (4*(1+r)^2*(Qhii:ℝ)*SR + (Qpi:ℝ)^2) * ((1+r)*(Wmi:ℝ))
        ≤ (SXi:ℝ)*SR^2 := by
      have h4 := mu_ge_mul (mu (2*Qhii) A2 + mu Qpi Qpi) (mu C1 Wmi)
      have hSXiR : (SXi:ℝ) = ((mu (mu (2*Qhii) A2 + mu Qpi Qpi) (mu C1 Wmi):ℤ):ℝ) := by rw [hSXi]
      rw [hSXiR]
      nlinarith [h4, hSA', hSB, hPp0, hQb0, hSA0, hSRpos]
    have h5 : (SXi:ℝ)*SR ≤ ((dvu SXi sLi:ℤ):ℝ)*(sLi:ℝ) := dvu_ge_mul hsL
    have h6 : ((dvu SXi sLi:ℤ):ℝ)*SR ≤ ((dvu (dvu SXi sLi) sLi:ℤ):ℝ)*(sLi:ℝ) :=
      dvu_ge_mul (a := dvu SXi sLi) (b := sLi) hsL
    have h7 : ((dvu (dvu SXi sLi) sLi:ℤ):ℝ)*SR
        ≤ ((dvu (dvu (dvu SXi sLi) sLi) (4*sLi):ℤ):ℝ)*(4*sLi:ℝ) := by
      have h := dvu_ge_mul (a := dvu (dvu SXi sLi) sLi) (b := 4*sLi) (by omega : (0:ℤ) < 4*sLi)
      push_cast at h
      exact h
    have k1 : ((4*(1+r)^2*(Qhii:ℝ)*SR + (Qpi:ℝ)^2) * ((1+r)*(Wmi:ℝ)))*SR ≤ (SXi:ℝ)*SR^3 := by
      have := mul_le_mul_of_nonneg_right hsx hSRpos.le
      nlinarith [this]
    have k2 : (SXi:ℝ)*SR^3 ≤ ((dvu SXi sLi:ℤ):ℝ)*((sLi:ℝ))*SR^2 := by
      have := mul_le_mul_of_nonneg_right h5 (by positivity : (0:ℝ) ≤ SR^2)
      nlinarith [this]
    have k3 : ((dvu SXi sLi:ℤ):ℝ)*((sLi:ℝ))*SR^2
        ≤ ((dvu (dvu SXi sLi) sLi:ℤ):ℝ)*((sLi:ℝ)^2)*SR := by
      have := mul_le_mul_of_nonneg_right h6 (by positivity : (0:ℝ) ≤ (sLi:ℝ)*SR)
      nlinarith [this]
    have k4 : ((dvu (dvu SXi sLi) sLi:ℤ):ℝ)*((sLi:ℝ)^2)*SR
        ≤ ((dvu (dvu (dvu SXi sLi) sLi) (4*sLi):ℤ):ℝ)*(4*(sLi:ℝ)^3) := by
      have := mul_le_mul_of_nonneg_right h7 (sq_nonneg (sLi:ℝ))
      nlinarith [this]
    linarith [k1, k2, k3, k4]
  have hA1 : SR * A1 ≤ (SN2i : ℝ) := by
    rw [hA1d, hSN2i]; push_cast
    linarith [s1, s2, s3]
  have hA1nn : 0 ≤ A1 := by
    rw [hA1d]
    have h1 : (0:ℝ) ≤ 2*(1+r)^2 := by positivity
    have h2 : (0:ℝ) ≤ (1+r)*Qp/Slo := by positivity
    have h3 : (0:ℝ) ≤ (1+r)*Wm1*(4*(1+r)^2*Qhi+Qp^2)/(4*Slo^3) := by positivity
    linarith [h1, h2, h3]
  have hmuWi : SR * W^2 ≤ ((mu Wi Wi : ℤ):ℝ) := by
    rw [← mul_le_mul_iff_left₀ hSRpos]
    have h := mu_ge_mul Wi Wi
    nlinarith [h, hWr]
  have hT1 : SR * (A1 * W ^ 2) ≤ ((mu SN2i (mu Wi Wi) : ℤ) : ℝ) := by
    have hSN2i0 : 0 ≤ (SN2i:ℝ) := le_trans (mul_nonneg hSRpos.le hA1nn) hA1
    have step1 : SR*(A1*W^2) ≤ (SN2i:ℝ)*W^2 := by
      have := mul_le_mul_of_nonneg_right hA1 (sq_nonneg W)
      linarith [this]
    have step2 : (SN2i:ℝ)*W^2 ≤ ((mu SN2i (mu Wi Wi):ℤ):ℝ) := by
      rw [← mul_le_mul_iff_left₀ hSRpos]
      have h4 := mu_ge_mul SN2i (mu Wi Wi)
      nlinarith [h4, hmuWi, hSN2i0]
    linarith [step1, step2]
  -- ===== component 2 =====
  have t1 : SR * (2*(r-1)^2) ≤ (E : ℝ) := le_of_eq hE.symm
  have t2 : SR * (2*(1+r)^2*W) ≤ ((mu A2 Wi : ℤ) : ℝ) := by
    rw [← mul_le_mul_iff_left₀ hSRpos]
    have h := mu_ge_mul A2 Wi
    have e : (SR*(2*(1+r)^2*W))*SR = ((A2:ℤ):ℝ)*((Wi:ℤ):ℝ) := by rw [hA2, hWr]; ring
    rw [e]; exact h
  have t3 : SR * ((1+r)*Shi) ≤ ((mu C1 sHi : ℤ) : ℝ) := by
    rw [← mul_le_mul_iff_left₀ hSRpos]
    have h := mu_ge_mul C1 sHi
    have e : (SR*((1+r)*Shi))*SR = ((C1:ℤ):ℝ)*((sHi:ℤ):ℝ) := by rw [hC1, hShir]; ring
    rw [e]; exact h
  have t4 : SR * ((1+r)*Wm1*Qp/(2*Slo)) ≤ ((dvu (mu (mu C1 Wmi) Qpi) (2*sLi) : ℤ) : ℝ) := by
    rw [← mul_le_mul_iff_left₀ (by positivity : (0:ℝ) < 2*(sLi:ℝ))]
    rw [← mul_le_mul_iff_left₀ hSRpos]
    have h0 := mu_ge_mul C1 Wmi
    have h1 := mu_ge_mul (mu C1 Wmi) Qpi
    have h2 := dvu_ge_mul (a := mu (mu C1 Wmi) Qpi) (b := 2*sLi) (by omega : (0:ℤ) < 2*sLi)
    push_cast at h2
    have e : (SR*((1+r)*Wm1*Qp/(2*Slo)))*(2*(sLi:ℝ))*SR
        = ((C1:ℤ):ℝ)*((Wmi:ℤ):ℝ)*((Qpi:ℤ):ℝ) := by
      rw [hWm1, hQp, hSlo, hC1]; field_simp <;> ring
    rw [e]
    nlinarith [h0, h1, h2, hQpi0R, hWmi0R, hSRpos]
  have hB1 : SR * B1 ≤ (SN1i : ℝ) := by
    rw [hB1d, hSN1i]; push_cast
    linarith [t1, t2, t3, t4]
  have hT2 : SR*(2*B1*W) ≤ 2*((mu SN1i Wi : ℤ):ℝ) := by
    rw [← mul_le_mul_iff_left₀ hSRpos]
    have h4 := mu_ge_mul SN1i Wi
    have hmul : (SR*B1)*((Wi:ℝ)) ≤ (SN1i:ℝ)*((Wi:ℝ)) := mul_le_mul_of_nonneg_right hB1 hWiR0
    have e : (SR*(2*B1*W))*SR = 2*((SR*B1)*((Wi:ℝ))) := by rw [hWr]; ring
    rw [e]
    nlinarith [h4, hmul]
  -- ===== component 3 =====
  have u1 : SR * ((1+r)^2) ≤ (A : ℝ) := le_of_eq hA.symm
  have u2 : SR * (2*(r-1)^2*W) ≤ ((mu E Wi : ℤ) : ℝ) := by
    rw [← mul_le_mul_iff_left₀ hSRpos]
    have h := mu_ge_mul E Wi
    have e : (SR*(2*(r-1)^2*W))*SR = ((E:ℤ):ℝ)*((Wi:ℤ):ℝ) := by rw [hE, hWr]; ring
    rw [e]; exact h
  have u3 : SR * ((1+r)^2*W^2) ≤ ((mu A (mu Wi Wi) : ℤ) : ℝ) := by
    rw [← mul_le_mul_iff_left₀ hSRpos]
    have h1 := mu_ge_mul A (mu Wi Wi)
    have hA0 : (0:ℝ) ≤ (A:ℝ) := by rw [hA]; positivity
    calc (SR*((1+r)^2*W^2))*SR = (1+r)^2 * (SR*W^2) * SR := by ring
      _ ≤ (1+r)^2 * ((mu Wi Wi:ℤ):ℝ) * SR := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hmuWi (by positivity)
          · exact hSRpos.le
      _ = (A:ℝ) * ((mu Wi Wi:ℤ):ℝ) := by rw [hA]; ring
      _ ≤ ((mu A (mu Wi Wi):ℤ):ℝ)*SR := h1
  have u4 : SR * ((1+r)*Wm1*Shi) ≤ ((mu (mu C1 Wmi) sHi : ℤ) : ℝ) := by
    rw [← mul_le_mul_iff_left₀ hSRpos]
    rw [← mul_le_mul_iff_left₀ hSRpos]
    have h0 := mu_ge_mul C1 Wmi
    have h1 := mu_ge_mul (mu C1 Wmi) sHi
    have e : (SR*((1+r)*Wm1*Shi))*SR*SR = ((C1:ℤ):ℝ)*((Wmi:ℤ):ℝ)*((sHi:ℤ):ℝ) := by
      rw [hWm1, hShi, hC1]; field_simp <;> ring
    rw [e]
    nlinarith [h0, h1, hsHi0R, hWmi0R, hSRpos]
  have hC3 : SR * C3 ≤ (SN0i : ℝ) := by
    rw [hC3d, hSN0i]; push_cast
    linarith [u1, u2, u3, u4]
  have hT3 : SR*(2*C3) ≤ 2*((SN0i : ℤ):ℝ) := by linarith [hC3]
  -- ===== denominator =====
  have hSDD : (SDDi : ℝ) ≤ SR*(8*r*Wlo^3) := by
    have hm1 := md_le_mul Wloi Wloi
    have hm2 := md_le_mul (md Wloi Wloi) Wloi
    have hm3 := md_le_mul G8 (md (md Wloi Wloi) Wloi)
    have hmd1nn : (0:ℤ) ≤ md Wloi Wloi := md_nonneg' (le_of_lt hWloi0) (le_of_lt hWloi0)
    have hmd2nn : (0:ℤ) ≤ md (md Wloi Wloi) Wloi := md_nonneg' hmd1nn (le_of_lt hWloi0)
    have hmd1nnR : (0:ℝ) ≤ ((md Wloi Wloi:ℤ):ℝ) := by exact_mod_cast hmd1nn
    have hmd2nnR : (0:ℝ) ≤ ((md (md Wloi Wloi) Wloi:ℤ):ℝ) := by exact_mod_cast hmd2nn
    have hWloi0R : (0:ℝ) ≤ (Wloi:ℝ) := by exact_mod_cast (le_of_lt hWloi0)
    have hwl : SR*(8*r*Wlo^3) = 8*r*(Wloi:ℝ)^3/SR^2 := by rw [hWlo]; field_simp <;> ring
    have hG8nn : (0:ℝ) ≤ (G8:ℝ) := by rw [hG8]; positivity
    rw [hwl, hSDDi]
    rw [le_div_iff₀ (by positivity : (0:ℝ) < SR^2)]
    rw [← mul_le_mul_iff_left₀ hSRpos]
    have e1 : ((md G8 (md (md Wloi Wloi) Wloi):ℤ):ℝ)*SR^2*SR
        = ((md G8 (md (md Wloi Wloi) Wloi):ℤ):ℝ)*SR*SR^2 := by ring
    have stepA : ((md G8 (md (md Wloi Wloi) Wloi):ℤ):ℝ)*SR*SR^2
        ≤ (((G8:ℤ):ℝ)*((md (md Wloi Wloi) Wloi:ℤ):ℝ))*SR^2 :=
      mul_le_mul_of_nonneg_right hm3 (by positivity : (0:ℝ) ≤ SR^2)
    have stepB : (((G8:ℤ):ℝ)*((md (md Wloi Wloi) Wloi:ℤ):ℝ))*SR^2
        ≤ ((G8:ℤ):ℝ)*(((md Wloi Wloi:ℤ):ℝ)*((Wloi:ℝ)))*SR := by
      have hb := mul_le_mul_of_nonneg_left hm2 hG8nn
      have hb2 := mul_le_mul_of_nonneg_right hb hSRpos.le
      nlinarith [hb2]
    have stepC : ((G8:ℤ):ℝ)*(((md Wloi Wloi:ℤ):ℝ)*((Wloi:ℝ)))*SR
        ≤ ((G8:ℤ):ℝ)*(((Wloi:ℝ))*((Wloi:ℝ)))*((Wloi:ℝ)) := by
      have hc := mul_le_mul_of_nonneg_right hm1 hWloi0R
      have hc2 := mul_le_mul_of_nonneg_left hc hG8nn
      nlinarith [hc2]
    have stepD : ((G8:ℤ):ℝ)*(((Wloi:ℝ))*((Wloi:ℝ)))*((Wloi:ℝ))
        = 8*r*(Wloi:ℝ)^3*SR := by rw [hG8]; ring
    linarith [e1, stepA, stepB, stepC, stepD]
  -- ===== assembly =====
  have hDENpos : 0 < DEN := by rw [hDEN]; positivity
  have hN : SR*NUM ≤ (SNUMi:ℝ) := by
    rw [hNUM, hSNUMi]; push_cast
    linarith [hT1, hT2, hT3]
  have hNUM0 : 0 ≤ NUM := by
    rw [hNUM]
    have hB1nn : 0 ≤ B1 := by rw [hB1d]; positivity
    have hC3nn : 0 ≤ C3 := by rw [hC3d]; positivity
    nlinarith [hA1nn, hB1nn, hC3nn, hW0, sq_nonneg W]
  have hSNUM0 : 0 ≤ (SNUMi:ℝ) := le_trans (mul_nonneg hSRpos.le hNUM0) hN
  have hdvu0 : 0 ≤ ((dvu SNUMi SDDi:ℤ):ℝ) := by
    have h := dvu_ge_mul (a := SNUMi) (b := SDDi) hdd
    have hpos : 0 < ((SDDi:ℤ):ℝ) := by exact_mod_cast hdd
    have : 0 ≤ ((dvu SNUMi SDDi:ℤ):ℝ) * ((SDDi:ℤ):ℝ) := by nlinarith [h, hSNUM0, hSRpos]
    exact nonneg_of_mul_nonneg_left this hpos
  have h2 : (SNUMi:ℝ) ≤ ((dvu SNUMi SDDi:ℤ):ℝ)*((SDDi:ℤ):ℝ)/SR := by
    rw [le_div_iff₀ hSRpos]
    have h := dvu_ge_mul (a := SNUMi) (b := SDDi) hdd
    linarith
  have hSDD' : ((SDDi:ℤ):ℝ) ≤ DEN*SR := by
    rw [hDEN]; linarith [hSDD]
  have h3 : ((dvu SNUMi SDDi:ℤ):ℝ)*((SDDi:ℤ):ℝ)/SR ≤ ((dvu SNUMi SDDi:ℤ):ℝ)*DEN := by
    rw [div_le_iff₀ hSRpos]
    nlinarith [hSDD', hdvu0]
  rw [div_le_div_iff₀ hDENpos hSRpos]
  linarith [hN, h2, h3]

end Work.Cert.ACSlit
