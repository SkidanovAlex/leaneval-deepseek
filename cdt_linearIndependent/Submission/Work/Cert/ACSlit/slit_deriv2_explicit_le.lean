import Mathlib
import Submission.Work.Cert.ACSlit.M2eSpec
import Submission.Work.Cert.ACSlit.Shadow
import Submission.Work.Cert.ACSlit.sQpD_bound
import Submission.Work.Cert.ACSlit.sQhi_bound
import Submission.Work.Cert.ACSlit.sQlo_bound
import Submission.Work.Cert.ACSlit.sQlo_sqrt_bound
import Submission.Work.ANum3.slit_crude_bound
import Submission.Work.Cert.ACBall.Basic
import Submission.Work.Cert.ACBall.binv_sound
import Submission.Work.APsi.defs

namespace Work.Cert.ACSlit

open Work.Cert Work.Cert.ACBall

/-! ## Elementary ball lemmas

`BallMem a z` says `‖z - c(a)‖ ≤ a.r/S`; these two lemmas turn a square bound on the mantissa
centre into a bound on `‖z‖` (upper and lower), using `‖c(a)‖ ≤ m/S ⟺ ‖c(a)‖² ≤ (m/S)²`. -/

/-- `m/S ≤ ‖cx x y‖` from `m² ≤ x² + y²` (the reverse direction of `norm_cx_le_of_sq_le`). -/
lemma le_norm_cx_of_sq_le (x y m : ℤ) (hm : 0 ≤ m) (h : m * m ≤ x * x + y * y) :
    (m : ℝ) / (S : ℝ) ≤ ‖cx x y‖ := by
  have hmR : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hcast : (m : ℝ) ^ 2 ≤ (x : ℝ) ^ 2 + (y : ℝ) ^ 2 := by
    have h' : ((m * m : ℤ) : ℝ) ≤ ((x * x + y * y : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h' ⊢
    linarith
  have h2 : ((m : ℝ) / (S : ℝ)) ^ 2 ≤ ‖cx x y‖ ^ 2 := by
    rw [norm_cx_sq, div_pow]
    exact div_le_div_of_nonneg_right hcast (sq_nonneg _)
  calc (m : ℝ) / (S : ℝ) = Real.sqrt (((m : ℝ) / (S : ℝ)) ^ 2) :=
        (Real.sqrt_sq (div_nonneg hmR S_posR.le)).symm
    _ ≤ Real.sqrt (‖cx x y‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖cx x y‖ := Real.sqrt_sq (norm_nonneg _)

/-- `‖z‖ ≤ (m + a.r)/S` if `z ∈ a` and the mantissa centre of `a` is bounded by `m/S`. -/
lemma norm_le_of_ballMem_hi {a : Bl} {z : ℂ} {m : ℤ} (h : BallMem a z) (hm : 0 ≤ m)
    (hsq : a.x * a.x + a.y * a.y ≤ m * m) : ‖z‖ ≤ (((m + a.r : ℤ)) : ℝ) / (S : ℝ) := by
  unfold BallMem at h
  have h1 : ‖z‖ ≤ ‖z - cx a.x a.y‖ + ‖cx a.x a.y‖ := by
    calc ‖z‖ = ‖(z - cx a.x a.y) + cx a.x a.y‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - cx a.x a.y‖ + ‖cx a.x a.y‖ := norm_add_le _ _
  have h2 := norm_cx_le_of_sq_le a.x a.y m hm hsq
  have h3 : (((m + a.r : ℤ)) : ℝ) / (S : ℝ)
      = (m : ℝ) / (S : ℝ) + (a.r : ℝ) / (S : ℝ) := by
    push_cast; ring
  rw [h3]
  linarith

/-- `(m - a.r)/S ≤ ‖z‖` if `z ∈ a` and `m/S` is a lower bound for the mantissa centre of `a`. -/
lemma le_norm_of_ballMem_lo {a : Bl} {z : ℂ} {m : ℤ} (h : BallMem a z) (hm : 0 ≤ m)
    (hsq : m * m ≤ a.x * a.x + a.y * a.y) : (((m - a.r : ℤ)) : ℝ) / (S : ℝ) ≤ ‖z‖ := by
  unfold BallMem at h
  have h2 : (m : ℝ) / (S : ℝ) ≤ ‖cx a.x a.y‖ := le_norm_cx_of_sq_le a.x a.y m hm hsq
  have h3 : ‖cx a.x a.y‖ ≤ ‖z - cx a.x a.y‖ + ‖z‖ := by
    calc ‖cx a.x a.y‖ = ‖z - (z - cx a.x a.y)‖ := by ring_nf
      _ ≤ ‖z‖ + ‖z - cx a.x a.y‖ := norm_sub_le _ _
      _ = ‖z - cx a.x a.y‖ + ‖z‖ := by ring
  have h4 : (((m - a.r : ℤ)) : ℝ) / (S : ℝ)
      = (m : ℝ) / (S : ℝ) - (a.r : ℝ) / (S : ℝ) := by
    push_cast; ring
  rw [h4]
  linarith

/-- `cx (cr - S) ci = cIn st - 1`. -/
lemma cx_sub_one_of_S (st : St) : cx (st.cr - S) st.ci = cIn st - 1 := by
  have h1 : cx S 0 = (1 : ℂ) := by
    rw [cx_zero_y, div_self (ne_of_gt S_posR), Complex.ofReal_one]
  have h2 : cx (st.cr - S) st.ci = cx (st.cr - S) (st.ci - 0) := by rw [Int.sub_zero]
  rw [h2, ← cx_sub st.cr st.ci S 0, h1]
  simp only [cIn]

/-- `slitQ r z` written in the real-coefficient form used by the crude bound. -/
lemma slitQ_poly (r : ℝ) (z : ℂ) :
    Work.APsi.slitQ r z
      = (1 + r) ^ 2 * z ^ 2 - 2 * (1 - 6 * r + r ^ 2) * z + (1 + r) ^ 2 := by
  simp only [Work.APsi.slitQ]
  push_cast
  ring

/-- `a ≤ √b` from `a² ≤ b` and `0 ≤ a`. -/
lemma le_sqrt_of_sq_le {a b : ℝ} (ha : 0 ≤ a) (h : a ^ 2 ≤ b) : a ≤ Real.sqrt b := by
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt b := Real.sqrt_le_sqrt h

theorem slit_deriv2_explicit_le (A B2 E C1 G8 A2 ror roi : ℤ) (st : Work.Cert.St) (w : Work.Cert.SlitW)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hA : (A : ℝ) = (Work.Cert.S : ℝ) * (1 + r) ^ 2)
    (hB2 : (B2 : ℝ) = (Work.Cert.S : ℝ) * (2 * (1 - 6 * r + r ^ 2)))
    (hE : (E : ℝ) = (Work.Cert.S : ℝ) * (2 * (r - 1) ^ 2))
    (hC1 : (C1 : ℝ) = (Work.Cert.S : ℝ) * (1 + r))
    (hG8 : (G8 : ℝ) = (Work.Cert.S : ℝ) * (8 * r))
    (hA2 : (A2 : ℝ) = (Work.Cert.S : ℝ) * (2 * (1 + r) ^ 2))
    (hokB : Work.Cert.ACSlit.sokB A B2 E C1 G8 A2 ror roi st w = true)
    (hokM : Work.Cert.ACSlit.sokM A B2 E C1 G8 A2 ror roi st w = true)
    (hokW : Work.Cert.ACSlit.sokW A B2 E C1 G8 A2 ror roi st w = true)
    (hwhi : Work.Cert.ACSlit.swhi A B2 E C1 G8 A2 ror roi st w < Work.Cert.S)
    (hrho : 0 ≤ st.rho)
    (huse : Work.Cert.ACSlit.suseE A B2 E C1 G8 A2 ror roi st w = true)
    (hQ : Work.Cert.ACBall.BallMem (Work.Cert.ACSlit.sQ A B2 E C1 G8 A2 ror roi st w)
        (Work.APsi.slitQ r (Work.Cert.ACSlit.cIn st)))
    (hQp : Work.Cert.ACBall.BallMem (Work.Cert.ACSlit.sQp A B2 E C1 G8 A2 ror roi st w)
        (2 * (1 + (r : ℂ)) ^ 2 * Work.Cert.ACSlit.cIn st
          - 2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2)))
    {u : ℂ} (hu : ‖u - Work.Cert.ACSlit.cIn st‖ ≤ (st.rho : ℝ) / (Work.Cert.S : ℝ)) :
    ‖deriv (deriv (Submission.CDTPlan.slit r)) u‖
      ≤ Work.ANum3.crude r ((1 + r) ^ 2) (2 * (r - 1) ^ 2) (1 + r)
          ((Work.Cert.ACSlit.swhi A B2 E C1 G8 A2 ror roi st w : ℝ) / (Work.Cert.S : ℝ))
          ((Work.Cert.ACSlit.swm1 A B2 E C1 G8 A2 ror roi st w : ℝ) / (Work.Cert.S : ℝ))
          ((Work.Cert.ACSlit.swlo A B2 E C1 G8 A2 ror roi st w : ℝ) / (Work.Cert.S : ℝ))
          ((Work.Cert.ACSlit.sQpD A B2 E C1 G8 A2 ror roi st w : ℝ) / (Work.Cert.S : ℝ))
          ((Work.Cert.ACSlit.sQhi A B2 E C1 G8 A2 ror roi st w : ℝ) / (Work.Cert.S : ℝ))
          ((w.sL : ℝ) / (Work.Cert.S : ℝ)) ((w.sH : ℝ) / (Work.Cert.S : ℝ)) := by
  have hS : (0 : ℝ) < (Work.Cert.S : ℝ) := S_posR
  have hρ : 0 ≤ (st.rho : ℝ) / (Work.Cert.S : ℝ) :=
    div_nonneg (by exact_mod_cast hrho) hS.le
  have hrhoR : (0 : ℝ) ≤ (st.rho : ℝ) := by exact_mod_cast hrho
  -- ## the flags, exposed
  obtain ⟨_hD0, _hfpD, hcU0, hcr2, hqU0, hqU2, hqL0, hqL2, hqpU0, hqpU2, hm1U0, hm1U2⟩ :=
    sokM_spec A B2 E C1 G8 A2 ror roi st w hokM
  obtain ⟨_hsr0, _hQr0, _hdenr0, _hL1lt, _hL1sq, _hssr0, _hLslt, _hLssq, hcL0, hcL2⟩ :=
    sokB_spec A B2 E C1 G8 A2 ror roi st w hokB
  obtain ⟨hQlopos, hswlopos⟩ := suseE_spec A B2 E C1 G8 A2 ror roi st w huse
  obtain ⟨hsL0, hsL2, hsH0, hsH2⟩ := sokW_spec A B2 E C1 G8 A2 ror roi st w hokW huse
  have hwhi' : w.cU + st.rho + 1 < Work.Cert.S := by simpa only [swhi] using hwhi
  -- ## geometric data for the centre `cIn st`
  have hcU : ‖cIn st‖ ≤ ((w.cU : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
    simpa only [cIn] using norm_cx_le_of_sq_le st.cr st.ci w.cU hcU0 hcr2
  have hcL : ((w.cL : ℤ) : ℝ) / (Work.Cert.S : ℝ) ≤ ‖cIn st‖ := by
    simpa only [cIn] using le_norm_cx_of_sq_le st.cr st.ci w.cL (le_of_lt hcL0) hcL2
  have hm1U : ‖cIn st - 1‖ ≤ ((w.m1U : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
    have h := norm_cx_le_of_sq_le (st.cr - Work.Cert.S) st.ci w.m1U hm1U0 hm1U2
    rwa [cx_sub_one_of_S st] at h
  -- ## real norms of `Q(c)`, `Q'(c)` from the ball data
  have hQhi_b : ‖Work.APsi.slitQ r (cIn st)‖
      ≤ (((w.qU + (sQ A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (Work.Cert.S : ℝ) :=
    norm_le_of_ballMem_hi hQ hqU0 hqU2
  have hQlo_b : (((w.qL - (sQ A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (Work.Cert.S : ℝ)
      ≤ ‖Work.APsi.slitQ r (cIn st)‖ :=
    le_norm_of_ballMem_lo hQ hqL0 hqL2
  have hQp_b : ‖2 * (1 + (r : ℂ)) ^ 2 * cIn st - 2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2)‖
      ≤ (((w.qpU + (sQp A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (Work.Cert.S : ℝ) :=
    norm_le_of_ballMem_hi hQp hqpU0 hqpU2
  have hQpoly : ‖Work.APsi.slitQ r (cIn st)‖
      = ‖(1 + r) ^ 2 * (cIn st) ^ 2 - 2 * (1 - 6 * r + r ^ 2) * (cIn st) + (1 + r) ^ 2‖ := by
    congr 1
    exact slitQ_poly r (cIn st)
  have hQp_eq : (2 * (1 + (r : ℂ)) ^ 2 * cIn st - 2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2))
      = (2 * (1 + r) ^ 2 * cIn st - 2 * (1 - 6 * r + r ^ 2)) := by
    push_cast
    ring
  have hQp_real : ‖2 * (1 + r) ^ 2 * cIn st - 2 * (1 - 6 * r + r ^ 2)‖
      ≤ (((w.qpU + (sQp A B2 E C1 G8 A2 ror roi st w).r : ℤ)) : ℝ) / (Work.Cert.S : ℝ) := by
    simpa only [hQp_eq] using hQp_b
  -- ## the four arithmetic inputs to the crude bound
  have hQpCrude : ‖2 * (1 + r) ^ 2 * cIn st - 2 * (1 - 6 * r + r ^ 2)‖
      + ((st.rho : ℝ) / (Work.Cert.S : ℝ)) * (2 * (1 + r) ^ 2)
      ≤ (((sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ) :=
    sQpD_bound A B2 E C1 G8 A2 ror roi st w hA2 hQp_real
  have hQhiCrude :
      ‖(1 + r) ^ 2 * (cIn st) ^ 2 - 2 * (1 - 6 * r + r ^ 2) * (cIn st) + (1 + r) ^ 2‖
      + ((st.rho : ℝ) / (Work.Cert.S : ℝ))
        * ((((sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ))
      ≤ (((sQhi A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ) := by
    have h := sQhi_bound (r := r) A B2 E C1 G8 A2 ror roi st w hQhi_b
    have heq : ((st.rho : ℝ) / (Work.Cert.S : ℝ))
          * (((sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ)
        = ((st.rho : ℝ) / (Work.Cert.S : ℝ))
          * ((((sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ)) := by
      ring
    rw [heq] at h
    rwa [← hQpoly]
  have hQloCrude : ((st.rho : ℝ) / (Work.Cert.S : ℝ))
      * (‖2 * (1 + r) ^ 2 * cIn st - 2 * (1 - 6 * r + r ^ 2)‖
        + ((st.rho : ℝ) / (Work.Cert.S : ℝ)) * (2 * (1 + r) ^ 2))
      < ‖(1 + r) ^ 2 * (cIn st) ^ 2 - 2 * (1 - 6 * r + r ^ 2) * (cIn st) + (1 + r) ^ 2‖ := by
    rw [← hQpoly]
    exact sQlo_bound A B2 E C1 G8 A2 ror roi st w hrhoR hQlopos hQlo_b hQpCrude
  have hSloCrude : ((w.sL : ℤ) : ℝ) / (Work.Cert.S : ℝ)
      ≤ Real.sqrt (‖(1 + r) ^ 2 * (cIn st) ^ 2 - 2 * (1 - 6 * r + r ^ 2) * (cIn st)
            + (1 + r) ^ 2‖
          - ((st.rho : ℝ) / (Work.Cert.S : ℝ))
            * ((((sQpD A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ))) := by
    rw [← hQpoly]
    exact sQlo_sqrt_bound (r := r) A B2 E C1 G8 A2 ror roi st w hQlopos hsL0 hsL2 hQlo_b
  have hShiCrude : Real.sqrt ((((sQhi A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ)
        / (Work.Cert.S : ℝ)) ≤ ((w.sH : ℤ) : ℝ) / (Work.Cert.S : ℝ) := by
    have hsH0R : (0 : ℝ) ≤ (w.sH : ℝ) := by exact_mod_cast hsH0
    have hsq : ((((sQhi A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ))
        ≤ ((((w.sH : ℤ)) : ℝ) / (Work.Cert.S : ℝ)) ^ 2 := by
      have h2 : (((sQhi A B2 E C1 G8 A2 ror roi st w * Work.Cert.S : ℤ)) : ℝ)
          ≤ ((w.sH * w.sH : ℤ) : ℝ) := by exact_mod_cast hsH2
      push_cast at h2
      rw [div_pow, div_le_div_iff₀ hS (pow_pos hS 2)]
      nlinarith [h2]
    calc Real.sqrt ((((sQhi A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ))
        ≤ Real.sqrt (((((w.sH : ℤ)) : ℝ) / (Work.Cert.S : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ((w.sH : ℤ) : ℝ) / (Work.Cert.S : ℝ) := Real.sqrt_sq (div_nonneg hsH0R hS.le)
  -- ## the remaining disc data
  have hdisc : ‖cIn st‖ + (st.rho : ℝ) / (Work.Cert.S : ℝ) < 1 := by
    have h2 : ((w.cU : ℤ) : ℝ) + (st.rho : ℝ) < (Work.Cert.S : ℝ) := by
      have hZ : w.cU + st.rho < Work.Cert.S := by omega
      have h3 : (((w.cU + st.rho : ℤ)) : ℝ) < (Work.Cert.S : ℝ) := by exact_mod_cast hZ
      push_cast at h3
      linarith
    have h3 : ((w.cU : ℤ) : ℝ) / (Work.Cert.S : ℝ) + (st.rho : ℝ) / (Work.Cert.S : ℝ) < 1 := by
      rw [← add_div]
      exact (div_lt_one hS).mpr h2
    linarith [hcU, h3]
  have hwloρ : (st.rho : ℝ) / (Work.Cert.S : ℝ) < ‖cIn st‖ := by
    have hlt : st.rho < w.cL := by
      simp only [swlo] at hswlopos
      omega
    have hltR : (st.rho : ℝ) < (w.cL : ℝ) := by exact_mod_cast hlt
    have h1 : (st.rho : ℝ) / (Work.Cert.S : ℝ) < (w.cL : ℝ) / (Work.Cert.S : ℝ) :=
      div_lt_div_of_pos_right hltR hS
    linarith [hcL, h1]
  have hW : ‖cIn st‖ + (st.rho : ℝ) / (Work.Cert.S : ℝ)
      ≤ (((swhi A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ) := by
    have h1 : (((swhi A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ)
        = ((w.cU : ℤ) : ℝ) + (st.rho : ℝ) + 1 := by
      rw [swhi]; push_cast; ring
    have h2 : ((((w.cU : ℤ) : ℝ) + (st.rho : ℝ) + 1) / (Work.Cert.S : ℝ))
        = ((w.cU : ℤ) : ℝ) / (Work.Cert.S : ℝ) + (st.rho : ℝ) / (Work.Cert.S : ℝ)
          + 1 / (Work.Cert.S : ℝ) := by
      ring
    rw [h1, h2]
    have h3 : (0 : ℝ) < 1 / (Work.Cert.S : ℝ) := by positivity
    linarith [hcU, h3]
  have hwm1 : ‖cIn st - 1‖ + (st.rho : ℝ) / (Work.Cert.S : ℝ)
      ≤ (((swm1 A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ) := by
    have h1 : (((swm1 A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ)
        = ((w.m1U : ℤ) : ℝ) + (st.rho : ℝ) + 1 := by
      rw [swm1]; push_cast; ring
    have h2 : ((((w.m1U : ℤ) : ℝ) + (st.rho : ℝ) + 1) / (Work.Cert.S : ℝ))
        = ((w.m1U : ℤ) : ℝ) / (Work.Cert.S : ℝ) + (st.rho : ℝ) / (Work.Cert.S : ℝ)
          + 1 / (Work.Cert.S : ℝ) := by
      ring
    rw [h1, h2]
    have h3 : (0 : ℝ) < 1 / (Work.Cert.S : ℝ) := by positivity
    linarith [hm1U, h3]
  have hWlo : (((swlo A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ)
      ≤ ‖cIn st‖ - (st.rho : ℝ) / (Work.Cert.S : ℝ) := by
    have h1 : (((swlo A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ)
        = ((w.cL : ℤ) : ℝ) - (st.rho : ℝ) - 1 := by
      rw [swlo]; push_cast; ring
    have h2 : ((((w.cL : ℤ) : ℝ) - (st.rho : ℝ) - 1) / (Work.Cert.S : ℝ))
        = ((w.cL : ℤ) : ℝ) / (Work.Cert.S : ℝ) - (st.rho : ℝ) / (Work.Cert.S : ℝ)
          - 1 / (Work.Cert.S : ℝ) := by
      ring
    rw [h1, h2]
    have h3 : (0 : ℝ) < 1 / (Work.Cert.S : ℝ) := by positivity
    linarith [hcL, h3]
  have hWlo_pos : 0 < (((swlo A B2 E C1 G8 A2 ror roi st w : ℤ)) : ℝ) / (Work.Cert.S : ℝ) :=
    div_pos (by exact_mod_cast hswlopos) hS
  have hSlo_pos : 0 < ((w.sL : ℤ) : ℝ) / (Work.Cert.S : ℝ) :=
    div_pos (by exact_mod_cast hsL0) hS
  -- ## the crude bound, and its identification with `crude`
  have hcrude := Work.ANum3.slit_crude_bound (r := r) hr0 hr1 (c := cIn st) (w := u)
    (ρ := (st.rho : ℝ) / (Work.Cert.S : ℝ)) hρ hu hdisc hwloρ hQloCrude
    (le_refl ((1 + r) ^ 2)) (le_refl |2 * (1 - 6 * r + r ^ 2)|) (le_refl (2 * (r - 1) ^ 2))
    (le_refl (1 + r)) hW hwm1 hWlo hWlo_pos hQpCrude hQhiCrude hSlo_pos hSloCrude hShiCrude
  unfold Work.ANum3.crude
  exact hcrude

end Work.Cert.ACSlit
