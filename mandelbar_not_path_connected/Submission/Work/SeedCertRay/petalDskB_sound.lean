import Mathlib
import Submission.Work.SeedCertRay.Q
import Submission.Work.SeedCertRay.Petal_iff_norm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

open LeanEval.ComplexAnalysis

/-! ## Preliminaries: the mantissa layer in `ℝ` -/

/-- `iabs` is the integer absolute value: in `ℝ` it is `|·|`. -/
lemma iabs_cast (x : ℤ) : ((iabs x : ℤ) : ℝ) = |(x:ℝ)| := by
  simp only [iabs, Int.cast_max, Int.cast_neg]
  rw [abs_eq_max_neg]

/-- The mantissa decoding `Q` in `ℝ`: `Q m = m / 2 ^ 40`. -/
lemma Q_cast (m : ℤ) : ((Q m : ℚ) : ℝ) = (m:ℝ)/(MSZ:ℝ) := by
  simp only [Q, MS]
  push_cast
  norm_num [MSZ]

lemma MSZ_pos_real : (0:ℝ) < (MSZ:ℝ) := by norm_num [MSZ]

lemma RRM_div_MSZ : (RRM:ℝ)/(MSZ:ℝ) = 4 := by
  have h : (RRM:ℝ) = 4*(MSZ:ℝ) := by norm_num [RRM, MSZ]
  have hS : (MSZ:ℝ) ≠ 0 := ne_of_gt MSZ_pos_real
  rw [h, mul_div_assoc, div_self hS, mul_one]

lemma iabs_nonneg (x : ℤ) : 0 ≤ iabs x := by
  rw [iabs]
  by_cases h : 0 ≤ x
  · exact le_trans h (le_max_left _ _)
  · have : 0 ≤ -x := by omega
    exact le_trans this (le_max_right _ _)

/-! ## Decoding the certificate `petalDskB` -/

/-- **The `petalDskB` certificate, decoded.**  The integer inequality emitted for one disk
implies, for the rescaled quantities `s = U/MS²`, `t = V/MS²`, `d = W/MS²`, the single real
inequality `|2·RR·s - 1| + 2·RR·(t + d) < 1` (with `RR = RRM/MS = 4` this is
`|8s - 1| + 8(t + d) < 1`). -/
lemma cert_real (U V W : ℤ)
    (h : iabs (2*RRM*U - MSZ*MSZ*MSZ) + 2*RRM*(V + W) < MSZ*MSZ*MSZ) :
    |2 * ((RRM:ℝ)/(MSZ:ℝ)) * ((U:ℝ)/(MSZ:ℝ)^2) - 1|
      + 2 * ((RRM:ℝ)/(MSZ:ℝ)) * ((V:ℝ)/(MSZ:ℝ)^2 + (W:ℝ)/(MSZ:ℝ)^2) < 1 := by
  have h' : iabs (2*RRM*U - MSZ^3) + 2*RRM*(V + W) < MSZ^3 := by
    simpa only [pow_three, mul_assoc] using h
  have hS : (0:ℝ) < (MSZ:ℝ) := MSZ_pos_real
  have hSne : (MSZ:ℝ) ≠ 0 := ne_of_gt hS
  have hS3 : (0:ℝ) < (MSZ:ℝ)^3 := by positivity
  have hcast : |2*(RRM:ℝ)*(U:ℝ) - (MSZ:ℝ)^3| + 2*(RRM:ℝ)*((V:ℝ)+(W:ℝ)) < (MSZ:ℝ)^3 := by
    have hh : ((iabs (2*RRM*U - MSZ^3) : ℤ) : ℝ) + ((2*RRM*(V+W) : ℤ) : ℝ) < ((MSZ^3 : ℤ) : ℝ) := by
      exact_mod_cast h'
    rw [iabs_cast] at hh
    push_cast at hh
    exact hh
  have e1 : |2 * ((RRM:ℝ)/(MSZ:ℝ)) * ((U:ℝ)/(MSZ:ℝ)^2) - 1|
      = |2*(RRM:ℝ)*(U:ℝ) - (MSZ:ℝ)^3| / (MSZ:ℝ)^3 := by
    have hB : (2*(RRM:ℝ)*(U:ℝ) - (MSZ:ℝ)^3)
        = (2 * ((RRM:ℝ)/(MSZ:ℝ)) * ((U:ℝ)/(MSZ:ℝ)^2) - 1) * (MSZ:ℝ)^3 := by
      field_simp
    rw [hB, abs_mul, abs_of_pos hS3, mul_div_assoc, div_self (ne_of_gt hS3), mul_one]
  have e2 : 2 * ((RRM:ℝ)/(MSZ:ℝ)) * ((V:ℝ)/(MSZ:ℝ)^2 + (W:ℝ)/(MSZ:ℝ)^2)
      = 2*(RRM:ℝ)*((V:ℝ)+(W:ℝ)) / (MSZ:ℝ)^3 := by
    rw [eq_div_iff (ne_of_gt hS3)]
    field_simp
  rw [e1, e2, ← add_div, div_lt_one hS3]
  exact hcast

/-- **Key real algebra.**  With `t ≥ 0`, `t + d < s` and `s + t + d < 1/4`, the disk of radius
`d` about `w₀` with `Re w₀ = s`, `|Im w₀| ≤ t` lies inside the open disk of radius `1/8` about
`1/8`: `(s - 1/8)² + t² < (1/8 - d)²`, and `1/8 - d > 0`. -/
lemma cert_algebra {s t d : ℝ} (ht : 0 ≤ t) (h1 : t + d < s) (h2 : s + t + d < 1/4) :
    (s - 1/8)^2 + t^2 < (1/8 - d)^2 ∧ 0 < 1/8 - d := by
  have hsd : 0 < s - d := by linarith
  have h4 : 4*(s+d) - 1 < -4*t := by linarith
  have hA : (s-d)*(4*(s+d)-1) < (s-d)*(-4*t) := mul_lt_mul_of_pos_left h4 hsd
  have hkey : 4*(s^2 + t^2 - d^2) < s - d := by
    have hid : 4*(s^2 + t^2 - d^2) - (s - d) = (s-d)*(4*(s+d)-1) + 4*t^2 := by ring
    rw [← sub_neg, hid]
    nlinarith [hA, ht, h1]
  constructor
  · have hid2 : (1/8 - d)^2 - ((s - 1/8)^2 + t^2) = (s-d)/4 - (s^2 + t^2 - d^2) := by ring
    linarith [hid2, hkey]
  · linarith [h1, h2, ht]

/-- **The geometric estimate.**  If `z` is within `qBr` of `p`, `z₁` is within `qETA1` (in each
coordinate) of `z₀`, and `A` is within `qETAA` (in each coordinate) of `a`, then
`A (z - z₁)` is within the indicated box-parallelepiped error of `a (p - z₀)`. -/
lemma norm_mul_sub_le (z z₁ A p z0 a : ℂ) (qBr qETA1 qETAA : ℝ)
    (hzp : ‖z - p‖ ≤ qBr)
    (hz1 : |z₁.re - z0.re| ≤ qETA1) (hz1' : |z₁.im - z0.im| ≤ qETA1)
    (hA : |A.re - a.re| ≤ qETAA) (hA' : |A.im - a.im| ≤ qETAA) :
    ‖A*(z - z₁) - a*(p - z0)‖
      ≤ 2*qETAA*(|p.re - z0.re| + |p.im - z0.im|) + (|a.re| + |a.im| + 2*qETAA)*(qBr + 2*qETA1) := by
  have hqE : 0 ≤ qETAA := le_trans (abs_nonneg (A.re - a.re)) hA
  have hq1 : 0 ≤ qETA1 := le_trans (abs_nonneg (z₁.re - z0.re)) hz1
  have hqB : 0 ≤ qBr := le_trans (norm_nonneg (z - p)) hzp
  have hAa : 0 ≤ |a.re| + |a.im| := by positivity
  have hAe : ‖A - a‖ ≤ 2*qETAA := by
    calc ‖A - a‖ ≤ |(A - a).re| + |(A - a).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |A.re - a.re| + |A.im - a.im| := by simp only [Complex.sub_re, Complex.sub_im]
      _ ≤ 2*qETAA := by linarith
  have hae : ‖a‖ ≤ |a.re| + |a.im| := Complex.norm_le_abs_re_add_abs_im a
  have hz1e : ‖z₁ - z0‖ ≤ 2*qETA1 := by
    calc ‖z₁ - z0‖ ≤ |(z₁ - z0).re| + |(z₁ - z0).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |z₁.re - z0.re| + |z₁.im - z0.im| := by simp only [Complex.sub_re, Complex.sub_im]
      _ ≤ 2*qETA1 := by linarith
  have hpe : ‖p - z0‖ ≤ |p.re - z0.re| + |p.im - z0.im| := by
    calc ‖p - z0‖ ≤ |(p - z0).re| + |(p - z0).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |p.re - z0.re| + |p.im - z0.im| := by simp only [Complex.sub_re, Complex.sub_im]
  have hze : ‖(z - z₁) - (p - z0)‖ ≤ qBr + 2*qETA1 := by
    have hd : (z - z₁) - (p - z0) = (z - p) - (z₁ - z0) := by ring
    calc ‖(z - z₁) - (p - z0)‖ = ‖(z - p) - (z₁ - z0)‖ := by rw [hd]
      _ ≤ ‖z - p‖ + ‖z₁ - z0‖ := norm_sub_le (z - p) (z₁ - z0)
      _ ≤ qBr + 2*qETA1 := by linarith
  have hdecomp : A*(z - z₁) - a*(p - z0) = (A - a)*(z - z₁) + a*((z - z₁) - (p - z0)) := by ring
  have hzz1 : ‖z - z₁‖ ≤ ‖p - z0‖ + ‖(z - z₁) - (p - z0)‖ := by
    have hd : z - z₁ = (p - z0) + ((z - z₁) - (p - z0)) := by ring
    calc ‖z - z₁‖ = ‖(p - z0) + ((z - z₁) - (p - z0))‖ := by conv_lhs => rw [hd]
      _ ≤ ‖p - z0‖ + ‖(z - z₁) - (p - z0)‖ := norm_add_le (p - z0) ((z - z₁) - (p - z0))
  calc ‖A*(z - z₁) - a*(p - z0)‖
      = ‖(A - a)*(z - z₁) + a*((z - z₁) - (p - z0))‖ := by rw [hdecomp]
    _ ≤ ‖(A - a)*(z - z₁)‖ + ‖a*((z - z₁) - (p - z0))‖ := norm_add_le _ _
    _ = ‖A - a‖*‖z - z₁‖ + ‖a‖*‖(z - z₁) - (p - z0)‖ := by rw [norm_mul, norm_mul]
    _ ≤ 2*qETAA*(‖p - z0‖ + ‖(z - z₁) - (p - z0)‖) + (|a.re| + |a.im|)*(qBr + 2*qETA1) := by
        have h1 : ‖A - a‖*‖z - z₁‖ ≤ 2*qETAA*(‖p - z0‖ + ‖(z - z₁) - (p - z0)‖) :=
          mul_le_mul hAe hzz1 (norm_nonneg _) (by linarith)
        have h2 : ‖a‖*‖(z - z₁) - (p - z0)‖ ≤ (|a.re| + |a.im|)*(qBr + 2*qETA1) :=
          mul_le_mul hae hze (norm_nonneg _) (by linarith)
        linarith
    _ ≤ 2*qETAA*(( |p.re - z0.re| + |p.im - z0.im| ) + (qBr + 2*qETA1)) + (|a.re| + |a.im|)*(qBr + 2*qETA1) := by
        have h4 : ‖p - z0‖ + ‖(z - z₁) - (p - z0)‖ ≤ (|p.re - z0.re| + |p.im - z0.im|) + (qBr + 2*qETA1) := by linarith
        have h5 : 2*qETAA*(‖p - z0‖ + ‖(z - z₁) - (p - z0)‖)
            ≤ 2*qETAA*((|p.re - z0.re| + |p.im - z0.im|) + (qBr + 2*qETA1)) :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
        linarith
    _ = 2*qETAA*(|p.re - z0.re| + |p.im - z0.im|) + (|a.re| + |a.im| + 2*qETAA)*(qBr + 2*qETA1) := by ring

/-- **The `Q`-form of the certificate radius.**  The integer expression `W` of `petalDskB`,
rescaled, is exactly the bound produced by `norm_mul_sub_le` at the disk centre of
`⟨Q Bx, Q By, Q Br⟩`, the point `z₀` of `Zb` and the coefficient `A` of `Ab`. -/
lemma d_ident (Bx By Br : ℤ) :
    (((2*ETAA*(iabs (Bx - ZCX) + iabs (By - ZCY))
        + (iabs ACX + iabs ACY + 2*ETAA)*(Br + 2*ETA1)) : ℤ) : ℝ)/(MSZ:ℝ)^2
    = 2*(((Q ETAA:ℚ):ℝ))*((|((Q Bx:ℚ):ℝ) - ((Q ZCX:ℚ):ℝ)|) + |((Q By:ℚ):ℝ) - ((Q ZCY:ℚ):ℝ)|)
      + ((|((Q ACX:ℚ):ℝ)| + |((Q ACY:ℚ):ℝ)|) + 2*((Q ETAA:ℚ):ℝ))*(((Q Br:ℚ):ℝ) + 2*((Q ETA1:ℚ):ℝ)) := by
  have hS : (0:ℝ) < (MSZ:ℝ) := MSZ_pos_real
  have e1 : |((Q Bx:ℚ):ℝ) - ((Q ZCX:ℚ):ℝ)| = |((Bx - ZCX:ℤ):ℝ)|/(MSZ:ℝ) := by
    rw [Q_cast, Q_cast, ← sub_div, abs_div, abs_of_pos hS]; congr 1; push_cast; ring
  have e2 : |((Q By:ℚ):ℝ) - ((Q ZCY:ℚ):ℝ)| = |((By - ZCY:ℤ):ℝ)|/(MSZ:ℝ) := by
    rw [Q_cast, Q_cast, ← sub_div, abs_div, abs_of_pos hS]; congr 1; push_cast; ring
  have e3 : |((Q ACX:ℚ):ℝ)| = |((ACX:ℤ):ℝ)|/(MSZ:ℝ) := by
    rw [Q_cast, abs_div, abs_of_pos hS]
  have e4 : |((Q ACY:ℚ):ℝ)| = |((ACY:ℤ):ℝ)|/(MSZ:ℝ) := by
    rw [Q_cast, abs_div, abs_of_pos hS]
  rw [e1, e2, e3, e4]
  push_cast
  simp only [iabs_cast, Q_cast]
  push_cast
  field_simp

theorem petalDskB_sound (Bx By Br : ℤ) (h : Work.SeedCertRay.petalDskB Bx By Br Work.SeedCertRay.ZCX Work.SeedCertRay.ZCY Work.SeedCertRay.ETA1 Work.SeedCertRay.ACX Work.SeedCertRay.ACY Work.SeedCertRay.ETAA Work.SeedCertRay.RRM = true) :
    ∀ z : ℂ, (⟨Work.SeedCertRay.Q Bx, Work.SeedCertRay.Q By, Work.SeedCertRay.Q Br⟩ : Work.SeedCertRay.Disk).mem z →
      ∀ z₁ : ℂ, Work.SeedCertRay.Zb.mem z₁ → ∀ A : ℂ, Work.SeedCertRay.Ab.mem A → z ∈ Work.SeedCertRay.Petal z₁ A 4 := by
  intro z hz z₁ hz₁ A hA
  -- ## 1. decode the certificate
  have hSpos : (0:ℝ) < (MSZ:ℝ) := MSZ_pos_real
  have hdec := of_decide_eq_true h
  set U : ℤ := ACX*(Bx - ZCX) - ACY*(By - ZCY) with hU
  set V : ℤ := iabs (ACX*(By - ZCY) + ACY*(Bx - ZCX)) with hV
  set W : ℤ := 2*ETAA*(iabs (Bx - ZCX) + iabs (By - ZCY))
      + (iabs ACX + iabs ACY + 2*ETAA)*(Br + 2*ETA1) with hW
  have hdec' : iabs (2*RRM*U - MSZ*MSZ*MSZ) + 2*RRM*(V + W) < MSZ*MSZ*MSZ := hdec
  have hcert := cert_real U V W hdec'
  set s : ℝ := (U:ℝ)/(MSZ:ℝ)^2 with hs
  set t : ℝ := (V:ℝ)/(MSZ:ℝ)^2 with ht
  set d : ℝ := (W:ℝ)/(MSZ:ℝ)^2 with hd
  rw [RRM_div_MSZ] at hcert
  have hcert2 : |8*s - 1| + 8*(t + d) < 1 := by
    rw [show (2:ℝ)*4 = 8 by norm_num] at hcert
    exact hcert
  have hlt : |8*s - 1| < 1 - 8*(t + d) := by linarith
  have habs := abs_lt.mp hlt
  have h1 : t + d < s := by linarith [habs.1]
  have h2 : s + t + d < 1/4 := by linarith [habs.2]
  have ht0 : 0 ≤ t := by
    rw [ht]
    exact div_nonneg (by rw [hV]; exact_mod_cast iabs_nonneg _) (by positivity)
  obtain ⟨hkey1, hkey2⟩ := cert_algebra ht0 h1 h2
  -- ## 2. the geometric objects
  set p : ℂ := (((Q Bx:ℚ):ℝ):ℂ) + (((Q By:ℚ):ℝ):ℂ)*Complex.I with hp
  set z0 : ℂ := (((Q ZCX:ℚ):ℝ):ℂ) + (((Q ZCY:ℚ):ℝ):ℂ)*Complex.I with hz0
  set a : ℂ := (((Q ACX:ℚ):ℝ):ℂ) + (((Q ACY:ℚ):ℝ):ℂ)*Complex.I with ha
  have hpre : p.re = ((Q Bx:ℚ):ℝ) := by rw [hp]; simp
  have hpim : p.im = ((Q By:ℚ):ℝ) := by rw [hp]; simp
  have hzr : z0.re = ((Q ZCX:ℚ):ℝ) := by rw [hz0]; simp
  have hzi : z0.im = ((Q ZCY:ℚ):ℝ) := by rw [hz0]; simp
  have har : a.re = ((Q ACX:ℚ):ℝ) := by rw [ha]; simp
  have hai : a.im = ((Q ACY:ℚ):ℝ) := by rw [ha]; simp
  have hzp : ‖z - p‖ ≤ ((Q Br:ℚ):ℝ) := by
    have hh := hz
    simp only [Disk.mem, Disk.center] at hh
    exact hh
  have hz1e : |z₁.re - z0.re| ≤ ((Q ETA1:ℚ):ℝ) ∧ |z₁.im - z0.im| ≤ ((Q ETA1:ℚ):ℝ) := by
    have hh := hz₁
    simp only [Zb, Box.mem] at hh
    rw [hzr, hzi]
    refine ⟨?_, ?_⟩
    · rw [abs_le]; constructor <;> push_cast at hh ⊢ <;> linarith
    · rw [abs_le]; constructor <;> push_cast at hh ⊢ <;> linarith
  have hAe : |A.re - a.re| ≤ ((Q ETAA:ℚ):ℝ) ∧ |A.im - a.im| ≤ ((Q ETAA:ℚ):ℝ) := by
    have hh := hA
    simp only [Ab, Box.mem] at hh
    rw [har, hai]
    refine ⟨?_, ?_⟩
    · rw [abs_le]; constructor <;> push_cast at hh ⊢ <;> linarith
    · rw [abs_le]; constructor <;> push_cast at hh ⊢ <;> linarith
  -- ## 3. bound `‖A (z - z₁) - a (p - z₀)‖ ≤ d`
  have hbound := norm_mul_sub_le z z₁ A p z0 a ((Q Br:ℚ):ℝ) ((Q ETA1:ℚ):ℝ) ((Q ETAA:ℚ):ℝ)
      hzp hz1e.1 hz1e.2 hAe.1 hAe.2
  have hd_eq : 2*((Q ETAA:ℚ):ℝ)*(|p.re - z0.re| + |p.im - z0.im|)
      + (|a.re| + |a.im| + 2*((Q ETAA:ℚ):ℝ))*(((Q Br:ℚ):ℝ) + 2*((Q ETA1:ℚ):ℝ)) = d := by
    rw [hpre, hpim, hzr, hzi, har, hai, hd]
    exact (d_ident Bx By Br).symm
  have hwd : ‖A*(z - z₁) - a*(p - z0)‖ ≤ d := by
    rw [hd_eq] at hbound
    exact hbound
  -- ## 4. `a (p - z₀)` is in the open disk of radius `1/8` about `1/8`
  have hw0re : (a*(p - z0)).re = s := by
    rw [hs, hU]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im]
    rw [har, hai, hpre, hpim, hzr, hzi]
    simp only [Q_cast]
    push_cast
    field_simp
  have hw0im : (a*(p - z0)).im = ((ACX*(By - ZCY) + ACY*(Bx - ZCX) : ℤ):ℝ)/(MSZ:ℝ)^2 := by
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im]
    rw [har, hai, hpre, hpim, hzr, hzi]
    simp only [Q_cast]
    push_cast
    field_simp
  have hw0im_abs : |(a*(p - z0)).im| = t := by
    rw [hw0im, ht, hV, iabs_cast]
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (MSZ:ℝ)^2)]
  have hsq : ‖a*(p - z0) - ((1/8:ℝ):ℂ)‖^2 = (s - 1/8)^2 + t^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, hw0re]
    rw [← hw0im_abs, sq_abs]
    ring
  have hw0norm : ‖a*(p - z0) - ((1/8:ℝ):ℂ)‖ < 1/8 - d := by
    have h2' : ‖a*(p - z0) - ((1/8:ℝ):ℂ)‖^2 < (1/8 - d)^2 := by
      rw [hsq]; exact hkey1
    have h3 := sq_lt_sq.mp h2'
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos hkey2] at h3
  -- ## 5. conclude
  have hfin : ‖A*(z - z₁) - ((1/8:ℝ):ℂ)‖ < 1/8 := by
    have htri : ‖A*(z - z₁) - ((1/8:ℝ):ℂ)‖
        ≤ ‖A*(z - z₁) - a*(p - z0)‖ + ‖a*(p - z0) - ((1/8:ℝ):ℂ)‖ := by
      have hd : A*(z - z₁) - ((1/8:ℝ):ℂ)
          = (A*(z - z₁) - a*(p - z0)) + (a*(p - z0) - ((1/8:ℝ):ℂ)) := by ring
      conv_lhs => rw [hd]
      exact norm_add_le (A*(z - z₁) - a*(p - z0)) (a*(p - z0) - ((1/8:ℝ):ℂ))
    linarith [htri, hwd, hw0norm]
  have hAne : A ≠ 0 := by
    intro h0
    have h1' : A.re = 0 := by rw [h0]; simp
    have h2' : ((Q ACX:ℚ):ℝ) - ((Q ETAA:ℚ):ℝ) ≤ A.re := by
      have hh := hAe.1
      rw [har] at hh
      rw [abs_le] at hh
      linarith [hh.1]
    have h3' : (0:ℝ) < ((Q ACX:ℚ):ℝ) - ((Q ETAA:ℚ):ℝ) := by
      rw [Q_cast, Q_cast, ← sub_div]
      apply div_pos
      · exact_mod_cast (show (ETAA:ℤ) < ACX by norm_num [ACX, ETAA])
      · exact MSZ_pos_real
    linarith
  rw [Petal_iff_norm (by norm_num : (0:ℝ) < 4) hAne z]
  convert hfin using 2 <;> norm_num

end Work.SeedCertRay
