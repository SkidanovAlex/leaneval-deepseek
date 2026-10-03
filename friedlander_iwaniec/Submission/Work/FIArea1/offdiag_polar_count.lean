import Mathlib
import Submission.Work.FIArea1.conjunct2_defs
import Submission.Work.FIArea1.Basic
import Submission.Work.FIArea1.L51Defs
import Submission.Work.FIArea2.hits_card_le
import Submission.Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm
import Submission.Work.FIArea1.offdiag_delta_ne_wne_le
import Submission.Work.FIArea1.offdiag_delta_ne_wzero_le

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary facts about the polar box (*FI* (5.14)) -/

/-- `θ ≤ 1`: the polar box (5.14) is contained in the dyadic annulus `N < |z|² ≤ 2N` of the
`Zbox` of `Submission.Work.FIArea1.L51Defs`. -/
lemma offdiag_theta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  have hx0 : (0:ℝ) < (Pa.x : ℝ) := by
    have : (0:ℕ) < Pa.x := by linarith [Pa.hx]
    exact_mod_cast this
  have hlog1 : (1:ℝ) ≤ Real.log (Pa.x : ℝ) := by
    rw [Real.le_log_iff_exp_le hx0]
    have : (3:ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith [Real.exp_one_lt_three]
  have hA' : (0:ℝ) ≤ Pa.A' := by
    have h1 := Pa.hA'
    have hA0 : (0:ℝ) ≤ Pa.A := le_of_lt Pa.hA
    nlinarith [show (0:ℝ) < (2:ℝ)^(20:ℕ) by positivity]
  calc (Real.log (Pa.x : ℝ)) ^ (-Pa.A') ≤ (Real.log (Pa.x : ℝ)) ^ (0:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    _ = 1 := Real.rpow_zero _

/-- The norm of a primary Gaussian integer is odd. -/
lemma offdiag_gnorm_odd_of_primary {z : GaussianInt} (h : Work.FIPlan.IsPrimary z) :
    Odd (Work.FIPlan.gnorm z) := by
  rw [gnorm_coords]
  refine h.1.natAbs.pow.add_even ?_
  obtain ⟨k, hk⟩ := h.2.1.natAbs
  exact ⟨2 * k ^ 2, by rw [hk]; ring⟩

/-- A point of the polar box (5.14) is primitive (`(z, z̄) = 1`). -/
lemma offdiag_isPrimitive_of_polarSupp {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (hz : z ∈ polarSupp Pa φ) : Work.FIPlan.IsPrimitive z := by
  rw [mem_polarSupp] at hz
  exact Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm hz.2.2.1
    (offdiag_gnorm_odd_of_primary hz.2.1.1)

/-- A point of the polar box (5.14) lies in the `Zbox N` of `L51Defs`. -/
lemma offdiag_mem_Zbox_of_polarSupp {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (hz : z ∈ polarSupp Pa φ) : z ∈ Zbox Pa.N := by
  rw [mem_polarSupp] at hz
  obtain ⟨hzbox, hpolar, hsq, hns⟩ := hz
  have hgn : (Work.FIPlan.gnorm z : ℝ) ≤ 2 * Pa.N := by
    have h1 := hpolar.2.2.1
    have h2 : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by
      have := offdiag_theta_le_one Pa
      nlinarith [Pa.hN1]
    linarith
  have hcoord : (Work.FIPlan.gnorm z : ℝ) = (z.re.natAbs : ℝ)^2 + (z.im.natAbs : ℝ)^2 := by
    rw [gnorm_coords]; push_cast; ring
  rw [mem_Zbox_iff]
  refine ⟨?_, ?_, hpolar.2.1, hgn⟩
  · rw [Work.FIArea2.mem_gBox_iff]
    have hKZ : KZ Pa.N = ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℤ) := rfl
    constructor
    · rw [Finset.mem_Icc]
      have h1 : ((z.re.natAbs : ℕ) : ℝ) ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℝ) := by
        have h2 : ((z.re.natAbs : ℝ))^2 ≤ 2 * Pa.N := by
          nlinarith [hcoord, sq_nonneg (z.im.natAbs : ℝ), hgn]
        have h3 : ((z.re.natAbs : ℝ)) ≤ Real.sqrt (2 * Pa.N) := by
          rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (z.re.natAbs : ℝ))]
          exact Real.sqrt_le_sqrt h2
        exact h3.trans (Nat.le_ceil _)
      have h4 : z.re.natAbs ≤ ⌈Real.sqrt (2 * Pa.N)⌉₊ := Nat.cast_le.mp h1
      have h7 : |z.re| ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℤ) := by
        rw [← Int.natCast_natAbs]; exact_mod_cast h4
      simp only [KZ]
      exact abs_le.mp h7
    · rw [Finset.mem_Icc]
      have h1 : ((z.im.natAbs : ℕ) : ℝ) ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℝ) := by
        have h2 : ((z.im.natAbs : ℝ))^2 ≤ 2 * Pa.N := by
          nlinarith [hcoord, sq_nonneg (z.re.natAbs : ℝ), hgn]
        have h3 : ((z.im.natAbs : ℝ)) ≤ Real.sqrt (2 * Pa.N) := by
          rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (z.im.natAbs : ℝ))]
          exact Real.sqrt_le_sqrt h2
        exact h3.trans (Nat.le_ceil _)
      have h4 : z.im.natAbs ≤ ⌈Real.sqrt (2 * Pa.N)⌉₊ := Nat.cast_le.mp h1
      have h7 : |z.im| ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℤ) := by
        rw [← Int.natCast_natAbs]; exact_mod_cast h4
      simp only [KZ]
      exact abs_le.mp h7
  · exact offdiag_isPrimitive_of_polarSupp (by rw [mem_polarSupp]; exact ⟨hzbox, hpolar, hsq, hns⟩)

/-- **`Δ = 0` in `Zbox`.**  Two primitive points of the dyadic annulus `N < |z|² ≤ 2N` with
`Δ(z₁,z₂) = Im(z̄₁z₂) = 0` are equal up to sign. -/
lemma offdiag_eq_neg_or_eq_of_Delta_eq_zero {N : ℝ} (hN : 2 ≤ N) {z1 z2 : GaussianInt}
    (h1 : z1 ∈ Zbox N) (h2 : z2 ∈ Zbox N) (hΔ : Work.FIPlan.Delta z1 z2 = 0) :
    z2 = z1 ∨ z2 = -z1 := by
  rw [mem_Zbox_iff] at h1 h2
  obtain ⟨_, hprim1, hN1, hN1'⟩ := h1
  obtain ⟨_, hprim2, hN2, hN2'⟩ := h2
  have hgn : Work.FIPlan.gnorm z1 ≠ 0 := by
    intro h0
    rw [h0] at hN1
    push_cast at hN1
    linarith
  have him : (star z1 * z2).im = 0 := by
    rw [Work.FIPlan.Delta] at hΔ; exact hΔ
  set P : ℤ := (star z1 * z2).re with hP
  have hPz : star z1 * z2 = (P : GaussianInt) := by
    ext <;> simp [hP, him]
  have hself : z1 * star z1 = (((Work.FIPlan.gnorm z1 : ℕ)) : GaussianInt) := by
    have h1 : (((Work.FIPlan.gnorm z1 : ℕ)) : GaussianInt) = ((z1.norm : ℤ) : GaussianInt) := by
      have h2 : ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) = z1.norm := by
        rw [Work.FIPlan.gnorm]
        exact Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num : (-1:ℤ) ≤ 0) z1)
      exact_mod_cast h2
    rw [h1, ← Zsqrtd.norm_eq_mul_conj]
  have hmain : (((Work.FIPlan.gnorm z1 : ℕ)) : GaussianInt) * z2 = z1 * (P : GaussianInt) := by
    have h2' : z1 * (star z1 * z2) = z1 * (P : GaussianInt) := by rw [hPz]
    rw [← mul_assoc, hself] at h2'
    simpa using h2'
  have e1 : (((Work.FIPlan.gnorm z1 : ℕ)) : ℤ) * z2.re = z1.re * P := by
    have := congrArg Zsqrtd.re hmain
    simpa using this
  have e2 : (((Work.FIPlan.gnorm z1 : ℕ)) : ℤ) * z2.im = z1.im * P := by
    have := congrArg Zsqrtd.im hmain
    simpa using this
  have hcop : IsCoprime z1.re z1.im := Work.FIArea2.isCoprime_re_im_of_isCoprime_star hprim1
  obtain ⟨a, b, hab⟩ := hcop
  have hdvd1 : (((Work.FIPlan.gnorm z1 : ℕ)) : ℤ) ∣ z1.re * P := ⟨z2.re, by rw [← e1]⟩
  have hdvd2 : (((Work.FIPlan.gnorm z1 : ℕ)) : ℤ) ∣ z1.im * P := ⟨z2.im, by rw [← e2]⟩
  have hdvdP : (((Work.FIPlan.gnorm z1 : ℕ)) : ℤ) ∣ P := by
    have hsum := dvd_add (dvd_mul_of_dvd_right hdvd1 a) (dvd_mul_of_dvd_right hdvd2 b)
    have heq : a * (z1.re * P) + b * (z1.im * P) = P := by
      have h' : a * (z1.re * P) + b * (z1.im * P) = P * (a * z1.re + b * z1.im) := by ring
      rw [hab, mul_one] at h'
      exact h'
    rwa [heq] at hsum
  obtain ⟨c, hc⟩ := hdvdP
  have hgnZ : (((Work.FIPlan.gnorm z1 : ℕ)) : GaussianInt) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; exact hgn
  have hz2 : z2 = ((c : ℤ) : GaussianInt) * z1 := by
    have hmain' : (((Work.FIPlan.gnorm z1 : ℕ)) : GaussianInt) * z2
        = (((Work.FIPlan.gnorm z1 : ℕ)) : GaussianInt) * (((c : ℤ) : GaussianInt) * z1) := by
      rw [hmain, hc]; push_cast; ring
    have h' : (((Work.FIPlan.gnorm z1 : ℕ)) : GaussianInt)
        * (z2 - ((c : ℤ) : GaussianInt) * z1) = 0 := by
      rw [mul_sub, hmain', sub_self]
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 hgnZ
    · exact sub_eq_zero.mp h0
  have hgn2 : Work.FIPlan.gnorm z2 = c.natAbs ^ 2 * Work.FIPlan.gnorm z1 := by
    rw [hz2, gnorm_mul, gnorm_intCast]
  have hc2 : (c : ℤ) ^ 2 * (((Work.FIPlan.gnorm z1 : ℕ)) : ℤ)
      = (((Work.FIPlan.gnorm z2 : ℕ)) : ℤ) := by
    have h1' : (((c.natAbs ^ 2 : ℕ)) : ℤ) = (c : ℤ) ^ 2 := by
      rw [Nat.cast_pow]
      exact Int.natAbs_sq c
    have h2' : (((c.natAbs ^ 2 * Work.FIPlan.gnorm z1 : ℕ)) : ℤ)
        = (((Work.FIPlan.gnorm z2 : ℕ)) : ℤ) := by rw [← hgn2]
    rw [Nat.cast_mul, h1'] at h2'
    exact h2'
  have hgn1pos : (0:ℝ) < (Work.FIPlan.gnorm z1 : ℝ) := by
    have : 0 < Work.FIPlan.gnorm z1 := Nat.pos_of_ne_zero hgn
    exact_mod_cast this
  have hzR : ((c : ℤ) : ℝ)^2 * (Work.FIPlan.gnorm z1 : ℝ) = (Work.FIPlan.gnorm z2 : ℝ) := by
    have h := congrArg (fun t : ℤ => (t : ℝ)) hc2
    push_cast at h
    exact h
  have hclt : (c : ℝ)^2 < 2 := by nlinarith [hzR, hN2', hN1]
  have hcgt : (1:ℝ)/2 < (c : ℝ)^2 := by nlinarith [hzR, hN2, hN1']
  have hcsq : (c : ℤ) ^ 2 = 1 := by
    have h1' : (c : ℤ)^2 < 2 := by
      have := hclt; push_cast at this; exact_mod_cast this
    have h2' : (0:ℤ) < (c:ℤ)^2 := by
      have := hcgt
      have : (0:ℝ) < ((c:ℤ)^2 : ℝ) := by linarith
      exact_mod_cast this
    omega
  have hcpm : c = 1 ∨ c = -1 := by
    have h : (c - 1) * (c + 1) = 0 := by nlinarith [hcsq]
    rcases mul_eq_zero.mp h with h' | h'
    · left; linarith
    · right; linarith
  rcases hcpm with hc1 | hc1
  · left; rw [hz2, hc1]; norm_num
  · right; rw [hz2, hc1]; norm_num

/-! ## 3. The union bound over common divisors -/

/-- `gnorm 0 = 0`. -/
lemma offdiag_gnorm_zero : Work.FIPlan.gnorm (0 : GaussianInt) = 0 := by
  simp [Work.FIPlan.gnorm, Zsqrtd.norm_def]

/-- Non-coprime Gaussian integers have a common non-unit divisor. -/
lemma offdiag_exists_common_dvd {z1 z2 : GaussianInt} (h : ¬ IsCoprime z1 z2) :
    ∃ d : GaussianInt, d ∣ z1 ∧ d ∣ z2 ∧ ¬ IsUnit d := by
  rw [← isRelPrime_iff_isCoprime] at h
  rw [IsRelPrime] at h
  push_neg at h
  exact h

/-- A common non-unit divisor of two polar-box points with squarefree norm lies in the set `D` of
divisors with `gnorm > Pz` used in the union bound.  (Its norm divides `gnorm z₁`, so all its prime
factors exceed `Pz` by (5.8).) -/
lemma offdiag_exists_mem_D {Pa : Work.FITop.Params} {φ : ℝ} {z1 z2 : GaussianInt}
    (h1 : z1 ∈ polarSupp Pa φ) (h2 : z2 ∈ polarSupp Pa φ) (hne : z1 ≠ z2)
    (hnc : ¬ Work.FIPlan.GaussCoprime z1 z2) :
    ∃ d ∈ (Work.FIPlan.gBox (KZ Pa.N)).filter (fun d => Pa.Pz < Work.FIPlan.gnorm d),
      d ∣ z1 ∧ d ∣ z2 := by
  rw [Work.FIPlan.GaussCoprime] at hnc
  obtain ⟨d, hd1, hd2, hdu⟩ := offdiag_exists_common_dvd hnc
  rw [mem_polarSupp] at h1 h2
  obtain ⟨-, hp1, -, hns1⟩ := h1
  -- `gnorm d ≥ 2`
  have hd0 : d ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := hd1
    rw [h0, zero_mul] at hu
    have hz : z1 = 0 := hu
    have hgn0 : (Work.FIPlan.gnorm z1 : ℝ) = 0 := by rw [hz, offdiag_gnorm_zero]; simp
    exact absurd hp1.2.1 (by rw [hgn0]; linarith [Pa.hN1])
  have hgn1 : Work.FIPlan.gnorm d ≠ 1 := by
    intro hgn
    exact hdu (Zsqrtd.norm_eq_one_iff.mp hgn)
  have hgn2 : 2 ≤ Work.FIPlan.gnorm d := by
    rcases Nat.lt_or_ge (Work.FIPlan.gnorm d) 2 with hlt | hge
    · have : Work.FIPlan.gnorm d = 1 := by
        have hpos : 1 ≤ Work.FIPlan.gnorm d := Nat.one_le_iff_ne_zero.mpr (fun h0 => by
          have : d.norm = 0 := by
            rw [Work.FIPlan.gnorm] at h0
            exact Int.natAbs_eq_zero.mp h0
          exact hd0 ((Zsqrtd.norm_eq_zero_iff (by norm_num : (-1:ℤ) < 0) d).mp this))
        omega
      exact absurd this hgn1
    · exact hge
  -- `gnorm d ∣ gnorm z₁`
  have hdvd : Work.FIPlan.gnorm d ∣ Work.FIPlan.gnorm z1 := by
    obtain ⟨u, hu⟩ := hd1
    rw [hu, gnorm_mul]
    exact Nat.dvd_mul_right _ _
  -- all prime factors exceed `Pz`
  have hbig : Pa.Pz < Work.FIPlan.gnorm d := by
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : Work.FIPlan.gnorm d ≠ 1)
    have hpz : p ∣ Work.FIPlan.gnorm z1 := hpd.trans hdvd
    have hpP : Pa.Pz < p := by
      by_contra hle
      exact hns1 p hp (le_of_not_gt hle) hpz
    exact lt_of_lt_of_le hpP (Nat.le_of_dvd (by omega) hpd)
  -- `d` lies in the box
  have hgnle : Work.FIPlan.gnorm d ≤ Work.FIPlan.gnorm z1 := Nat.le_of_dvd (by
    rcases Nat.eq_zero_or_pos (Work.FIPlan.gnorm z1) with h | h
    · exfalso
      have hz : z1 = 0 := by
        have : z1.norm = 0 := by
          rw [Work.FIPlan.gnorm] at h
          exact Int.natAbs_eq_zero.mp h
        exact (Zsqrtd.norm_eq_zero_iff (by norm_num : (-1:ℤ) < 0) z1).mp this
      have hgn0 : (Work.FIPlan.gnorm z1 : ℝ) = 0 := by rw [hz, offdiag_gnorm_zero]; simp
      exact absurd hp1.2.1 (by rw [hgn0]; linarith [Pa.hN1])
    · exact h) hdvd
  have hgnz1 : (Work.FIPlan.gnorm z1 : ℝ) ≤ 2 * Pa.N := by
    have h2 : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by
      have := offdiag_theta_le_one Pa
      nlinarith [Pa.hN1]
    linarith [hp1.2.2.1]
  have hmem : d ∈ Work.FIPlan.gBox (KZ Pa.N) := by
    rw [Work.FIArea2.mem_gBox_iff]
    have hcoord : (Work.FIPlan.gnorm d : ℝ) = (d.re.natAbs : ℝ)^2 + (d.im.natAbs : ℝ)^2 := by
      rw [gnorm_coords]; push_cast; ring
    have hle : (Work.FIPlan.gnorm d : ℝ) ≤ 2 * Pa.N := by
      have : (Work.FIPlan.gnorm d : ℝ) ≤ (Work.FIPlan.gnorm z1 : ℝ) := by exact_mod_cast hgnle
      linarith
    constructor <;> rw [Finset.mem_Icc]
    · have h1' : ((d.re.natAbs : ℕ) : ℝ) ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℝ) := by
        have h2 : ((d.re.natAbs : ℝ))^2 ≤ 2 * Pa.N := by
          nlinarith [hcoord, sq_nonneg (d.im.natAbs : ℝ), hle]
        have h3 : ((d.re.natAbs : ℝ)) ≤ Real.sqrt (2 * Pa.N) := by
          rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (d.re.natAbs : ℝ))]
          exact Real.sqrt_le_sqrt h2
        exact h3.trans (Nat.le_ceil _)
      have h4 : d.re.natAbs ≤ ⌈Real.sqrt (2 * Pa.N)⌉₊ := Nat.cast_le.mp h1'
      have h7 : |d.re| ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℤ) := by
        rw [← Int.natCast_natAbs]; exact_mod_cast h4
      simp only [KZ]
      exact abs_le.mp h7
    · have h1' : ((d.im.natAbs : ℕ) : ℝ) ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℝ) := by
        have h2 : ((d.im.natAbs : ℝ))^2 ≤ 2 * Pa.N := by
          nlinarith [hcoord, sq_nonneg (d.re.natAbs : ℝ), hle]
        have h3 : ((d.im.natAbs : ℝ)) ≤ Real.sqrt (2 * Pa.N) := by
          rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (d.im.natAbs : ℝ))]
          exact Real.sqrt_le_sqrt h2
        exact h3.trans (Nat.le_ceil _)
      have h4 : d.im.natAbs ≤ ⌈Real.sqrt (2 * Pa.N)⌉₊ := Nat.cast_le.mp h1'
      have h7 : |d.im| ≤ ((⌈Real.sqrt (2 * Pa.N)⌉₊ : ℕ) : ℤ) := by
        rw [← Int.natCast_natAbs]; exact_mod_cast h4
      simp only [KZ]
      exact abs_le.mp h7
  exact ⟨d, Finset.mem_filter.mpr ⟨hmem, hbig⟩, hd1, hd2⟩

/-- **The union bound.**  The off-diagonal non-coprime count is at most the sum over the common
divisors `d` with `gnorm d > Pz` of the `d`-divisible bilinear sums. -/
theorem offdiagPairSum_le_sum_divisors (Pa : Work.FITop.Params) (φ : ℝ) :
    offdiagPairSum Pa φ
      ≤ ∑ W ∈ Work.FITop.boxM Pa, ∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
          ∑ d ∈ (Work.FIPlan.gBox (KZ Pa.N)).filter (fun d => Pa.Pz < Work.FIPlan.gnorm d),
            (if d ∣ Z1 ∧ d ∣ Z2 then
              (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ) else 0) := by
  classical
  set D := (Work.FIPlan.gBox (KZ Pa.N)).filter (fun d => Pa.Pz < Work.FIPlan.gnorm d) with hD
  unfold offdiagPairSum
  apply Finset.sum_le_sum; intro W hW
  apply Finset.sum_le_sum; intro Z1 hZ1
  apply Finset.sum_le_sum; intro Z2 hZ2
  by_cases hcond : Z1 = Z2 ∨ Work.FIPlan.GaussCoprime Z1 Z2
  · rw [if_pos hcond]
    refine Finset.sum_nonneg (fun d _ => ?_)
    by_cases hc : d ∣ Z1 ∧ d ∣ Z2
    · simp only [hc, if_true]; positivity
    · simp only [hc, if_false, le_refl]
  · rw [if_neg hcond]
    push Not at hcond
    obtain ⟨hne, hnc⟩ := hcond
    obtain ⟨d0, hd0mem, hd01, hd02⟩ := offdiag_exists_mem_D hZ1 hZ2 hne hnc
    have hnn : ∀ d ∈ D, (0:ℝ) ≤ (if d ∣ Z1 ∧ d ∣ Z2 then
          (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
           * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ) else 0) := by
      intro d _
      by_cases hc : d ∣ Z1 ∧ d ∣ Z2
      · simp only [hc, if_true]; positivity
      · simp only [hc, if_false, le_refl]
    have hsingle := Finset.single_le_sum hnn hd0mem
    have hval : (if d0 ∣ Z1 ∧ d0 ∣ Z2 then
          (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
           * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ) else 0)
        = (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
           * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ) := by
      simp only [hd01, hd02, and_self, if_true]
    rw [hval] at hsingle
    exact hsingle


 /-- Monotonicity of a sum under a change of the index set (with a different summand). -/
lemma offdiag_sum_le_sum_set {s t : Finset GaussianInt} (h : s ⊆ t) {f g : GaussianInt → ℝ}
    (hf : ∀ x ∈ s, f x ≤ g x) (hg : ∀ x ∈ t, x ∉ s → 0 ≤ g x) :
    (∑ x ∈ s, f x) ≤ ∑ x ∈ t, g x := by
  calc (∑ x ∈ s, f x) ≤ ∑ x ∈ s, g x := Finset.sum_le_sum hf
    _ ≤ ∑ x ∈ t, g x := Finset.sum_le_sum_of_subset_of_nonneg h hg

/-! ## 5. The vacuous small-`N` case and the final assembly -/

/-- For `N < 2` the polar box (5.14) is empty: a primary Gaussian integer has odd norm, and the
only odd sum of two squares below `4` is `3`, which is not a sum of two squares. -/
lemma offdiag_polarSupp_eq_empty_of_lt {Pa : Work.FITop.Params} {φ : ℝ} (hN : ¬ 2 ≤ Pa.N) :
    polarSupp Pa φ = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨z, hz⟩
  rw [mem_polarSupp] at hz
  obtain ⟨-, hpolar, -, -⟩ := hz
  have hNlt : Pa.N < 2 := lt_of_not_ge hN
  have hNgt1 : (1:ℝ) < (Pa.N : ℝ) := by
    have hη : (0:ℝ) < (1:ℝ)/4 + Pa.η := by linarith [Pa.hη]
    have hx3 : ((3:ℕ) : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    have hstep : (1:ℝ) < (3:ℝ) ^ ((1:ℝ)/4 + Pa.η) :=
      Real.one_lt_rpow (by norm_num) hη
    have hmono : (3:ℝ) ^ ((1:ℝ)/4 + Pa.η) ≤ (Pa.x : ℝ) ^ ((1:ℝ)/4 + Pa.η) :=
      Real.rpow_le_rpow (by norm_num) hx3 (le_of_lt hη)
    linarith [Pa.hNlo]
  have hn2 : 2 ≤ Work.FIPlan.gnorm z := by
    have h1 := hpolar.2.1
    have : (1:ℝ) < (Work.FIPlan.gnorm z : ℝ) := by linarith
    have : (1:ℕ) < Work.FIPlan.gnorm z := by exact_mod_cast this
    omega
  have hn4 : Work.FIPlan.gnorm z < 4 := by
    have h2 : (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N := hpolar.2.2.1
    have hθ : Pa.θ ≤ 1 := offdiag_theta_le_one Pa
    have : (Work.FIPlan.gnorm z : ℝ) < 4 := by nlinarith [Pa.hN1]
    exact_mod_cast this
  have hodd := offdiag_gnorm_odd_of_primary hpolar.1
  have h3 : Work.FIPlan.gnorm z = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨hre, him, -⟩ := hpolar.1
  obtain ⟨j, hj⟩ := hre
  obtain ⟨k, hk⟩ := him
  have hsum : z.re ^ 2 + z.im ^ 2 = (3 : ℤ) := by
    have h := gnorm_int z
    rw [h3] at h
    push_cast at h
    linarith
  have hid : z.re ^ 2 + z.im ^ 2 = 4 * (j^2 + j + k^2) + 1 := by
    rw [hj, hk]; ring
  rw [hid] at hsum
  omega

/-- `Δ(z,z) = Im(z̄z) = 0`. -/
lemma offdiag_Delta_self (z : GaussianInt) : Work.FIPlan.Delta z z = 0 := by
  have h : star z * z = ((z.norm : ℤ) : GaussianInt) := by
    calc star z * z = z * star z := mul_comm _ _
      _ = ((z.norm : ℤ) : GaussianInt) := (Zsqrtd.norm_eq_mul_conj z).symm
  rw [Work.FIPlan.Delta, h]
  simp

/-- Monotonicity in the two inner variables: the `polarSupp`-sum is dominated by the `Zbox`-sum. -/
lemma offdiag_polarSupp_sum_le_Zbox (Pa : Work.FITop.Params) (φ : ℝ) (W : GaussianInt) :
    (∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
        ∑ d ∈ (Work.FIPlan.gBox (KZ Pa.N)).filter (fun d => Pa.Pz < Work.FIPlan.gnorm d),
          (if Work.FIPlan.Delta Z1 Z2 = 0 ∧ d ∣ Z1 ∧ d ∣ Z2 then
            (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ) else 0))
      ≤ (∑ Z1 ∈ Work.FIArea1.Zbox Pa.N, ∑ Z2 ∈ Work.FIArea1.Zbox Pa.N,
        ∑ d ∈ (Work.FIPlan.gBox (KZ Pa.N)).filter (fun d => Pa.Pz < Work.FIPlan.gnorm d),
          (if Work.FIPlan.Delta Z1 Z2 = 0 ∧ d ∣ Z1 ∧ d ∣ Z2 then
            (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ) else 0)) := by
  have hsub : polarSupp Pa φ ⊆ Work.FIArea1.Zbox Pa.N :=
    fun z hz => offdiag_mem_Zbox_of_polarSupp hz
  have hle : ∀ Z1 Z2 : GaussianInt,
      (0:ℝ) ≤ (∑ d ∈ (Work.FIPlan.gBox (KZ Pa.N)).filter (fun d => Pa.Pz < Work.FIPlan.gnorm d),
          (if Work.FIPlan.Delta Z1 Z2 = 0 ∧ d ∣ Z1 ∧ d ∣ Z2 then
            (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ) else 0)) := by
    intro Z1 Z2
    refine Finset.sum_nonneg (fun d _ => ?_)
    by_cases hc : Work.FIPlan.Delta Z1 Z2 = 0 ∧ d ∣ Z1 ∧ d ∣ Z2 <;>
      simp only [hc, if_true, if_false] <;> try positivity
  exact le_trans
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun Z1 _ _ => Finset.sum_nonneg (fun Z2 _ => hle Z1 Z2)))
    (Finset.sum_le_sum
      (fun Z1 _ => Finset.sum_le_sum_of_subset_of_nonneg hsub (fun Z2 _ _ => hle Z1 Z2)))

/-- **The union bound for the `Δ = 0` part.**  The pairs with `Δ(z₁,z₂) = 0` are bounded by the sum
over the common divisors `d` with `gnorm d > Pz` of the `d`-divisible terms; this is the input of
`Work.FIArea1.offdiag_delta_zero_le`. -/
lemma offdiag_delta_zero_part_le_sum_divisors (Pa : Work.FITop.Params) (φ : ℝ) :
    (∑ W ∈ Work.FITop.boxM Pa, ∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
        (if Work.FIPlan.Delta Z1 Z2 = 0 then
          (if Z1 = Z2 ∨ Work.FIPlan.GaussCoprime Z1 Z2 then 0
           else (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ)) else 0))
      ≤ ∑ W ∈ Work.FITop.boxM Pa, ∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
          ∑ d ∈ (Work.FIPlan.gBox (KZ Pa.N)).filter (fun d => Pa.Pz < Work.FIPlan.gnorm d),
            (if Work.FIPlan.Delta Z1 Z2 = 0 ∧ d ∣ Z1 ∧ d ∣ Z2 then
              (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ) else 0) := by
  classical
  set D := (Work.FIPlan.gBox (KZ Pa.N)).filter (fun d => Pa.Pz < Work.FIPlan.gnorm d) with hD
  apply Finset.sum_le_sum; intro W _
  apply Finset.sum_le_sum; intro Z1 hZ1
  apply Finset.sum_le_sum; intro Z2 hZ2
  by_cases hΔ : Work.FIPlan.Delta Z1 Z2 = 0
  · by_cases hcond : Z1 = Z2 ∨ Work.FIPlan.GaussCoprime Z1 Z2
    · rw [if_pos hΔ, if_pos hcond]
      refine Finset.sum_nonneg (fun d _ => ?_)
      by_cases hc : Work.FIPlan.Delta Z1 Z2 = 0 ∧ d ∣ Z1 ∧ d ∣ Z2
      · simp only [hc, if_true]; positivity
      · simp only [hc, if_false, le_refl]
    · rw [if_pos hΔ, if_neg hcond]
      push Not at hcond
      obtain ⟨hne, hnc⟩ := hcond
      obtain ⟨d0, hd0mem, hd01, hd02⟩ := offdiag_exists_mem_D hZ1 hZ2 hne hnc
      have hnn : ∀ d ∈ D, (0:ℝ) ≤ (if Work.FIPlan.Delta Z1 Z2 = 0 ∧ d ∣ Z1 ∧ d ∣ Z2 then
            (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
             * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ) else 0) := by
        intro d _
        by_cases hc : Work.FIPlan.Delta Z1 Z2 = 0 ∧ d ∣ Z1 ∧ d ∣ Z2
        · simp only [hc, if_true]; positivity
        · simp only [hc, if_false, le_refl]
      have hsingle := Finset.single_le_sum hnn hd0mem
      have hval : (if Work.FIPlan.Delta Z1 Z2 = 0 ∧ d0 ∣ Z1 ∧ d0 ∣ Z2 then
            (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
             * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ) else 0)
          = (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
             * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ) := by
        simp only [hΔ, hd01, hd02, true_and, and_true, if_true]
      rw [hval] at hsingle
      exact hsingle
  · rw [if_neg hΔ]
    refine Finset.sum_nonneg (fun d _ => ?_)
    by_cases hc : Work.FIPlan.Delta Z1 Z2 = 0 ∧ d ∣ Z1 ∧ d ∣ Z2
    · simp only [hc, if_true]; positivity
    · simp only [hc, if_false, le_refl]

/-- **The split of the off-diagonal count by `Δ = 0`.**  The non-coprime pairs with `Δ = 0` (which
are necessarily `z₂ = ±z₁`) are separated from the pairs with `Δ ≠ 0`; the second summand is the
left-hand side of `Work.FIArea1.offdiag_delta_ne_count`. -/
lemma offdiag_delta_split (Pa : Work.FITop.Params) (φ : ℝ) :
    Work.FIArea1.offdiagPairSum Pa φ
      = (∑ W ∈ Work.FITop.boxM Pa, ∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
          (if Work.FIPlan.Delta Z1 Z2 = 0 then
            (if Z1 = Z2 ∨ Work.FIPlan.GaussCoprime Z1 Z2 then 0
             else (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ)) else 0))
      + (∑ W ∈ Work.FITop.boxM Pa, ∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
          (if Work.FIPlan.Delta Z1 Z2 = 0 ∨ Work.FIPlan.GaussCoprime Z1 Z2 then 0
           else (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ))) := by
  unfold Work.FIArea1.offdiagPairSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro W _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro Z1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro Z2 _
  by_cases hΔ : Work.FIPlan.Delta Z1 Z2 = 0
  · rw [if_pos hΔ, if_pos (Or.inl hΔ), add_zero]
  · have hne : ¬ (Z1 = Z2) := fun h => hΔ (by rw [h]; exact offdiag_Delta_self Z2)
    rw [if_neg hΔ, zero_add]
    by_cases hcop : Work.FIPlan.GaussCoprime Z1 Z2
    · rw [if_pos (Or.inr hcop), if_pos (Or.inr hcop)]
    · rw [if_neg (fun h => h.elim (fun h' => absurd h' hne) (fun h' => absurd h' hcop)),
        if_neg (fun h => h.elim (fun h' => absurd h' hΔ) (fun h' => absurd h' hcop))]

/-! ## 6. Route notes for the final theorem

The proof below splits `offdiagPairSum` by `Δ = 0` (`offdiag_delta_split`): the `Δ = 0` part is
bounded with `offdiag_delta_zero_le` and the `Δ ≠ 0` part is the statement
`Work.FIArea1.offdiag_delta_ne_count` (*FI* (5.22) with the diagonal removed), which is used as a
black box here.

**Fallback if `offdiag_delta_ne_count` is unavailable** (all the ingredients are already proved in
the workspace):

* `Work.FIArea1.gauss_prime_common_divisor` (proved): every non-coprime pair of `polarSupp` points
  has a common Gaussian prime `π` with `gnorm π > Pz`; since `π ∣ z₁ ∈ Zbox N` also
  `gnorm π ≤ 2N`, so `π ∈ (gBox (KZ N)).filter (Prime · ∧ Pz < gnorm ·)`.
* `Work.FIArea1.gauss_prime_dvd_card_le` (proved): `♯{π prime : q < gnorm π, π ∣ W} ≤
  C (1 + log(gnorm W + 2)/log q)`.
* `Work.FIArea1.offdiag_count_l51` (proved, *FI* Lemma 5.1 off-diagonal): for `1 ≤ R`, `2 ≤ N'`,
  `2√N' ≤ R`, `∑_{w ∈ (gBox R).erase 0} ∑_{z₁,z₂ ∈ Zbox N'} (Δ ≠ 0) Z Z ≤ C R N'^{3/2} log^514`.
* `Work.FIArea1.gnorm_inv_sums` (proved): `∑_{gnorm d > P} (gnorm d)^{-2} ≤ C/P` and
  `∑_{d ∈ gBox R} (gnorm d)^{-1} ≤ C (1 + log(R+2))`.

Then, for the `Δ ≠ 0` part:

1. split off the single `w = 0` term (weight `Zint 0 · Zint 0 = 1`) and bound it by the number of
   non-coprime pairs `≤ ∑_{π ∈ Π} (9(2N/gnorm π + 1))² ≤ c(Pz^{-1}M^{1/2}N^{3/2} +
   M^{3/4}N^{3/4}log^{516})` using `gnorm_inv_sums`, `♯Π ≤ 30N`, and `M ≥ N`;
2. union bound over `π ∈ Π` via `gauss_prime_common_divisor` (+ `Finset.single_le_sum`);
3. partition `Π` by the dyadic ranges `gnorm π ∈ (Pz 2^k, Pz 2^{k+1}]`;
4. on each range apply `Work.FIArea1.offdiag_pi_range_le` (which performs the substitution
   `zᵢ = π yᵢ`, `W = wπ`, the fiber bound and the free count) after replacing `polarSupp` by the
   larger `Zbox N` (monotonicity, summands `≥ 0`);
5. sum the geometric series `∑_k M^{1/2}N^{3/2}/(Pz 2^k) ≤ 2Pz^{-1}M^{1/2}N^{3/2}` and absorb the
   `log` losses of the dyadic summation into `log(MN)^{516}`.

-/

/-! ## 6. The final theorem -/


/-- `Z(Re (0 · z)) = Z(0) = 1`. -/
lemma offdiag_Zint_cForm_zero (z : GaussianInt) :
    (Work.FIPlan.Zint (Work.FIPlan.cForm (0 : GaussianInt) z) : ℝ) = 1 := by
  have h : Work.FIPlan.cForm (0 : GaussianInt) z = 0 := by simp [Work.FIPlan.cForm]
  rw [h]
  norm_num [Work.FIPlan.Zint, Work.FIPlan.Zb]

/-- `-z` is never a point of the polar box when `z` is: the primary condition of (5.14) is not
negation-stable. -/
lemma offdiag_neg_not_mem_polarSupp {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt}
    (hz : z ∈ polarSupp Pa φ) : -z ∉ polarSupp Pa φ := by
  intro h
  rw [mem_polarSupp] at hz h
  have hzmod : z.im ≡ z.re - 1 [ZMOD 4] := hz.2.1.1.2.2
  have hmod : (-z).im ≡ (-z).re - 1 [ZMOD 4] := h.2.1.1.2.2
  have hre : (-z).re = -z.re := rfl
  have him : (-z).im = -z.im := rfl
  rw [hre, him] at hmod
  have hsum := hzmod.add hmod
  have hsum' : (0 : ℤ) ≡ (-2 : ℤ) [ZMOD 4] := by
    convert hsum using 1 <;> ring
  rw [Int.ModEq] at hsum'
  exact absurd hsum' (by norm_num)

/-- The `Δ = 0` part of the off-diagonal count vanishes: the only `Δ = 0` pairs in the polar box are
`z₂ = z₁` (killed by the indicator) and `z₂ = -z₁`, and `-z₁` is not in the polar box. -/
lemma offdiag_delta_zero_part_eq_zero (Pa : Work.FITop.Params) (φ : ℝ) (hN : 2 ≤ Pa.N) :
    (∑ W ∈ Work.FITop.boxM Pa, ∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
        (if Work.FIPlan.Delta Z1 Z2 = 0 then
          (if Z1 = Z2 ∨ Work.FIPlan.GaussCoprime Z1 Z2 then 0
           else (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ)) else 0)) = 0 := by
  refine Finset.sum_eq_zero (fun W _ => Finset.sum_eq_zero (fun Z1 hZ1 =>
    Finset.sum_eq_zero (fun Z2 hZ2 => ?_)))
  by_cases hΔ : Work.FIPlan.Delta Z1 Z2 = 0
  · rw [if_pos hΔ]
    by_cases hcond : Z1 = Z2 ∨ Work.FIPlan.GaussCoprime Z1 Z2
    · rw [if_pos hcond]
    · rw [if_neg hcond]
      exfalso
      push Not at hcond
      obtain ⟨hne, -⟩ := hcond
      rcases offdiag_eq_neg_or_eq_of_Delta_eq_zero hN
        (offdiag_mem_Zbox_of_polarSupp hZ1) (offdiag_mem_Zbox_of_polarSupp hZ2) hΔ with h | h
      · exact hne h.symm
      · exact offdiag_neg_not_mem_polarSupp hZ1 (h ▸ hZ2)
  · rw [if_neg hΔ]

theorem offdiag_polar_count :
    ∃ c : ℝ, 0 < c ∧ ∀ (Pa : Work.FITop.Params) (φ : ℝ),
      Work.FIArea1.offdiagPairSum Pa φ
        ≤ c * (Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4)
                + (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2))
            * (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := by
  obtain ⟨CA, hCApos, hCA⟩ := Work.FIArea1.offdiag_delta_ne_wne_le
  obtain ⟨CB, hCBpos, hCB⟩ := Work.FIArea1.offdiag_delta_ne_wzero_le
  refine ⟨CA + CB + 1, by positivity, fun Pa φ => ?_⟩
  have hMn : (0 : ℝ) ≤ Pa.M := le_trans zero_le_one Pa.hM1
  have hNn : (0 : ℝ) ≤ Pa.N := le_trans zero_le_one Pa.hN1
  have hPzn : (0 : ℝ) ≤ (Pa.Pz : ℝ) := by positivity
  have hX : (0 : ℝ) ≤ Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4) :=
    mul_nonneg (Real.rpow_nonneg hMn _) (Real.rpow_nonneg hNn _)
  have hY : (0 : ℝ) ≤ (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr hPzn) (Real.rpow_nonneg hMn _))
      (Real.rpow_nonneg hNn _)
  have hcpos : (0 : ℝ) < CA + CB + 1 := by positivity
  by_cases hN : 2 ≤ Pa.N
  · have hMN : Pa.N ≤ Pa.M := Pa.hMge
    have hL1 : (0 : ℝ) ≤ Real.log (Pa.M * Pa.N) := by
      apply Real.log_nonneg; nlinarith [hN, hMN, Pa.hM1]
    have hL1p : (0 : ℝ) ≤ (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := pow_nonneg hL1 _
    have h0 : (∑ W ∈ Work.FITop.boxM Pa, ∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
          (if Work.FIPlan.Delta Z1 Z2 = 0 then
            (if Z1 = Z2 ∨ Work.FIPlan.GaussCoprime Z1 Z2 then 0
             else (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ)) else 0)) = 0 :=
      offdiag_delta_zero_part_eq_zero Pa φ hN
    have hA := hCA Pa φ hN hMN
    have hB := hCB Pa φ hN
    have hbox : Work.FITop.boxM Pa = Work.FIPlan.gBox (KR Pa.M) := rfl
    have h0mem : (0 : GaussianInt) ∈ Work.FITop.boxM Pa := by
      rw [hbox]
      have hK : (0 : ℤ) ≤ KR Pa.M := KR_nonneg Pa.M
      refine Work.FIArea2.mem_gBox_iff.mpr ⟨?_, ?_⟩ <;>
        exact Finset.mem_Icc.mpr ⟨neg_nonpos.mpr hK, hK⟩
    have hwsplit : (∑ W ∈ Work.FITop.boxM Pa, ∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
          (if Work.FIPlan.Delta Z1 Z2 = 0 ∨ Work.FIPlan.GaussCoprime Z1 Z2 then 0
           else (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ)))
        = (∑ W ∈ (Work.FIPlan.gBox (KR Pa.M)).erase 0,
            ∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
            (if Work.FIPlan.Delta Z1 Z2 = 0 ∨ Work.FIPlan.GaussCoprime Z1 Z2 then 0
             else (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
                  * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ)))
          + (∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
              (if Work.FIPlan.Delta Z1 Z2 = 0 ∨ Work.FIPlan.GaussCoprime Z1 Z2 then 0
               else 1)) := by
      have hzero : (∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
            (if Work.FIPlan.Delta Z1 Z2 = 0 ∨ Work.FIPlan.GaussCoprime Z1 Z2 then 0
             else (Work.FIPlan.Zint (Work.FIPlan.cForm (0 : GaussianInt) Z1) : ℝ)
                  * (Work.FIPlan.Zint (Work.FIPlan.cForm (0 : GaussianInt) Z2) : ℝ)))
          = (∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
              (if Work.FIPlan.Delta Z1 Z2 = 0 ∨ Work.FIPlan.GaussCoprime Z1 Z2 then 0
               else 1)) := by
        apply Finset.sum_congr rfl; intro Z1 _
        apply Finset.sum_congr rfl; intro Z2 _
        by_cases hc : Work.FIPlan.Delta Z1 Z2 = 0 ∨ Work.FIPlan.GaussCoprime Z1 Z2
        · rw [if_pos hc, if_pos hc]
        · rw [if_neg hc, if_neg hc, offdiag_Zint_cForm_zero, offdiag_Zint_cForm_zero, mul_one]
      have h := Finset.add_sum_erase (Work.FITop.boxM Pa)
        (fun W => ∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
          (if Work.FIPlan.Delta Z1 Z2 = 0 ∨ Work.FIPlan.GaussCoprime Z1 Z2 then 0
           else (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ))) h0mem
      rw [← h, hbox, hzero, add_comm]
    set X : ℝ := Pa.M ^ ((3 : ℝ) / 4) * Pa.N ^ ((3 : ℝ) / 4) with hXdef
    set Y : ℝ := (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) with hYdef
    set L : ℝ := (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) with hLdef
    set P : ℝ := CA * (Pa.Pz : ℝ)⁻¹ * Pa.M ^ ((1 : ℝ) / 2) * Pa.N ^ ((3 : ℝ) / 2) * L with hP
    set Q : ℝ := CB * (X + Y) * L with hQ
    have hX' : (0 : ℝ) ≤ X := by rw [hXdef]; exact hX
    have hY' : (0 : ℝ) ≤ Y := by rw [hYdef]; exact hY
    have hL' : (0 : ℝ) ≤ L := by rw [hLdef]; exact hL1p
    have hCAn : (0 : ℝ) ≤ CA := le_of_lt hCApos
    have hCBn : (0 : ℝ) ≤ CB := le_of_lt hCBpos
    have hΔne : (∑ W ∈ Work.FITop.boxM Pa, ∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
          (if Work.FIPlan.Delta Z1 Z2 = 0 ∨ Work.FIPlan.GaussCoprime Z1 Z2 then 0
           else (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
                * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ))) ≤ P + Q := by
      rw [hwsplit]
      exact add_le_add hA hB
    have hP' : P = CA * Y * L := by
      rw [hP, hYdef, hLdef]; ring
    have hQ' : Q = CB * (X + Y) * L := by rw [hQ]
    have hfin : CA * Y * L + CB * (X + Y) * L ≤ (CA + CB + 1) * (X + Y) * L := by
      have h1 : CA * Y * L ≤ CA * (X + Y) * L := by
        apply mul_le_mul_of_nonneg_right _ hL'
        apply mul_le_mul_of_nonneg_left _ hCAn
        linarith
      have h2 : (0 : ℝ) ≤ (X + Y) * L := mul_nonneg (add_nonneg hX' hY') hL'
      nlinarith [h1, h2, hL', hX', hY', hCAn, hCBn]
    rw [offdiag_delta_split Pa φ, h0, zero_add]
    calc (∑ W ∈ Work.FITop.boxM Pa, ∑ Z1 ∈ polarSupp Pa φ, ∑ Z2 ∈ polarSupp Pa φ,
            (if Work.FIPlan.Delta Z1 Z2 = 0 ∨ Work.FIPlan.GaussCoprime Z1 Z2 then 0
             else (Work.FIPlan.Zint (Work.FIPlan.cForm W Z1) : ℝ)
                  * (Work.FIPlan.Zint (Work.FIPlan.cForm W Z2) : ℝ)))
        ≤ P + Q := hΔne
      _ = CA * Y * L + CB * (X + Y) * L := by rw [hP', hQ']
      _ ≤ (CA + CB + 1) * (X + Y) * L := hfin
  · have hemp : polarSupp Pa φ = ∅ := offdiag_polarSupp_eq_empty_of_lt hN
    have hzero : Work.FIArea1.offdiagPairSum Pa φ = 0 := by
      unfold Work.FIArea1.offdiagPairSum
      simp [hemp]
    rw [hzero]
    have hL1 : (0 : ℝ) ≤ Real.log (Pa.M * Pa.N) := by
      apply Real.log_nonneg; nlinarith [Pa.hM1, Pa.hN1]
    have hLp : (0 : ℝ) ≤ (Real.log (Pa.M * Pa.N)) ^ (516 : ℕ) := pow_nonneg hL1 _
    exact mul_nonneg (mul_nonneg (le_of_lt hcpos) (add_nonneg hX hY)) hLp
end

end Work.FIArea1