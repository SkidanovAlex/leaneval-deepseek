import Mathlib
import Submission.Work.FIArea2.area2_r3
import Submission.Work.FIArea1.count_annulus

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. From primitivity `(z, z̄) = 1` to coprimality of the coordinates -/

lemma isCoprime_re_im_of_isCoprime_star {z : GaussianInt} (h : IsCoprime z (star z)) :
    IsCoprime z.re z.im := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
  set g : ℕ := z.re.natAbs.gcd z.im.natAbs with hg
  have hdvd_re : ((g : ℤ)) ∣ z.re := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
    exact Nat.gcd_dvd_left z.re.natAbs z.im.natAbs
  have hdvd_im : ((g : ℤ)) ∣ z.im := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
    exact Nat.gcd_dvd_right z.re.natAbs z.im.natAbs
  obtain ⟨x, hx⟩ := hdvd_re
  obtain ⟨y, hy⟩ := hdvd_im
  have hz : z = ((g:ℤ) : GaussianInt) * ⟨x, y⟩ := by ext <;> simp [hx, hy]
  have hsz : star z = ((g:ℤ) : GaussianInt) * ⟨x, -y⟩ := by ext <;> simp [hx, hy]
  have hu : IsUnit (((g:ℤ) : GaussianInt)) := h.isUnit_of_dvd' ⟨_, hz⟩ ⟨_, hsz⟩
  have hnorm : Work.FIPlan.gnorm (((g:ℤ) : GaussianInt)) = 1 := Zsqrtd.norm_eq_one_iff.mpr hu
  have hg2 : Work.FIPlan.gnorm (((g:ℤ) : GaussianInt)) = g^2 := by
    rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq]; simp [sq]
  have h2 : g^2 = 1 := by rw [← hg2]; exact hnorm
  have hdvd : g ∣ 1 := by rw [← h2, pow_two]; exact dvd_mul_right g g
  exact Nat.dvd_one.mp hdvd

/-! ## 2. `Zint b ≠ 0` is exactly "`b` is a square" -/

lemma Zb_ne_zero_iff (m : ℕ) : Work.FIPlan.Zb m ≠ 0 ↔ Nat.sqrt m ^ 2 = m := by
  unfold Work.FIPlan.Zb
  split_ifs with h1 h2 <;> simp_all

lemma sqrt_sq_eq_iff (m : ℕ) : Nat.sqrt m ^ 2 = m ↔ ∃ k, k^2 = m := by
  constructor
  · intro h; exact ⟨Nat.sqrt m, h⟩
  · rintro ⟨k, hk⟩
    have h1 : k ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by nlinarith [hk])
    have h2 : Nat.sqrt m ≤ k := by
      rw [← Nat.lt_succ_iff, Nat.sqrt_lt']; nlinarith [hk]
    rw [le_antisymm h2 h1, hk]

/-- `Z(b) ≠ 0` iff `b` is a non-negative perfect square (with `Z(0) = 1`, *FI* (5.2)). -/
lemma Zint_ne_zero_iff (d : ℤ) : Work.FIPlan.Zint d ≠ 0 ↔ ∃ c : ℤ, c ^ 2 = d := by
  have hZint : Work.FIPlan.Zint d ≠ 0 ↔ 0 ≤ d ∧ Work.FIPlan.Zb d.natAbs ≠ 0 := by
    unfold Work.FIPlan.Zint
    by_cases h : d < 0
    · simp [h]
    · simp [h, not_lt.mp h]
  rw [hZint]
  constructor
  · rintro ⟨hge, hb⟩
    rw [Zb_ne_zero_iff, sqrt_sq_eq_iff] at hb
    obtain ⟨k, hk⟩ := hb
    refine ⟨(k:ℤ), ?_⟩
    have hcast : ((k:ℤ))^2 = ((k^2 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, hk, Int.natAbs_of_nonneg hge]
  · rintro ⟨c, hc⟩
    have hge : 0 ≤ d := by nlinarith [sq_nonneg c, hc]
    refine ⟨hge, ?_⟩
    rw [Zb_ne_zero_iff, sqrt_sq_eq_iff]
    refine ⟨c.natAbs, ?_⟩
    have hc' : (c.natAbs : ℤ) ^ 2 = (d.natAbs : ℤ) := by
      rw [Int.natAbs_sq, hc, Int.natAbs_of_nonneg hge]
    exact_mod_cast hc'

/-! ## 3. The box `gBox R` in coordinates -/

lemma mem_gBox_iff {R : ℤ} {w : GaussianInt} :
    w ∈ Work.FIPlan.gBox R ↔ w.re ∈ Finset.Icc (-R) R ∧ w.im ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [Finset.product_eq_sprod, Finset.mem_product] at hp
    exact hp
  · intro h
    exact ⟨(w.re, w.im), by rw [Finset.product_eq_sprod, Finset.mem_product]; exact h,
      by ext <;> rfl⟩

lemma abs_re_le_of_mem_gBox {R : ℤ} {w : GaussianInt} (hw : w ∈ Work.FIPlan.gBox R) :
    |w.re| ≤ R := by
  have h := (mem_gBox_iff.mp hw).1
  rw [Finset.mem_Icc] at h
  exact abs_le.mpr h

lemma abs_im_le_of_mem_gBox {R : ℤ} {w : GaussianInt} (hw : w ∈ Work.FIPlan.gBox R) :
    |w.im| ≤ R := by
  have h := (mem_gBox_iff.mp hw).2
  rw [Finset.mem_Icc] at h
  exact abs_le.mpr h

/-- `|w|² ≤ 2R²` for `w` in the box `gBox R` (`R ≥ 0`). -/
lemma gnorm_le_of_mem_gBox {R : ℤ} (hR : 0 ≤ R) {w : GaussianInt}
    (hw : w ∈ Work.FIPlan.gBox R) : Work.FIPlan.gnorm w ≤ 2 * R.natAbs ^ 2 := by
  have hre : w.re.natAbs ≤ R.natAbs := by
    have h := abs_re_le_of_mem_gBox hw
    have h1 : (w.re.natAbs : ℤ) = |w.re| := Int.natCast_natAbs w.re
    have h2 : (R.natAbs : ℤ) = R := Int.natAbs_of_nonneg hR
    have : (w.re.natAbs : ℤ) ≤ (R.natAbs : ℤ) := by rw [h1, h2]; exact h
    exact_mod_cast this
  have him : w.im.natAbs ≤ R.natAbs := by
    have h := abs_im_le_of_mem_gBox hw
    have h1 : (w.im.natAbs : ℤ) = |w.im| := Int.natCast_natAbs w.im
    have h2 : (R.natAbs : ℤ) = R := Int.natAbs_of_nonneg hR
    have : (w.im.natAbs : ℤ) ≤ (R.natAbs : ℤ) := by rw [h1, h2]; exact h
    exact_mod_cast this
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq]
  nlinarith [hre, him, Nat.zero_le w.re.natAbs, Nat.zero_le w.im.natAbs]

/-- `Re(wz) ≤ R (|re z| + |im z|)` for `w` in the box. -/
lemma cForm_le_of_mem_gBox {z : GaussianInt} {R : ℤ} {w : GaussianInt}
    (hw : w ∈ Work.FIPlan.gBox R) :
    (Work.FIPlan.cForm w z : ℝ) ≤ (R:ℝ) * (|(z.re:ℝ)| + |(z.im:ℝ)|) := by
  have hre : |(w.re:ℝ)| ≤ (R:ℝ) := by
    have h : (((|w.re| : ℤ)) : ℝ) ≤ (R:ℝ) := by exact_mod_cast abs_re_le_of_mem_gBox hw
    rwa [Int.cast_abs] at h
  have him : |(w.im:ℝ)| ≤ (R:ℝ) := by
    have h : (((|w.im| : ℤ)) : ℝ) ≤ (R:ℝ) := by exact_mod_cast abs_im_le_of_mem_gBox hw
    rwa [Int.cast_abs] at h
  rw [Work.FIArea1.cForm_coords]
  push_cast
  have h1 : (w.re:ℝ) * (z.re:ℝ) ≤ |(w.re:ℝ)| * |(z.re:ℝ)| := by
    calc (w.re:ℝ) * (z.re:ℝ) ≤ |(w.re:ℝ) * (z.re:ℝ)| := le_abs_self _
      _ = |(w.re:ℝ)| * |(z.re:ℝ)| := abs_mul _ _
  have h2 : -((w.im:ℝ) * (z.im:ℝ)) ≤ |(w.im:ℝ)| * |(z.im:ℝ)| := by
    calc -((w.im:ℝ) * (z.im:ℝ)) ≤ |(w.im:ℝ) * (z.im:ℝ)| := neg_le_abs _
      _ = |(w.im:ℝ)| * |(z.im:ℝ)| := abs_mul _ _
  have hzre : 0 ≤ |(z.re:ℝ)| := abs_nonneg _
  have hzim : 0 ≤ |(z.im:ℝ)| := abs_nonneg _
  calc (w.re:ℝ) * (z.re:ℝ) - (w.im:ℝ) * (z.im:ℝ)
      = (w.re:ℝ) * (z.re:ℝ) + (-((w.im:ℝ) * (z.im:ℝ))) := by ring
    _ ≤ |(w.re:ℝ)| * |(z.re:ℝ)| + |(w.im:ℝ)| * |(z.im:ℝ)| := add_le_add h1 h2
    _ ≤ (R:ℝ) * |(z.re:ℝ)| + (R:ℝ) * |(z.im:ℝ)| :=
          add_le_add (mul_le_mul_of_nonneg_right hre hzre) (mul_le_mul_of_nonneg_right him hzim)
    _ = (R:ℝ) * (|(z.re:ℝ)| + |(z.im:ℝ)|) := by ring

/-! ## 4. The per-line count -/

/-- **The one-line lattice count.**  The points of the box `gBox R` on the line `Re(wz) = d`
(a coset of `ℤ·(im z, re z)`, spaced `|z|`) number at most `2√2 R/|z| + 1`. -/
lemma card_line_le {z : GaussianInt} (hcop : IsCoprime z.re z.im)
    (hnz : Work.FIPlan.gnorm z ≠ 0) (R : ℤ) (hR : 0 ≤ R) (d : ℤ) :
    (((Work.FIPlan.gBox R).filter (fun w => Work.FIPlan.cForm w z = d)).card : ℝ)
      ≤ 2 * Real.sqrt 2 * (R:ℝ) / Real.sqrt (Work.FIPlan.gnorm z : ℝ) + 1 := by
  have hnzpos : 0 < Work.FIPlan.gnorm z := Nat.pos_of_ne_zero hnz
  have hnzR : (0:ℝ) < (Work.FIPlan.gnorm z : ℝ) := by exact_mod_cast hnzpos
  have hnzZ : ((Work.FIPlan.gnorm z : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hnz
  set T := (Work.FIPlan.gBox R).filter (fun w => Work.FIPlan.cForm w z = d) with hT
  by_cases hne : T.Nonempty
  · obtain ⟨w₀, hw₀⟩ := hne
    have hmem : ∀ w ∈ T, w ∈ Work.FIPlan.gBox R ∧ Work.FIPlan.cForm w z = d := by
      intro w hw; rw [hT, Finset.mem_filter] at hw; exact hw
    set B : Finset ℤ := T.image (Work.FIArea1.psi z) with hB
    have hinj : Set.InjOn (Work.FIArea1.psi z) (T : Set GaussianInt) := by
      intro a ha b hb hab
      simp only [Finset.mem_coe] at ha hb
      exact Work.FIArea1.psi_eq_of_cForm_eq hcop hnzZ (by rw [(hmem a ha).2, (hmem b hb).2]) hab
    have hBcard : B.card = T.card := by rw [hB]; exact Finset.card_image_of_injOn hinj
    have hdiv : ∀ t ∈ B, ((Work.FIPlan.gnorm z : ℕ) : ℤ) ∣ (t - Work.FIArea1.psi z w₀) := by
      intro t ht
      rw [hB, Finset.mem_image] at ht
      obtain ⟨w, hw, rfl⟩ := ht
      exact Work.FIArea1.nz_dvd_psi_sub hcop (by rw [(hmem w hw).2, (hmem w₀ hw₀).2])
    have hint : ∀ t ∈ B, |(t:ℝ)| ≤ (R:ℝ) * Real.sqrt (2 * (Work.FIPlan.gnorm z : ℝ)) := by
      intro t ht
      rw [hB, Finset.mem_image] at ht
      obtain ⟨w, hw, rfl⟩ := ht
      have hgw : (Work.FIPlan.gnorm w : ℝ) ≤ 2 * (R:ℝ)^2 := by
        have h := gnorm_le_of_mem_gBox hR (hmem w hw).1
        have hRnat : ((R.natAbs : ℕ) : ℝ) = (R : ℝ) := by
          have h1 : (R.natAbs : ℤ) = R := Int.natAbs_of_nonneg hR
          have := congrArg (fun x : ℤ => (x : ℝ)) h1
          simpa using this
        calc (Work.FIPlan.gnorm w : ℝ) ≤ ((2 * R.natAbs^2 : ℕ):ℝ) := by exact_mod_cast h
          _ = 2 * ((R.natAbs:ℕ):ℝ)^2 := by push_cast; ring
          _ = 2 * (R:ℝ)^2 := by rw [hRnat]
      have hsq : ((Work.FIArea1.psi z w : ℤ) : ℝ)^2
          ≤ 2 * (R:ℝ)^2 * (Work.FIPlan.gnorm z : ℝ) := by
        have h1 := Work.FIArea1.psi_sq_le w z
        have h2 : ((Work.FIArea1.psi z w : ℤ) : ℝ)^2
            ≤ (((Work.FIPlan.gnorm w : ℤ) * (Work.FIPlan.gnorm z : ℤ) : ℤ) : ℝ) := by
          exact_mod_cast h1
        push_cast at h2
        calc ((Work.FIArea1.psi z w : ℤ) : ℝ)^2
            ≤ (Work.FIPlan.gnorm w : ℝ) * (Work.FIPlan.gnorm z : ℝ) := h2
          _ ≤ (2 * (R:ℝ)^2) * (Work.FIPlan.gnorm z : ℝ) :=
              mul_le_mul_of_nonneg_right hgw (le_of_lt hnzR)
      have hsqrt : Real.sqrt (2 * (R:ℝ)^2 * (Work.FIPlan.gnorm z : ℝ))
          = (R:ℝ) * Real.sqrt (2 * (Work.FIPlan.gnorm z : ℝ)) := by
        rw [show (2:ℝ) * (R:ℝ)^2 * (Work.FIPlan.gnorm z : ℝ)
            = (R:ℝ)^2 * (2 * (Work.FIPlan.gnorm z : ℝ)) by ring,
          Real.sqrt_mul (sq_nonneg (R:ℝ)),
          Real.sqrt_sq (by exact_mod_cast hR : (0:ℝ) ≤ (R:ℝ))]
      calc |((Work.FIArea1.psi z w : ℤ) : ℝ)|
          ≤ Real.sqrt (2 * (R:ℝ)^2 * (Work.FIPlan.gnorm z : ℝ)) := Real.abs_le_sqrt hsq
        _ = (R:ℝ) * Real.sqrt (2 * (Work.FIPlan.gnorm z : ℝ)) := hsqrt
    have hmain := Work.FIArea1.card_int_le_shifted_ap (U := B) (t0 := Work.FIArea1.psi z w₀)
      (m := Work.FIPlan.gnorm z) (R := (R:ℝ) * Real.sqrt (2 * (Work.FIPlan.gnorm z : ℝ)))
      hnzpos (by positivity) hdiv hint
    rw [hBcard] at hmain
    have hstep : 2 * ((R:ℝ) * Real.sqrt (2 * (Work.FIPlan.gnorm z : ℝ))) / (Work.FIPlan.gnorm z : ℝ)
        = 2 * Real.sqrt 2 * (R:ℝ) / Real.sqrt (Work.FIPlan.gnorm z : ℝ) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      field_simp
      rw [Real.sq_sqrt (le_of_lt hnzR)]
    linarith [hmain, hstep]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-! ## 5. The final arithmetic -/

/-- The term-by-term bound behind the constant `8`: with `u = √(R+1)`, `v = |z|^{-1/2}`-style
variables, every term of the expanded product is dominated by the corresponding term of the
right-hand side. -/
lemma arith_core {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (2 ^ ((1:ℝ)/4) * u * v + 1) * (2 * Real.sqrt 2 * u^2 / v^2 + 1)
      ≤ 8 * u^3 / v + 4 * u^2 / v^2 + 4 * u * v + 4 := by
  have h24 : (2:ℝ) ^ ((1:ℝ)/4) ≤ 4 := by
    have h1 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (1:ℝ)/4 ≤ 1)
    rw [Real.rpow_one] at h1
    linarith
  have hsqrt2 : 2 * Real.sqrt 2 ≤ 4 := by
    have h : Real.sqrt 2 ≤ 2 :=
      (Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 2)).mpr (by norm_num)
    linarith
  have h268 : (2:ℝ) ^ ((1:ℝ)/4) * (2 * Real.sqrt 2) ≤ 8 := by
    have h : (2:ℝ) ^ ((1:ℝ)/4) ≤ 2 := by
      have h1 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (by norm_num : (1:ℝ)/4 ≤ 1)
      rwa [Real.rpow_one] at h1
    nlinarith [h, hsqrt2, Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) ((1:ℝ)/4),
      Real.sqrt_nonneg 2]
  have key3 : u * v * (u^2 / v^2) = u^3 / v := by
    rcases eq_or_ne v 0 with hv0 | hv0
    · rw [hv0]; norm_num
    · field_simp
  have hnn : 0 ≤ u * v * (u^2 / v^2) :=
    mul_nonneg (mul_nonneg hu hv) (div_nonneg (sq_nonneg u) (sq_nonneg v))
  have kA : (2 ^ ((1:ℝ)/4) * u * v) * (2 * Real.sqrt 2 * u^2 / v^2) ≤ 8 * (u^3/v) := by
    calc (2 ^ ((1:ℝ)/4) * u * v) * (2 * Real.sqrt 2 * u^2 / v^2)
        = (2 ^ ((1:ℝ)/4) * (2 * Real.sqrt 2)) * (u * v * (u^2 / v^2)) := by ring
      _ ≤ 8 * (u * v * (u^2 / v^2)) := mul_le_mul_of_nonneg_right h268 hnn
      _ = 8 * (u^3/v) := by rw [key3]
  have kB : 2 ^ ((1:ℝ)/4) * u * v ≤ 4 * (u * v) := by
    have h := mul_le_mul_of_nonneg_right h24 (mul_nonneg hu hv)
    calc 2 ^ ((1:ℝ)/4) * u * v = 2 ^ ((1:ℝ)/4) * (u * v) := by ring
      _ ≤ 4 * (u * v) := h
  have hC : 2 * Real.sqrt 2 * u^2 / v^2 ≤ 4 * (u^2 / v^2) := by
    rw [show 2 * Real.sqrt 2 * u^2 / v^2 = (2 * Real.sqrt 2) * (u^2/v^2) by ring]
    exact mul_le_mul_of_nonneg_right hsqrt2 (div_nonneg (sq_nonneg u) (sq_nonneg v))
  calc (2 ^ ((1:ℝ)/4) * u * v + 1) * (2 * Real.sqrt 2 * u^2 / v^2 + 1)
      = (2 ^ ((1:ℝ)/4) * u * v) * (2 * Real.sqrt 2 * u^2 / v^2) + 2 ^ ((1:ℝ)/4) * u * v
          + 2 * Real.sqrt 2 * u^2 / v^2 + 1 := by ring
    _ ≤ 8 * (u^3/v) + 4 * (u * v) + 4 * (u^2/v^2) + 4 := by linarith [kA, kB, hC]
    _ = 8 * u^3 / v + 4 * u^2 / v^2 + 4 * u * v + 4 := by ring

/-- The change of variables `u = √(R+1)`, `v = n^{1/4}` reducing the count to `arith_core`. -/
lemma hits_arith {R nr P0 : ℝ} (hR : 0 ≤ R) (hnr : 1 ≤ nr) (hP0nn : 0 ≤ P0)
    (hP0le : P0 ≤ R * (Real.sqrt 2 * Real.sqrt nr)) :
    (Real.sqrt P0 + 1) * (2 * Real.sqrt 2 * R / Real.sqrt nr + 1)
      ≤ 8 * (R + 1) ^ ((3:ℝ)/2) / nr ^ ((1:ℝ)/4)
        + 4 * (R + 1) / Real.sqrt nr
        + 4 * Real.sqrt (R + 1) * nr ^ ((1:ℝ)/4) + 4 := by
  have hR1 : (0:ℝ) < R + 1 := by linarith
  have hnrnn : (0:ℝ) < nr := lt_of_lt_of_le zero_lt_one hnr
  set u : ℝ := (R+1) ^ ((1:ℝ)/2) with hu
  set v : ℝ := nr ^ ((1:ℝ)/4) with hv
  have hunn : 0 ≤ u := Real.rpow_nonneg (le_of_lt hR1) _
  have hvnn : 0 ≤ v := Real.rpow_nonneg (le_of_lt hnrnn) _
  have hu2 : u^2 = R + 1 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hR1)]
    norm_num
  have hu3 : u^3 = (R+1) ^ ((3:ℝ)/2) := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hR1)]
    norm_num
  have hv2 : v^2 = Real.sqrt nr := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hnrnn), Real.sqrt_eq_rpow]
    norm_num
  have h24sq : ((2:ℝ) ^ ((1:ℝ)/4))^2 = Real.sqrt 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_eq_rpow]
    norm_num
  have hP0sq : (Real.sqrt P0)^2 ≤ (2 ^ ((1:ℝ)/4) * u * v)^2 := by
    rw [Real.sq_sqrt hP0nn]
    calc P0 ≤ R * (Real.sqrt 2 * Real.sqrt nr) := hP0le
      _ ≤ (R+1) * (Real.sqrt 2 * Real.sqrt nr) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (2 ^ ((1:ℝ)/4) * u * v)^2 := by
            rw [mul_pow, mul_pow, h24sq, hu2, hv2]; ring
  have hsqrtP0 : Real.sqrt P0 ≤ 2 ^ ((1:ℝ)/4) * u * v :=
    (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (by positivity) (by norm_num)).mp hP0sq
  have hbeta : 2 * Real.sqrt 2 * R / Real.sqrt nr ≤ 2 * Real.sqrt 2 * u^2 / v^2 := by
    rw [hu2, hv2]
    have h1 : 2 * Real.sqrt 2 * R ≤ 2 * Real.sqrt 2 * (R+1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact div_le_div_of_nonneg_right h1 (Real.sqrt_nonneg nr)
  have h1' : Real.sqrt P0 + 1 ≤ 2 ^ ((1:ℝ)/4) * u * v + 1 := by linarith [hsqrtP0]
  have h2' : 2 * Real.sqrt 2 * R / Real.sqrt nr + 1 ≤ 2 * Real.sqrt 2 * u^2 / v^2 + 1 :=
    by linarith [hbeta]
  calc (Real.sqrt P0 + 1) * (2 * Real.sqrt 2 * R / Real.sqrt nr + 1)
      ≤ (2 ^ ((1:ℝ)/4) * u * v + 1) * (2 * Real.sqrt 2 * u^2 / v^2 + 1) :=
        mul_le_mul h1' h2' (by positivity) (by positivity)
    _ ≤ 8 * u^3 / v + 4 * u^2 / v^2 + 4 * u * v + 4 := arith_core hunn hvnn
    _ = 8 * (R+1) ^ ((3:ℝ)/2) / nr ^ ((1:ℝ)/4) + 4 * (R+1) / Real.sqrt nr
          + 4 * Real.sqrt (R+1) * nr ^ ((1:ℝ)/4) + 4 := by
        rw [hu3, hu2, hv2, hu, hv, ← Real.sqrt_eq_rpow]

/-- **The one-point lattice count ("hits") of §5/§6.**  For a non-zero *primitive* Gaussian
integer `z` (in *FI* this is supplied by the Möbius factor of (4.13), cf.
`isCoprime_star_of_squarefree_odd_gnorm`) the number of `w` in the box `gBox R` whose `Re(wz)` is a
square (with `Z(0) = 1`, as in (5.2)) is
`≪ (R+1)^{3/2}/(gnorm z)^{1/4} + (R+1)/(gnorm z)^{1/2} + √(R+1)·(gnorm z)^{1/4} + 1`:
each value `c²` cuts the line `u·re z − v·im z = c²`, which meets the box in
`≤ 2√2 R/|z| + 1` lattice points (coset of `ℤ·i z̄`, spacing `|z|`), while the relevant `c` satisfy
`|c| ≤ (√2 R |z|)^{1/2}`; the product is `4·2^{3/4} R^{3/2}|z|^{-1/2} = 6.73·R^{3/2}/(gnorm z)^{1/4}`.
With `R = ⌈√(4M)⌉` and `|z|² ≍ N` this reads `≪ M^{3/4}N^{-1/4} + …`, the trivial count behind
(5.16) and Lemma 5.1. -/
theorem hits_card_le {z : GaussianInt} (hz : z ≠ 0) (hprim : IsCoprime z (star z)) (R : ℤ)
    (hR : 0 ≤ R) :
    (((Finset.filter (fun w => Work.FIPlan.Zint (Work.FIPlan.cForm w z) ≠ 0)
        (Work.FIPlan.gBox R)).card : ℝ)
      ≤ 8 * ((R : ℝ) + 1) ^ ((3 : ℝ) / 2)
            / (((Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4))
        + 4 * ((R : ℝ) + 1) / Real.sqrt ((Work.FIPlan.gnorm z : ℝ))
        + 4 * Real.sqrt ((R : ℝ) + 1) * (((Work.FIPlan.gnorm z : ℝ)) ^ ((1 : ℝ) / 4))
        + 4) := by
  classical
  have hnz0 : Work.FIPlan.gnorm z ≠ 0 := fun h => hz ((gnorm_eq_zero_iff z).mp h)
  have hnz1 : 1 ≤ Work.FIPlan.gnorm z := Nat.one_le_iff_ne_zero.mpr hnz0
  have hcop : IsCoprime z.re z.im := isCoprime_re_im_of_isCoprime_star hprim
  have hnr : (1:ℝ) ≤ (Work.FIPlan.gnorm z : ℝ) := by exact_mod_cast hnz1
  set P0 : ℝ := (R:ℝ) * (|(z.re:ℝ)| + |(z.im:ℝ)|) with hP0
  have hP0nn : 0 ≤ P0 := by rw [hP0]; positivity
  set C0 : ℕ := ⌊Real.sqrt P0⌋₊ with hC0
  set S := (Work.FIPlan.gBox R).filter
    (fun w => Work.FIPlan.Zint (Work.FIPlan.cForm w z) ≠ 0) with hS
  set Sc : ℕ → Finset GaussianInt :=
    fun c => (Work.FIPlan.gBox R).filter (fun w => Work.FIPlan.cForm w z = ((c:ℤ)^2)) with hSc
  have hsub : S ⊆ (Finset.range (C0+1)).biUnion Sc := by
    intro w hw
    rw [Finset.mem_biUnion]
    rw [hS, Finset.mem_filter] at hw
    obtain ⟨hwg, hwz⟩ := hw
    obtain ⟨c0, hc0⟩ := (Zint_ne_zero_iff _).mp hwz
    have hle : (Work.FIPlan.cForm w z : ℝ) ≤ P0 := by
      rw [hP0]; exact cForm_le_of_mem_gBox hwg
    have hc0le : ((c0:ℝ))^2 ≤ P0 := by
      have h1 : ((c0^2 : ℤ) : ℝ) = ((c0:ℝ))^2 := by push_cast; ring
      rw [← h1, hc0]; exact hle
    have habs : |(c0:ℝ)| ≤ Real.sqrt P0 := by
      have h2 : (|(c0:ℝ)|)^2 ≤ (Real.sqrt P0)^2 := by
        rw [sq_abs, Real.sq_sqrt hP0nn]; exact hc0le
      exact (pow_le_pow_iff_left₀ (abs_nonneg _) (Real.sqrt_nonneg _) (by norm_num)).mp h2
    have hnat : (c0.natAbs : ℝ) ≤ Real.sqrt P0 := by
      rw [show ((c0.natAbs:ℕ):ℝ) = |(c0:ℝ)| from by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]]
      exact habs
    have hC0le : c0.natAbs ≤ C0 := by
      rw [hC0]; exact Nat.le_floor hnat
    exact ⟨c0.natAbs, Finset.mem_range.mpr (by omega), by
      rw [hSc, Finset.mem_filter]; exact ⟨hwg, by rw [← hc0, Int.natAbs_sq]⟩⟩
  have hcardS : (S.card : ℝ)
      ≤ ((C0:ℝ)+1) * (2*Real.sqrt 2*(R:ℝ)/Real.sqrt (Work.FIPlan.gnorm z : ℝ) + 1) := by
    have h1 : S.card ≤ ((Finset.range (C0+1)).biUnion Sc).card := Finset.card_le_card hsub
    have h2 : ((Finset.range (C0+1)).biUnion Sc).card
        ≤ ∑ c ∈ Finset.range (C0+1), (Sc c).card := Finset.card_biUnion_le
    have h3 : ∀ c ∈ Finset.range (C0+1),
        ((Sc c).card : ℝ) ≤ 2*Real.sqrt 2*(R:ℝ)/Real.sqrt (Work.FIPlan.gnorm z : ℝ) + 1 := by
      intro c _
      have hc := card_line_le hcop hnz0 R hR ((c:ℤ)^2)
      simpa only [hSc] using hc
    calc (S.card : ℝ) ≤ (((Finset.range (C0+1)).biUnion Sc).card : ℝ) := by exact_mod_cast h1
      _ ≤ ((∑ c ∈ Finset.range (C0+1), (Sc c).card : ℕ) : ℝ) := by exact_mod_cast h2
      _ = ∑ c ∈ Finset.range (C0+1), ((Sc c).card : ℝ) := by push_cast; ring
      _ ≤ ∑ c ∈ Finset.range (C0+1),
            (2*Real.sqrt 2*(R:ℝ)/Real.sqrt (Work.FIPlan.gnorm z : ℝ) + 1) := Finset.sum_le_sum h3
      _ = ((C0:ℝ)+1) * (2*Real.sqrt 2*(R:ℝ)/Real.sqrt (Work.FIPlan.gnorm z : ℝ) + 1) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hC0le' : (C0:ℝ) + 1 ≤ Real.sqrt P0 + 1 := by
    have : (C0:ℝ) ≤ Real.sqrt P0 := by rw [hC0]; exact Nat.floor_le (Real.sqrt_nonneg P0)
    linarith
  have hcoord : ((z.re:ℝ))^2 + ((z.im:ℝ))^2 = (Work.FIPlan.gnorm z : ℝ) := by
    have h := Work.FIArea1.gnorm_int z
    have h2 := congrArg (fun t : ℤ => (t:ℝ)) h
    push_cast at h2
    linarith [h2]
  have habs_le : |(z.re:ℝ)| + |(z.im:ℝ)| ≤ Real.sqrt 2 * Real.sqrt (Work.FIPlan.gnorm z : ℝ) := by
    have h1 : (|(z.re:ℝ)| + |(z.im:ℝ)|)^2 ≤ 2 * ((z.re:ℝ)^2 + (z.im:ℝ)^2) := by
      nlinarith [sq_nonneg (|(z.re:ℝ)| - |(z.im:ℝ)|), abs_nonneg (z.re:ℝ), abs_nonneg (z.im:ℝ),
        sq_abs (z.re:ℝ), sq_abs (z.im:ℝ)]
    rw [hcoord] at h1
    have h2 : (|(z.re:ℝ)| + |(z.im:ℝ)|)^2
        ≤ (Real.sqrt 2 * Real.sqrt (Work.FIPlan.gnorm z : ℝ))^2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
        Real.sq_sqrt (by positivity : (0:ℝ) ≤ (Work.FIPlan.gnorm z : ℝ))]
      exact h1
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp h2
  have hP0bound : P0 ≤ (R:ℝ) * (Real.sqrt 2 * Real.sqrt (Work.FIPlan.gnorm z : ℝ)) := by
    rw [hP0]
    exact mul_le_mul_of_nonneg_left habs_le (by exact_mod_cast hR)
  have hfinal := hits_arith (R := (R:ℝ)) (nr := (Work.FIPlan.gnorm z : ℝ)) (P0 := P0)
    (by exact_mod_cast hR) hnr hP0nn hP0bound
  have hb : 0 ≤ 2*Real.sqrt 2*(R:ℝ)/Real.sqrt (Work.FIPlan.gnorm z : ℝ) + 1 := by positivity
  have key : ((Finset.filter (fun w => Work.FIPlan.Zint (Work.FIPlan.cForm w z) ≠ 0)
        (Work.FIPlan.gBox R)).card : ℝ) = (S.card : ℝ) := by rw [hS]
  rw [key]
  exact le_trans hcardS (le_trans (mul_le_mul_of_nonneg_right hC0le' hb) hfinal)

end

end Work.FIArea2
