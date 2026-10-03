import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea4.S15_delta_count_lines
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7CF.card_gBox_filter_dvd_absDelta
import Submission.Work.FIArea7.dvd_im_gBox_arith

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The box `gBox R` has diameter at most `2·(√2 R)`. -/
lemma gBox_diam (R : ℤ) :
    ∀ z ∈ Work.FIPlan.gBox R, ∀ w ∈ Work.FIPlan.gBox R,
      ‖z.toComplex - w.toComplex‖ ≤ 2 * (Real.sqrt 2 * (R : ℝ)) := by
  intro z hz w hw
  rw [Work.FIArea7.cf_mem_gBox_iff] at hz hw
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  have hR0 : (0 : ℤ) ≤ R := by linarith
  have hz1' : (-R : ℝ) ≤ (z.re : ℝ) := by exact_mod_cast hz1
  have hz2' : (z.re : ℝ) ≤ (R : ℝ) := by exact_mod_cast hz2
  have hz3' : (-R : ℝ) ≤ (z.im : ℝ) := by exact_mod_cast hz3
  have hz4' : (z.im : ℝ) ≤ (R : ℝ) := by exact_mod_cast hz4
  have hw1' : (-R : ℝ) ≤ (w.re : ℝ) := by exact_mod_cast hw1
  have hw2' : (w.re : ℝ) ≤ (R : ℝ) := by exact_mod_cast hw2
  have hw3' : (-R : ℝ) ≤ (w.im : ℝ) := by exact_mod_cast hw3
  have hw4' : (w.im : ℝ) ≤ (R : ℝ) := by exact_mod_cast hw4
  have hsub : z.toComplex - w.toComplex = (z - w).toComplex := by rw [map_sub]
  rw [hsub, Work.FIArea4.norm_toComplex_eq_sqrt_gnorm]
  have hgn : ((Work.FIPlan.gnorm (z - w) : ℕ) : ℝ) ≤ (2 * Real.sqrt 2 * (R : ℝ)) ^ 2 := by
    have h1 : ((Work.FIPlan.gnorm (z - w) : ℕ) : ℝ)
        = (((z - w).re : ℤ) : ℝ) ^ 2 + (((z - w).im : ℤ) : ℝ) ^ 2 := by
      have h := Work.FIArea7.norm_eq (z - w)
      have h2 : ((Work.FIPlan.gnorm (z - w) : ℕ) : ℝ)
          = ((Work.FIPlan.gnorm (z - w) : ℤ) : ℝ) := by
        push_cast; ring
      rw [h2, h]; push_cast; ring
    rw [h1, show (2 * Real.sqrt 2 * (R:ℝ))^2 = 8 * (R:ℝ)^2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; ring]
    have e1 : (((z - w).re : ℤ) : ℝ) = (z.re : ℝ) - (w.re : ℝ) := by simp
    have e2 : (((z - w).im : ℤ) : ℝ) = (z.im : ℝ) - (w.im : ℝ) := by simp
    rw [e1, e2]
    have hzr : |(z.re : ℝ) - (w.re : ℝ)| ≤ 2 * (R:ℝ) := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    have hzi : |(z.im : ℝ) - (w.im : ℝ)| ≤ 2 * (R:ℝ) := by
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    nlinarith [sq_abs ((z.re : ℝ) - (w.re : ℝ)), sq_abs ((z.im : ℝ) - (w.im : ℝ))]
  calc Real.sqrt ((Work.FIPlan.gnorm (z - w) : ℕ) : ℝ)
      ≤ Real.sqrt ((2 * Real.sqrt 2 * (R : ℝ)) ^ 2) := Real.sqrt_le_sqrt hgn
    _ = 2 * Real.sqrt 2 * (R : ℝ) := Real.sqrt_sq (by positivity)
    _ = 2 * (Real.sqrt 2 * (R : ℝ)) := by ring

/-- On the box, `|Δ(z₁,z₂)| ≤ (|r₁|+|s₁|)·R`. -/
lemma abs_Delta_le_gBox (z1 : GaussianInt) (R : ℤ) :
    ∀ z ∈ Work.FIPlan.gBox R,
      |((Work.FIPlan.Delta z1 z : ℤ) : ℝ)| ≤ (((|z1.re| + |z1.im| : ℤ) : ℝ)) * (R : ℝ) := by
  intro z hz
  rw [Work.FIArea7.cf_mem_gBox_iff] at hz
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hz
  have hR0 : (0:ℤ) ≤ R := by linarith
  have hR0' : (0:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR0
  have hzr : |(z.re : ℝ)| ≤ (R:ℝ) := by
    rw [abs_le]; exact ⟨by exact_mod_cast hz1, by exact_mod_cast hz2⟩
  have hzi : |(z.im : ℝ)| ≤ (R:ℝ) := by
    rw [abs_le]; exact ⟨by exact_mod_cast hz3, by exact_mod_cast hz4⟩
  have h : ((Work.FIPlan.Delta z1 z : ℤ) : ℝ) = (z1.re:ℝ)*(z.im:ℝ) - (z1.im:ℝ)*(z.re:ℝ) := by
    rw [Work.FIArea4.Delta_eq]; push_cast; ring
  rw [h]
  have h1 : |(z1.re:ℝ)*(z.im:ℝ)| ≤ (|(z1.re:ℝ)|) * (R:ℝ) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hzi (abs_nonneg _)
  have h2 : |(z1.im:ℝ)*(z.re:ℝ)| ≤ (|(z1.im:ℝ)|) * (R:ℝ) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hzr (abs_nonneg _)
  have h3 : |(z1.re:ℝ)*(z.im:ℝ) - (z1.im:ℝ)*(z.re:ℝ)|
      ≤ |(z1.re:ℝ)*(z.im:ℝ)| + |(z1.im:ℝ)*(z.re:ℝ)| := by
    rw [sub_eq_add_neg]
    calc |(z1.re:ℝ)*(z.im:ℝ) + -((z1.im:ℝ)*(z.re:ℝ))|
        ≤ |(z1.re:ℝ)*(z.im:ℝ)| + |-((z1.im:ℝ)*(z.re:ℝ))| := abs_add_le _ _
      _ = |(z1.re:ℝ)*(z.im:ℝ)| + |(z1.im:ℝ)*(z.re:ℝ)| := by rw [abs_neg]
  have h4 : (|(z1.re:ℝ)|) * (R:ℝ) + (|(z1.im:ℝ)|) * (R:ℝ)
      = (((|z1.re| + |z1.im| : ℤ) : ℝ)) * (R:ℝ) := by push_cast; ring
  linarith [h3, h1, h2]

/-- **The fibre count.** -/
theorem card_gBox_filter_dvd_Delta_le (z1 : GaussianInt) (R : ℤ) (m : ℕ) (hR : 0 ≤ R)
    (hm : 1 ≤ m) (hr : z1.re ≠ 0) (hcop : IsCoprime z1.re z1.im) :
    ((((Work.FIPlan.gBox R).filter (fun z2 => (m:ℤ) ∣ Work.FIPlan.Delta z1 z2)).card : ℝ)
      ≤ (4 * Real.sqrt 2 * (R:ℝ) / ‖z1.toComplex‖ + 1)
          * (2 * (((|z1.re| + |z1.im| : ℤ) : ℝ) * (R:ℝ) / (m:ℝ)) + 1)) := by
  classical
  have hρ : 0 ≤ Real.sqrt 2 * (R:ℝ) := mul_nonneg (Real.sqrt_nonneg 2) (by exact_mod_cast hR)
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  let S : Finset GaussianInt :=
    (Work.FIPlan.gBox R).filter (fun z2 => (m:ℤ) ∣ Work.FIPlan.Delta z1 z2)
  let f : GaussianInt → ℤ := fun z => Work.FIPlan.Delta z1 z / (m:ℤ)
  have hSS : S = (Work.FIPlan.gBox R).filter (fun z2 => (m:ℤ) ∣ Work.FIPlan.Delta z1 z2) := rfl
  have hfiber : ∀ k ∈ S.image f, ((S.filter (fun z => f z = k)).card : ℝ)
      ≤ 4 * (Real.sqrt 2 * (R:ℝ)) / ‖z1.toComplex‖ + 1 := by
    intro k hk
    have hsub : S.filter (fun z => f z = k)
        ⊆ (Work.FIPlan.gBox R).filter (fun z => Work.FIPlan.Delta z1 z = (m:ℤ) * k) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      obtain ⟨hzS, hzk⟩ := hz
      rw [hSS, Finset.mem_filter] at hzS
      refine ⟨hzS.1, ?_⟩
      have h4 : (m:ℤ) * f z = Work.FIPlan.Delta z1 z := Int.mul_ediv_cancel' hzS.2
      rw [hzk] at h4
      exact h4.symm
    exact le_trans (Nat.cast_le.mpr (Finset.card_le_card hsub))
      (Work.FIArea4.card_Delta_fiber_le (T := Work.FIPlan.gBox R) (z1 := z1)
        (ρ := Real.sqrt 2 * (R:ℝ)) hρ hr hcop (gBox_diam R) ((m:ℤ) * k))
  have himg : ((S.image f).card : ℝ)
      ≤ 2 * (((|z1.re| + |z1.im| : ℤ) : ℝ) * (R:ℝ) / (m:ℝ)) + 1 := by
    have hB0 : 0 ≤ (((|z1.re| + |z1.im| : ℤ) : ℝ) * (R:ℝ)) := by
      have : (0:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
      positivity
    have hBm : 0 ≤ (((|z1.re| + |z1.im| : ℤ) : ℝ) * (R:ℝ)) / (m:ℝ) := div_nonneg hB0 hmR.le
    refine Work.FIArea4.card_int_le_of_mem_interval (S.image f)
      (t := -((((|z1.re| + |z1.im| : ℤ) : ℝ) * (R:ℝ)) / (m:ℝ)))
      (ρ := ((((|z1.re| + |z1.im| : ℤ) : ℝ) * (R:ℝ)) / (m:ℝ))) hBm ?_
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzS : z ∈ S := hz
    rw [hSS, Finset.mem_filter] at hzS
    have hdvd : (m:ℤ) ∣ Work.FIPlan.Delta z1 z := hzS.2
    have hmul : (m:ℤ) * f z = Work.FIPlan.Delta z1 z := Int.mul_ediv_cancel' hdvd
    have hcast : ((m:ℤ):ℝ) * ((f z : ℤ):ℝ) = ((Work.FIPlan.Delta z1 z : ℤ):ℝ) := by
      rw [← hmul]; push_cast; ring
    have hmm2 : ((m:ℤ):ℝ) = (m:ℝ) := by push_cast; ring
    have habs : (m:ℝ) * |((f z : ℤ) : ℝ)| = |((Work.FIPlan.Delta z1 z : ℤ) : ℝ)| := by
      rw [← hcast, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((m:ℤ):ℝ)), hmm2]
    have hspan := abs_Delta_le_gBox z1 R z hzS.1
    have hle : |((f z : ℤ) : ℝ)| ≤ ((((|z1.re| + |z1.im| : ℤ) : ℝ) * (R:ℝ)) / (m:ℝ)) := by
      rw [le_div_iff₀ hmR]
      nlinarith [hspan, habs]
    rw [abs_le] at hle
    exact ⟨by linarith [hle.2], by linarith [hle.1]⟩
  have hcardS : (S.card : ℝ)
      ≤ (4 * Real.sqrt 2 * (R:ℝ) / ‖z1.toComplex‖ + 1) * ((S.image f).card : ℝ) := by
    have hmaps : Set.MapsTo f ↑S ↑(S.image f) := fun z hz => Finset.mem_image_of_mem _ hz
    have h1 : (S.card : ℝ) = ∑ k ∈ S.image f, ((S.filter (fun z => f z = k)).card : ℝ) := by
      rw [Finset.card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
    rw [h1]
    calc ∑ k ∈ S.image f, ((S.filter (fun z => f z = k)).card : ℝ)
        ≤ ∑ _k ∈ S.image f, (4 * (Real.sqrt 2 * (R:ℝ)) / ‖z1.toComplex‖ + 1) :=
          Finset.sum_le_sum hfiber
      _ = ((S.image f).card : ℝ) * (4 * (Real.sqrt 2 * (R:ℝ)) / ‖z1.toComplex‖ + 1) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = (4 * Real.sqrt 2 * (R:ℝ) / ‖z1.toComplex‖ + 1) * ((S.image f).card : ℝ) := by ring
  have hK0 : 0 ≤ 4 * Real.sqrt 2 * (R:ℝ) / ‖z1.toComplex‖ + 1 := by positivity
  have hfinal : (S.card : ℝ) ≤ (4 * Real.sqrt 2 * (R:ℝ) / ‖z1.toComplex‖ + 1)
      * (2 * ((((|z1.re| + |z1.im| : ℤ) : ℝ) * (R:ℝ)) / (m:ℝ)) + 1) :=
    le_trans hcardS (mul_le_mul_of_nonneg_left himg hK0)
  simpa only [hSS] using hfinal

/-- The card of the box is `(2R+1)²`-shaped. -/
lemma gBox_card_eq (R : ℤ) :
    (Work.FIPlan.gBox R).card = (2 * R + 1).toNat ^ 2 := by
  have hbox : Work.FIPlan.gBox R
      = ((Finset.Icc (-R) R) ×ˢ (Finset.Icc (-R) R)).image
          (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : GaussianInt)) := by
    rw [Work.FIPlan.gBox, Finset.product_eq_sprod]
  rw [hbox, Finset.card_image_of_injective _ Work.FIPlan.gaussMk_injective,
    Finset.card_product, Int.card_Icc]
  rw [show R + 1 - -R = 2 * R + 1 by ring]
  ring

theorem card_dvd_im_gBox_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℤ) (m : ℕ) (z1 : GaussianInt),
      0 ≤ R → 1 ≤ m → IsCoprime z1.re z1.im →
      (R : ℝ) ^ 2 ≤ 4 * (Work.FIPlan.gnorm z1 : ℝ) →
      (Work.FIPlan.gnorm z1 : ℝ) ≤ 4 * ((R : ℝ) + 1) ^ 2 →
      (((Work.FIPlan.gBox R).filter (fun z2 => (m : ℤ) ∣ (star z1 * z2).im)).card : ℝ)
        ≤ C * (((2 * (R : ℝ) + 1) ^ 2) / (m : ℝ) + 1) := by
  refine ⟨40, by norm_num, ?_⟩
  intro R m z1 hR hm hcop hlow hhigh
  have hR' : (0:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
  have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  by_cases hR2 : R ≤ 2
  · have hcard := Finset.card_filter_le (Work.FIPlan.gBox R)
      (fun z2 : GaussianInt => (m:ℤ) ∣ (star z1 * z2).im)
    rw [gBox_card_eq] at hcard
    have hle25 : (2 * R + 1).toNat ≤ 5 := by
      have h1 : (2 * R + 1 : ℤ) ≤ 5 := by omega
      calc (2 * R + 1).toNat ≤ (5 : ℤ).toNat := Int.toNat_le_toNat h1
        _ = 5 := by decide
    have hcard25 : (((Work.FIPlan.gBox R).filter
        (fun z2 => (m:ℤ) ∣ (star z1 * z2).im)).card : ℝ) ≤ 25 := by
      have h1 : (((Work.FIPlan.gBox R).filter
          (fun z2 => (m:ℤ) ∣ (star z1 * z2).im)).card : ℝ)
          ≤ ((2 * R + 1).toNat : ℝ) ^ 2 := by exact_mod_cast hcard
      have h2 : ((2 * R + 1).toNat : ℝ) ≤ 5 := by exact_mod_cast hle25
      have h2' : (0:ℝ) ≤ ((2 * R + 1).toNat : ℝ) := by positivity
      nlinarith [h1, h2, h2']
    have hX : (0:ℝ) ≤ ((2 * (R:ℝ) + 1) ^ 2) / (m:ℝ) :=
      div_nonneg (sq_nonneg _) (by positivity)
    nlinarith [hcard25, hX]
  · push_neg at hR2
    have hr : z1.re ≠ 0 := by
      intro h0
      obtain ⟨x, y, hxy⟩ := hcop
      rw [h0, mul_zero, zero_add] at hxy
      have hdvd : z1.im ∣ (1:ℤ) := ⟨y, by rw [mul_comm]; exact hxy.symm⟩
      have hunit : z1.im = 1 ∨ z1.im = -1 := Int.isUnit_iff.mp (isUnit_iff_dvd_one.mpr hdvd)
      have hgnint : (Work.FIPlan.gnorm z1 : ℤ) = 1 := by
        have h := Work.FIArea7.norm_eq z1
        rw [h0] at h
        rcases hunit with h1 | h1 <;> rw [h1] at h <;> nlinarith [h]
      have hgn : (Work.FIPlan.gnorm z1 : ℝ) = 1 := by
        have h3 : Work.FIPlan.gnorm z1 = 1 := by exact_mod_cast hgnint
        rw [h3]; norm_num
      rw [hgn] at hlow
      have hRle : (R:ℝ) ≤ 2 := by nlinarith [hlow, hR']
      have hgt : (2:ℝ) < (R:ℝ) := by exact_mod_cast hR2
      linarith
    have hLpos : 0 < ‖z1.toComplex‖ := by
      have hz1ne : z1 ≠ 0 := by intro h; exact hr (by rw [h]; simp)
      have hgnpos : (0:ℝ) < (Work.FIPlan.gnorm z1 : ℝ) := by
        exact_mod_cast Work.FIArea7.gnorm_pos_of_ne_zero hz1ne
      rw [Work.FIArea4.norm_toComplex_eq_sqrt_gnorm]
      exact Real.sqrt_pos_of_pos hgnpos
    have hSd0 : 0 ≤ (((|z1.re| + |z1.im| : ℤ) : ℝ)) := by
      have : (0:ℤ) ≤ |z1.re| + |z1.im| := add_nonneg (abs_nonneg _) (abs_nonneg _)
      exact_mod_cast this
    have hLR : (R:ℝ) ≤ 2 * ‖z1.toComplex‖ := by
      have hsq : (R:ℝ) ^ 2 ≤ (2 * ‖z1.toComplex‖) ^ 2 := by
        rw [mul_pow, Work.FIArea4.normSq_toComplex_gnorm]
        linarith [hlow]
      have h1 := sq_le_sq.mp hsq
      rw [abs_of_nonneg hR', abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ‖z1.toComplex‖)] at h1
      exact h1
    have hLS : ‖z1.toComplex‖ ≤ 2 * ((R:ℝ) + 1) := by
      have hsq : ‖z1.toComplex‖ ^ 2 ≤ (2 * ((R:ℝ) + 1)) ^ 2 := by
        rw [Work.FIArea4.normSq_toComplex_gnorm]
        nlinarith [hhigh]
      have h1 := sq_le_sq.mp hsq
      rw [abs_of_nonneg (norm_nonneg _),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * ((R:ℝ)+1))] at h1
      exact h1
    have hSdL : (((|z1.re| + |z1.im| : ℤ) : ℝ)) ≤ Real.sqrt 2 * ‖z1.toComplex‖ := by
      have hsq : (((|z1.re| + |z1.im| : ℤ) : ℝ)) ^ 2
          ≤ (Real.sqrt 2 * ‖z1.toComplex‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
          Work.FIArea4.normSq_toComplex_gnorm]
        have hcast : (((|z1.re| + |z1.im| : ℤ) : ℝ))
            = |((z1.re : ℤ) : ℝ)| + |((z1.im : ℤ) : ℝ)| := by push_cast; ring
        have hZ : (z1.re : ℤ) ^ 2 + (z1.im : ℤ) ^ 2 = ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) := by
          rw [← Work.FIArea7.norm_eq z1]
        have hsq2 : ((z1.re : ℤ) : ℝ) ^ 2 + ((z1.im : ℤ) : ℝ) ^ 2
            = ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) := by exact_mod_cast hZ
        rw [hcast, ← hsq2]
        nlinarith [sq_nonneg (|((z1.re : ℤ) : ℝ)| - |((z1.im : ℤ) : ℝ)|),
          sq_abs ((z1.re : ℤ) : ℝ), sq_abs ((z1.im : ℤ) : ℝ),
          abs_nonneg ((z1.re : ℤ) : ℝ), abs_nonneg ((z1.im : ℤ) : ℝ)]
      have h1 := sq_le_sq.mp hsq
      rw [abs_of_nonneg hSd0,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.sqrt 2 * ‖z1.toComplex‖)] at h1
      exact h1
    have hcount := card_gBox_filter_dvd_Delta_le z1 R m hR hm hr hcop
    have hgroup : (4 * Real.sqrt 2 * (R:ℝ) / ‖z1.toComplex‖ + 1)
        * (2 * (((|z1.re| + |z1.im| : ℤ) : ℝ) * (R:ℝ) / (m:ℝ)) + 1)
        = (4 * Real.sqrt 2 * (R:ℝ) / ‖z1.toComplex‖ + 1)
          * (2 * ((|z1.re| + |z1.im| : ℤ) : ℝ) * (R:ℝ) / (m:ℝ) + 1) := by ring
    rw [hgroup] at hcount
    exact le_trans hcount
      (dvd_im_gBox_arith (R := (R:ℝ)) (m := (m:ℝ)) (L := ‖z1.toComplex‖)
        (Sd := ((|z1.re| + |z1.im| : ℤ) : ℝ))
        hR' hmR hLpos hSd0 hLR hLS hSdL le_rfl)

end

end Work.FIArea7
