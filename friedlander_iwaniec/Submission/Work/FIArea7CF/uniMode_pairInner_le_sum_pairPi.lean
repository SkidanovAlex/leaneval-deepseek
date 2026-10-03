/-
# `Submission.Work.FIArea7CF.uniMode_pairInner_le_sum_pairPi` — clash-free copy of `Submission.Work.FIArea7.uniMode_pairInner_le_sum_pairPi`

Imports redirected to the `FIArea7CF` copies; renamed: mem_gBox_iff→ump_mem_gBox_iff.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.PiPairDefs
import Submission.Work.FIArea7.UniPairMassDefs
import Submission.Work.FITop4.Defs6
import Submission.Commons.NumberTheory.GaussianInt.units_classification

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Elementary facts about `gnorm`, `gBox` and units -/

/-- `radN` is non-negative. -/
lemma radN_nonneg (Pa : Work.FITop.Params) : 0 ≤ Work.FITop.radN Pa := by
  rw [Work.FITop.radN]
  exact Int.natCast_nonneg _

/-- Membership in the coordinate box `gBox R`. -/
lemma ump_mem_gBox_iff {R : ℤ} {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ -R ≤ z.re ∧ z.re ≤ R ∧ -R ≤ z.im ∧ z.im ≤ R := by
  rw [Work.FIPlan.gBox, Finset.product_eq_sprod, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hpe⟩
    simp only [Finset.mem_product, Finset.mem_Icc] at hp
    rw [← hpe]
    exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(z.re, z.im), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

/-- `gnorm z = 0` exactly for `z = 0`. -/
lemma upi_gnorm_eq_zero_iff {z : GaussianInt} : Work.FIPlan.gnorm z = 0 ↔ z = 0 := by
  simp only [Work.FIPlan.gnorm, Int.natAbs_eq_zero, GaussianInt.norm_eq_zero]

/-- `gnorm` is monotone for divisibility. -/
lemma gnorm_dvd_of_dvd {e w : GaussianInt} (h : e ∣ w) :
    Work.FIPlan.gnorm e ∣ Work.FIPlan.gnorm w := by
  obtain ⟨c, rfl⟩ := h
  rw [Work.FIArea7.gnorm_mul]
  exact ⟨Work.FIPlan.gnorm c, rfl⟩

/-- The real part of a Gaussian integer is bounded by its norm. -/
lemma sq_re_le_gnorm (z : GaussianInt) : z.re ^ 2 ≤ ((Work.FIPlan.gnorm z : ℕ) : ℤ) := by
  have h := Work.FIArea7.norm_eq z
  linarith [sq_nonneg z.im]

/-- The imaginary part of a Gaussian integer is bounded by its norm. -/
lemma sq_im_le_gnorm (z : GaussianInt) : z.im ^ 2 ≤ ((Work.FIPlan.gnorm z : ℕ) : ℤ) := by
  have h := Work.FIArea7.norm_eq z
  linarith [sq_nonneg z.re]

/-- Associates have equal norm. -/
lemma gnorm_eq_of_associated {z w : GaussianInt} (h : Associated z w) :
    Work.FIPlan.gnorm z = Work.FIPlan.gnorm w := by
  obtain ⟨u, hu⟩ := h
  have hu1 : Work.FIPlan.gnorm (↑u : GaussianInt) = 1 :=
    Zsqrtd.norm_eq_one_iff.mpr u.isUnit
  rw [← hu, Work.FIArea7.gnorm_mul, hu1, mul_one]

/-- The unit `i` of `ℤ[i]`. -/
lemma isUnit_I : IsUnit (⟨0, 1⟩ : GaussianInt) := by
  rw [← Zsqrtd.norm_eq_one_iff (x := (⟨0, 1⟩ : GaussianInt))]
  decide

/-- The unit `-i` of `ℤ[i]`. -/
lemma isUnit_neg_I : IsUnit (⟨0, -1⟩ : GaussianInt) := by
  rw [← Zsqrtd.norm_eq_one_iff (x := (⟨0, -1⟩ : GaussianInt))]
  decide

/-! ## 2. The canonical quadrant -/

/-- Every non-zero Gaussian integer is associate to an element of the closed quadrant
`{0 < re, 0 ≤ im}` — the quadrant used by `bigPi`. -/
theorem quadAssoc_quadrant {z : GaussianInt} (hz : z ≠ 0) :
    ∃ w : GaussianInt, Associated w z ∧ 0 < w.re ∧ 0 ≤ w.im
      ∧ Work.FIPlan.gnorm w = Work.FIPlan.gnorm z := by
  have hI := isUnit_I
  have hnI := isUnit_neg_I
  have hI_re : (z * (⟨0, 1⟩ : GaussianInt)).re = -z.im := by simp [Zsqrtd.re_mul]
  have hI_im : (z * (⟨0, 1⟩ : GaussianInt)).im = z.re := by simp [Zsqrtd.im_mul]
  have hnI_re : (z * (⟨0, -1⟩ : GaussianInt)).re = z.im := by simp [Zsqrtd.re_mul]
  have hnI_im : (z * (⟨0, -1⟩ : GaussianInt)).im = -z.re := by simp [Zsqrtd.im_mul]
  have hm1_re : (z * (-1 : GaussianInt)).re = -z.re := by simp [Zsqrtd.re_mul]
  have hm1_im : (z * (-1 : GaussianInt)).im = -z.im := by simp [Zsqrtd.im_mul]
  rcases lt_or_ge (0 : ℤ) z.re with h1 | h1
  · rcases lt_or_ge (0 : ℤ) z.im with h2 | h2
    · exact ⟨z, Associated.refl z, h1, le_of_lt h2, rfl⟩
    · by_cases h2' : z.im = 0
      · exact ⟨z, Associated.refl z, h1, le_of_eq h2'.symm, rfl⟩
      · refine ⟨z * (⟨0, 1⟩ : GaussianInt), associated_mul_unit_left z _ hI, ?_, ?_, ?_⟩
        · rw [hI_re]; omega
        · rw [hI_im]; exact le_of_lt h1
        · exact gnorm_eq_of_associated (associated_mul_unit_left z _ hI)
  · rcases lt_or_ge (0 : ℤ) z.im with h2 | h2
    · refine ⟨z * (⟨0, -1⟩ : GaussianInt), associated_mul_unit_left z _ hnI, ?_, ?_, ?_⟩
      · rw [hnI_re]; exact h2
      · rw [hnI_im]; omega
      · exact gnorm_eq_of_associated (associated_mul_unit_left z _ hnI)
    · by_cases h1' : z.re = 0
      · have him0 : z.im ≠ 0 := by
          intro him
          refine hz ?_
          rw [Zsqrtd.ext_iff]
          exact ⟨by simpa using h1', by simpa using him⟩
        have h2lt : z.im < 0 := lt_of_le_of_ne h2 him0
        refine ⟨z * (⟨0, 1⟩ : GaussianInt), associated_mul_unit_left z _ hI, ?_, ?_, ?_⟩
        · rw [hI_re]; omega
        · rw [hI_im, h1']
        · exact gnorm_eq_of_associated (associated_mul_unit_left z _ hI)
      · have h1lt : z.re < 0 := lt_of_le_of_ne h1 h1'
        refine ⟨z * (-1 : GaussianInt), associated_mul_unit_left z _ (IsUnit.neg isUnit_one),
          ?_, ?_, ?_⟩
        · rw [hm1_re]; omega
        · rw [hm1_im]; omega
        · exact gnorm_eq_of_associated
            (associated_mul_unit_left z _ (IsUnit.neg isUnit_one))

/-! ## 3. Divisors of a box element -/

/-- A non-zero divisor lying in the canonical quadrant of a non-zero element of the box lies in the
box.  If the cofactor is not a unit then `|π|² ≤ |z|²/2 ≤ R²` and the coordinates of `π` are bounded
by `|π|`; if the cofactor is a unit then `π` is an associate of `z` and its coordinates are signed
permutations of those of `z`. -/
theorem divisor_mem_gBox_of_box {R : ℤ} (hR : 0 ≤ R) {π z : GaussianInt}
    (hz : z ∈ Work.FIPlan.gBox R) (hz0 : z ≠ 0) (hπ0 : π ≠ 0) (hdvd : π ∣ z)
    (hre : 0 < π.re) (him : 0 ≤ π.im) : π ∈ Work.FIPlan.gBox R := by
  obtain ⟨hzre1, hzre2, hzim1, hzim2⟩ := ump_mem_gBox_iff.mp hz
  obtain ⟨w, hw⟩ := hdvd
  have hw0 : w ≠ 0 := by
    intro h
    exact hz0 (by rw [hw, h, mul_zero])
  have hgn : Work.FIPlan.gnorm z = Work.FIPlan.gnorm π * Work.FIPlan.gnorm w := by
    rw [hw, Work.FIArea7.gnorm_mul]
  have hzsq : ((Work.FIPlan.gnorm z : ℕ) : ℤ) ≤ 2 * R ^ 2 := by
    rw [Work.FIArea7.norm_eq]
    nlinarith
  have hgw0 : Work.FIPlan.gnorm w ≠ 0 := fun hh => hw0 (upi_gnorm_eq_zero_iff.mp hh)
  by_cases hcase : 2 ≤ Work.FIPlan.gnorm w
  · have hπsq : ((Work.FIPlan.gnorm π : ℕ) : ℤ) ≤ R ^ 2 := by
      have h1 : ((Work.FIPlan.gnorm π : ℕ) : ℤ) * ((Work.FIPlan.gnorm w : ℕ) : ℤ)
          ≤ ((Work.FIPlan.gnorm z : ℕ) : ℤ) := by rw [hgn, Nat.cast_mul]
      have h2 : (2 : ℤ) ≤ ((Work.FIPlan.gnorm w : ℕ) : ℤ) := by exact_mod_cast hcase
      have h3 : (0 : ℤ) ≤ ((Work.FIPlan.gnorm π : ℕ) : ℤ) := Nat.cast_nonneg _
      nlinarith
    have hre_le : π.re ≤ R := le_of_sq_le_sq (le_trans (sq_re_le_gnorm π) hπsq) hR
    have him_le : π.im ≤ R := le_of_sq_le_sq (le_trans (sq_im_le_gnorm π) hπsq) hR
    rw [ump_mem_gBox_iff]
    exact ⟨by linarith, hre_le, by linarith, him_le⟩
  · have hw1 : Work.FIPlan.gnorm w = 1 := by omega
    have hunit : IsUnit w := by
      rw [← Zsqrtd.norm_eq_one_iff (x := w)]
      exact hw1
    rw [Commons.NumberTheory.GaussianInt.units_classification w] at hunit
    rcases hunit with h1 | h1 | h1 | h1
    · have hze : z.re = π.re := by rw [hw, h1, mul_one]
      have hzi : z.im = π.im := by rw [hw, h1, mul_one]
      rw [hze] at hzre1 hzre2
      rw [hzi] at hzim1 hzim2
      rw [ump_mem_gBox_iff]
      exact ⟨hzre1, hzre2, hzim1, hzim2⟩
    · have hze : z.re = -π.re := by rw [hw, h1]; simp [Zsqrtd.re_mul]
      have hzi : z.im = -π.im := by rw [hw, h1]; simp [Zsqrtd.im_mul]
      rw [hze] at hzre1 hzre2
      rw [hzi] at hzim1 hzim2
      rw [ump_mem_gBox_iff]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · have hze : z.re = -π.im := by rw [hw, h1]; simp [Zsqrtd.re_mul]
      have hzi : z.im = π.re := by rw [hw, h1]; simp [Zsqrtd.im_mul]
      rw [hze] at hzre1 hzre2
      rw [hzi] at hzim1 hzim2
      rw [ump_mem_gBox_iff]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · have hze : z.re = π.im := by rw [hw, h1]; simp [Zsqrtd.re_mul]
      have hzi : z.im = -π.re := by rw [hw, h1]; simp [Zsqrtd.im_mul]
      rw [hze] at hzre1 hzre2
      rw [hzi] at hzim1 hzim2
      rw [ump_mem_gBox_iff]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ## 4. The sublattice box -/

/-- If `n²·N(π) ≤ 2R²` (in `ℝ`) then `n ≤ shrunkNat R π`. -/
lemma natAbs_le_shrunkNat_of_sq {R : ℤ} (hR : 0 ≤ R) {π : GaussianInt} (hπ : π ≠ 0) {n : ℕ}
    (h : ((n : ℝ)) ^ 2 * ((Work.FIPlan.gnorm π : ℕ) : ℝ) ≤ 2 * (R : ℝ) ^ 2) :
    n ≤ Work.FIArea7.shrunkNat R π := by
  set g : ℝ := ((Work.FIPlan.gnorm π : ℕ) : ℝ) with hgdef
  have hgpos : 0 < g := by
    have h0 : Work.FIPlan.gnorm π ≠ 0 := fun hh => hπ (upi_gnorm_eq_zero_iff.mp hh)
    rw [hgdef]
    exact_mod_cast Nat.pos_of_ne_zero h0
  have h1 : ((n : ℝ) * Real.sqrt g) ^ 2 ≤ (R * Real.sqrt 2) ^ 2 := by
    have h2 : Real.sqrt g ^ 2 = g := Real.sq_sqrt (le_of_lt hgpos)
    have h3 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have h4 : ((n : ℝ) * Real.sqrt g) ^ 2 = ((n : ℝ)) ^ 2 * g := by
      rw [mul_pow, h2]
    have h5 : (R * Real.sqrt 2) ^ 2 = 2 * (R : ℝ) ^ 2 := by
      rw [mul_pow, h3]; ring
    rw [h4, h5]
    exact h
  have h6 : (n : ℝ) * Real.sqrt g ≤ R * Real.sqrt 2 :=
    le_of_sq_le_sq h1 (by positivity)
  have h7 : (n : ℝ) ≤ (R : ℝ) * Real.sqrt 2 / Real.sqrt g := by
    rw [le_div_iff₀ (Real.sqrt_pos.mpr hgpos)]
    exact h6
  have h8 : n ≤ Nat.floor ((R : ℝ) * Real.sqrt 2 / Real.sqrt g) := Nat.le_floor h7
  have h9 : Nat.floor ((R : ℝ) * Real.sqrt 2 / Real.sqrt g)
      = Work.FIArea7.shrunkNat R π := by
    rw [Work.FIArea7.shrunkNat, hgdef]
  rwa [h9] at h8

/-- If `n²·N(π) ≤ 2R²` (in `ℤ`) then `n ≤ shrunkNat R π`. -/
lemma nat_le_shrunkNat_of_sq {R : ℤ} (hR : 0 ≤ R) {π : GaussianInt} (hπ : π ≠ 0) {n : ℕ}
    (h : (((n : ℕ)) : ℤ) ^ 2 * ((Work.FIPlan.gnorm π : ℕ) : ℤ) ≤ 2 * R ^ 2) :
    n ≤ Work.FIArea7.shrunkNat R π := by
  have h' : (((n : ℕ)) : ℝ) ^ 2 * ((Work.FIPlan.gnorm π : ℕ) : ℝ) ≤ 2 * (R : ℝ) ^ 2 := by
    exact_mod_cast h
  exact natAbs_le_shrunkNat_of_sq hR hπ h'

/-- The `π`-sublattice points of the box: if `π w = z` with `z` in the box, then `w` is in the
box of radius `shrunkNat R π`. -/
theorem mem_gBox_shrunkNat {R : ℤ} (hR : 0 ≤ R) {π w z : GaussianInt} (hπ : π ≠ 0)
    (hmul : π * w = z) (hz : z ∈ Work.FIPlan.gBox R) :
    w ∈ Work.FIPlan.gBox ((Work.FIArea7.shrunkNat R π : ℕ) : ℤ) := by
  obtain ⟨hzre1, hzre2, hzim1, hzim2⟩ := ump_mem_gBox_iff.mp hz
  have hzsq : ((Work.FIPlan.gnorm z : ℕ) : ℤ) ≤ 2 * R ^ 2 := by
    rw [Work.FIArea7.norm_eq]
    nlinarith
  have hgn : Work.FIPlan.gnorm z = Work.FIPlan.gnorm π * Work.FIPlan.gnorm w := by
    rw [← hmul, Work.FIArea7.gnorm_mul]
  have hgw : ((Work.FIPlan.gnorm π : ℕ) : ℤ) * ((Work.FIPlan.gnorm w : ℕ) : ℤ)
      = ((Work.FIPlan.gnorm z : ℕ) : ℤ) := by rw [hgn, Nat.cast_mul]
  have hbound : ∀ c : ℤ, c ^ 2 ≤ ((Work.FIPlan.gnorm w : ℕ) : ℤ) →
      (c.natAbs : ℤ) ≤ (Work.FIArea7.shrunkNat R π : ℤ) := by
    intro c hc
    have h1 : (((c.natAbs : ℕ)) : ℤ) ^ 2 * ((Work.FIPlan.gnorm π : ℕ) : ℤ) ≤ 2 * R ^ 2 := by
      have hsq : (((c.natAbs : ℕ)) : ℤ) ^ 2 = c ^ 2 := by
        rw [Int.natCast_natAbs, sq_abs]
      rw [hsq]
      have h3 : c ^ 2 * ((Work.FIPlan.gnorm π : ℕ) : ℤ)
          ≤ ((Work.FIPlan.gnorm w : ℕ) : ℤ) * ((Work.FIPlan.gnorm π : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)
      have h4 : ((Work.FIPlan.gnorm w : ℕ) : ℤ) * ((Work.FIPlan.gnorm π : ℕ) : ℤ)
          ≤ 2 * R ^ 2 := by rw [mul_comm, hgw]; exact hzsq
      linarith
    have hle := nat_le_shrunkNat_of_sq hR hπ h1
    exact_mod_cast hle
  have hrew : |w.re| ≤ (Work.FIArea7.shrunkNat R π : ℤ) := by
    have h := hbound w.re (sq_re_le_gnorm w)
    rwa [Int.natCast_natAbs] at h
  have himw : |w.im| ≤ (Work.FIArea7.shrunkNat R π : ℤ) := by
    have h := hbound w.im (sq_im_le_gnorm w)
    rwa [Int.natCast_natAbs] at h
  obtain ⟨h1, h2⟩ := abs_le.mp hrew
  obtain ⟨h3, h4⟩ := abs_le.mp himw
  rw [ump_mem_gBox_iff]
  exact ⟨h1, h2, h3, h4⟩

/-! ## 5. The common Gaussian prime of a non-coprime pair -/

/-- A pair of the box with `β z₁ ≠ 0` whose elements are not coprime shares a Gaussian prime `π` of
the canonical quadrant, of norm `> Pz`, coprime to `4be` and lying in the box, i.e. a common prime
of the covering `bigPi Pa (4be)`. -/
theorem exists_bigPi_dvd_pair {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (b e : ℕ)
    {z1 z2 : GaussianInt} (hz1 : z1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa))
    (h1 : β z1 ≠ 0) (hnc : ¬ Work.FIPlan.GaussCoprime z1 z2)
    (hc1 : Nat.Coprime (Work.FIPlan.gnorm z1) (4 * b * e)) :
    ∃ t : GaussianInt × GaussianInt × GaussianInt,
      t.1 ∈ Work.FIArea7.bigPi Pa (4 * b * e) ∧ t.1 * t.2.1 = z1 ∧ t.1 * t.2.2 = z2 := by
  have hpol : Work.FITop3.InPolarBox Pa φ z1 := hβ.support h1
  have hns : Work.FITop3.NoSmallPrimes Pa z1 := hβ.noSmallPrimes h1
  have hz1' : z1 ≠ 0 := by
    intro h0
    have hprim : Work.FIPlan.IsPrimary z1 := hpol.1
    rw [h0] at hprim
    exact Work.FIArea7.IsPrimary.re_ne_zero hprim (by simp)
  -- a common Gaussian prime of norm `> Pz` (5.8)
  have hexp : ∃ π0 : GaussianInt,
      Prime π0 ∧ π0 ∣ z1 ∧ π0 ∣ z2 ∧ Pa.Pz < Work.FIPlan.gnorm π0 := by
    have hnc' : ¬ IsCoprime z1 z2 := hnc
    have hex : ∃ d : GaussianInt, d ∣ z1 ∧ d ∣ z2 ∧ ¬ IsUnit d := by
      rw [← isRelPrime_iff_isCoprime] at hnc'
      rw [IsRelPrime] at hnc'
      push Not at hnc'
      exact hnc'
    obtain ⟨d, hd1, hd2, hdu⟩ := hex
    have hd0 : d ≠ 0 := by
      intro hd
      obtain ⟨k, hk⟩ := hd1
      rw [hd, zero_mul] at hk
      exact hz1' hk
    obtain ⟨π0, hirr, hπ0d⟩ := WfDvdMonoid.exists_irreducible_factor hdu hd0
    have hπ0prime : Prime π0 := hirr.prime
    refine ⟨π0, hπ0prime, hπ0d.trans hd1, hπ0d.trans hd2, ?_⟩
    have hπ0ne : π0 ≠ 0 := hπ0prime.ne_zero
    have hgn0 : Work.FIPlan.gnorm π0 ≠ 0 := fun hh => hπ0ne (upi_gnorm_eq_zero_iff.mp hh)
    have hgn1 : Work.FIPlan.gnorm π0 ≠ 1 := fun hh =>
      hπ0prime.not_isUnit
        (Zsqrtd.norm_eq_one_iff.mp (show (Zsqrtd.norm π0).natAbs = 1 from hh))
    obtain ⟨q, hqprime, hqπ⟩ := Nat.exists_prime_and_dvd hgn1
    have hvd : Work.FIPlan.gnorm π0 ∣ Work.FIPlan.gnorm z1 :=
      gnorm_dvd_of_dvd (hπ0d.trans hd1)
    have hqvd : q ∣ Work.FIPlan.gnorm z1 := hqπ.trans hvd
    have hqP : Pa.Pz < q := by
      by_contra hle
      exact hns q hqprime (le_of_not_gt hle) hqvd
    exact lt_of_lt_of_le hqP (Nat.le_of_dvd (Nat.pos_of_ne_zero hgn0) hqπ)
  obtain ⟨π0, hπ0prime, hπ0d1, hπ0d2, hPz⟩ := hexp
  -- rotate into the canonical quadrant
  obtain ⟨π, hπassoc, hπre, hπim, hπgn⟩ := quadAssoc_quadrant hπ0prime.ne_zero
  have hπprime : Prime π := hπassoc.symm.prime hπ0prime
  have hπd1 : π ∣ z1 := (Associated.dvd_iff_dvd_left hπassoc).mpr hπ0d1
  have hπd2 : π ∣ z2 := (Associated.dvd_iff_dvd_left hπassoc).mpr hπ0d2
  have hPzπ : Pa.Pz < Work.FIPlan.gnorm π := by rw [hπgn]; exact hPz
  have hcopπ : Nat.Coprime (Work.FIPlan.gnorm π) (4 * b * e) := by
    rw [hπgn]
    exact Nat.Coprime.coprime_dvd_left (gnorm_dvd_of_dvd hπ0d1) hc1
  have hπbox : π ∈ Work.FIPlan.gBox (Work.FITop.radN Pa) :=
    divisor_mem_gBox_of_box (radN_nonneg Pa) hz1 hz1' hπprime.ne_zero hπd1 hπre hπim
  have hπbig : π ∈ bigPi Pa (4 * b * e) := by
    rw [bigPi, Finset.mem_filter]
    exact ⟨hπbox, hπprime, hπre, hπim, hPzπ, hcopπ⟩
  obtain ⟨u, hu⟩ := hπd1
  obtain ⟨v, hv⟩ := hπd2
  refine ⟨(π, u, v), hπbig, ?_, ?_⟩
  · simpa using hu.symm
  · simpa using hv.symm

/-! ## 6. The `π`-sublattice -/

/-- A quotient of a box element by a non-zero divisor whose norm is coprime to `m` lies in the
`π`-sublattice `piBox Pa π m`. -/
theorem mem_piBox_of_mul_mem {Pa : Work.FITop.Params} {π u z : GaussianInt} {m : ℕ}
    (hπ0 : π ≠ 0) (hmul : π * u = z) (hz : z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa))
    (hco : Nat.Coprime (Work.FIPlan.gnorm z) m) : u ∈ piBox Pa π m := by
  rw [piBox, Finset.mem_filter, Finset.mem_filter]
  refine ⟨⟨mem_gBox_shrunkNat (radN_nonneg Pa) hπ0 hmul hz, ?_⟩, ?_⟩
  · rw [hmul]; exact hz
  · have hg : Work.FIPlan.gnorm z = Work.FIPlan.gnorm π * Work.FIPlan.gnorm u := by
      rw [← hmul, Work.FIArea7.gnorm_mul]
    refine Nat.Coprime.coprime_dvd_left ?_ hco
    rw [hg]
    exact ⟨Work.FIPlan.gnorm π, by rw [mul_comm]⟩

/-! ## 7. The pair mass is covered by the `π`-parts -/

def pairCond (b e : ℕ) (p : GaussianInt × GaussianInt) : Prop :=
  ¬ Work.FIPlan.GaussCoprime p.1 p.2
    ∧ Nat.Coprime (Work.FIPlan.gnorm p.1) (4 * b * e)
    ∧ Nat.Coprime (Work.FIPlan.gnorm p.2) (4 * b * e)
    ∧ 4 * b * e ∣ Work.FIPlan.absDelta p.1 p.2

/-- The integrand of `uniMode_pairInner` as a function of the pair. -/
def pairWeight (b e : ℕ) (β : GaussianInt → ℂ) (p : GaussianInt × GaussianInt) : ℝ :=
  if pairCond b e p then ‖β p.1‖ * ‖β p.2‖ else 0

/-- `pairWeight` with the vanishing of the coefficient made explicit. -/
lemma pairWeight_eq_ite (b e : ℕ) (β : GaussianInt → ℂ) (p : GaussianInt × GaussianInt) :
    pairWeight b e β p
      = (if pairCond b e p ∧ β p.1 ≠ 0 ∧ β p.2 ≠ 0
          then ‖β p.1‖ * ‖β p.2‖ else 0) := by
  by_cases hc : pairCond b e p
  · by_cases h1 : β p.1 = 0
    · have hq : ¬ (pairCond b e p ∧ β p.1 ≠ 0 ∧ β p.2 ≠ 0) := fun hh => hh.2.1 h1
      rw [pairWeight, if_pos hc, if_neg hq]
      rw [h1, norm_zero, zero_mul]
    · by_cases h2 : β p.2 = 0
      · have hq : ¬ (pairCond b e p ∧ β p.1 ≠ 0 ∧ β p.2 ≠ 0) := fun hh => hh.2.2 h2
        rw [pairWeight, if_pos hc, if_neg hq]
        rw [h2, norm_zero, mul_zero]
      · have hq : pairCond b e p ∧ β p.1 ≠ 0 ∧ β p.2 ≠ 0 := ⟨hc, h1, h2⟩
        rw [pairWeight, if_pos hc, if_pos hq]
  · have hq : ¬ (pairCond b e p ∧ β p.1 ≠ 0 ∧ β p.2 ≠ 0) := fun hh => hc hh.1
    rw [pairWeight, if_neg hc, if_neg hq]

/-- The integrand of `pairPi` as a function of the pair `(w₁,w₂)`. -/
def pairWeightPi (b e : ℕ) (β : GaussianInt → ℂ) (π : GaussianInt)
    (q : GaussianInt × GaussianInt) : ℝ :=
  if 4 * b * e ∣ Work.FIPlan.absDelta (π * q.1) (π * q.2)
    then ‖β (π * q.1)‖ * ‖β (π * q.2)‖ else 0

/-- The supported pairs of `uniMode_pairInner`: pairs of the box satisfying `pairCond` with both
coefficients non-zero. -/
def pairSupp (Pa : Work.FITop.Params) (b e : ℕ) (β : GaussianInt → ℂ) :
    Finset (GaussianInt × GaussianInt) :=
  ((Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ (Work.FIPlan.gBox (Work.FITop.radN Pa))).filter
    (fun p => pairCond b e p ∧ β p.1 ≠ 0 ∧ β p.2 ≠ 0)

lemma mem_pairSupp {Pa : Work.FITop.Params} {b e : ℕ} {β : GaussianInt → ℂ}
    {p : GaussianInt × GaussianInt} :
    p ∈ pairSupp Pa b e β ↔ p.1 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa)
      ∧ p.2 ∈ Work.FIPlan.gBox (Work.FITop.radN Pa)
      ∧ pairCond b e p ∧ β p.1 ≠ 0 ∧ β p.2 ≠ 0 := by
  rw [pairSupp, Finset.mem_filter, Finset.mem_product]
  tauto

/-- `pairPi` as a sum over the product of two copies of the `π`-sublattice. -/
lemma pairPi_eq_sum_product (Pa : Work.FITop.Params) (b e : ℕ) (β : GaussianInt → ℂ)
    (π : GaussianInt) :
    pairPi Pa b e β π
      = ∑ q ∈ (piBox Pa π (4 * b * e)) ×ˢ (piBox Pa π (4 * b * e)), pairWeightPi b e β π q := by
  simp only [pairPi, Finset.sum_product, pairWeightPi]

/-- The per-pair existence of the common prime and the two quotients, in the form used to define a
choice function on all pairs. -/
theorem pairPiData_exists (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (b e : ℕ)
    (p : GaussianInt × GaussianInt) :
    ∃ t : GaussianInt × GaussianInt × GaussianInt,
      p ∈ pairSupp Pa b e β →
        t.1 ∈ bigPi Pa (4 * b * e) ∧ t.1 * t.2.1 = p.1 ∧ t.1 * t.2.2 = p.2 := by
  by_cases hp : p ∈ pairSupp Pa b e β
  · obtain ⟨hbox1, hbox2, hcond, hb1, hb2⟩ := mem_pairSupp.mp hp
    obtain ⟨hgc, hcn1, hcn2, hdvd⟩ := hcond
    obtain ⟨t, ht⟩ := exists_bigPi_dvd_pair hβ b e hbox1 hb1 hgc hcn1
    exact ⟨t, fun _ => ht⟩
  · exact ⟨(1, 0, 0), fun h => absurd h hp⟩

/-- The chosen common prime of a pair, together with the two quotients. -/
noncomputable def pairPiData (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt)
    (β : GaussianInt → ℂ) (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (b e : ℕ)
    (p : GaussianInt × GaussianInt) : GaussianInt × GaussianInt × GaussianInt :=
  Classical.choose (pairPiData_exists Pa φ z0 β hβ b e p)

theorem pairPiData_spec {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (b e : ℕ)
    {p : GaussianInt × GaussianInt} (hp : p ∈ pairSupp Pa b e β) :
    (pairPiData Pa φ z0 β hβ b e p).1 ∈ bigPi Pa (4 * b * e)
      ∧ (pairPiData Pa φ z0 β hβ b e p).1 * (pairPiData Pa φ z0 β hβ b e p).2.1 = p.1
      ∧ (pairPiData Pa φ z0 β hβ b e p).1 * (pairPiData Pa φ z0 β hβ b e p).2.2 = p.2 :=
  (Classical.choose_spec (pairPiData_exists Pa φ z0 β hβ b e p)) hp

/-- **The pair mass of the guard removal is covered by the `π`-sublattice masses.** -/
theorem uniMode_pairInner_le_sum_pairPi {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β)
    (b e : ℕ) (hb : 1 ≤ b) (he : 1 ≤ e) :
    Work.FIArea7.uniMode_pairInner Pa b e β
      ≤ ∑ π ∈ Work.FIArea7.bigPi Pa (4 * b * e), Work.FIArea7.pairPi Pa b e β π := by
  classical
  have hLHS1 : Work.FIArea7.uniMode_pairInner Pa b e β
      = ∑ p ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ (Work.FIPlan.gBox (Work.FITop.radN Pa)),
          pairWeight b e β p := by
    unfold Work.FIArea7.uniMode_pairInner
    refine Eq.trans ?_ (Finset.sum_product (Work.FIPlan.gBox (Work.FITop.radN Pa))
      (Work.FIPlan.gBox (Work.FITop.radN Pa)) (pairWeight b e β)).symm
    refine Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun z2 _ => ?_))
    by_cases hc : pairCond b e (z1, z2)
    · have hcc : ¬ Work.FIPlan.GaussCoprime z1 z2
          ∧ Nat.Coprime (Work.FIPlan.gnorm z1) (4 * b * e)
          ∧ Nat.Coprime (Work.FIPlan.gnorm z2) (4 * b * e)
          ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 := by
        simpa [pairCond] using hc
      simp only [pairWeight, if_pos hc, if_pos hcc]
    · have hcc : ¬ (¬ Work.FIPlan.GaussCoprime z1 z2
          ∧ Nat.Coprime (Work.FIPlan.gnorm z1) (4 * b * e)
          ∧ Nat.Coprime (Work.FIPlan.gnorm z2) (4 * b * e)
          ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2) := by
        simpa [pairCond] using hc
      simp only [pairWeight, if_neg hc, if_neg hcc]
  have hLHS2 : (∑ p ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ
          (Work.FIPlan.gBox (Work.FITop.radN Pa)), pairWeight b e β p)
      = ∑ p ∈ pairSupp Pa b e β, ‖β p.1‖ * ‖β p.2‖ := by
    simp only [pairSupp]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p _ => pairWeight_eq_ite b e β p)
  have hfib : ∑ π ∈ bigPi Pa (4 * b * e),
        ∑ p ∈ (pairSupp Pa b e β).filter
          (fun p => (pairPiData Pa φ z0 β hβ b e p).1 = π), ‖β p.1‖ * ‖β p.2‖
      = ∑ p ∈ pairSupp Pa b e β, ‖β p.1‖ * ‖β p.2‖ :=
    Finset.sum_fiberwise_of_maps_to
      (s := pairSupp Pa b e β) (t := bigPi Pa (4 * b * e))
      (g := fun p => (pairPiData Pa φ z0 β hβ b e p).1)
      (f := fun p => ‖β p.1‖ * ‖β p.2‖)
      (fun p hp => (pairPiData_spec hβ b e hp).1)
  have hper : ∀ π ∈ bigPi Pa (4 * b * e),
      ∑ p ∈ (pairSupp Pa b e β).filter
          (fun p => (pairPiData Pa φ z0 β hβ b e p).1 = π),
        ‖β p.1‖ * ‖β p.2‖ ≤ pairPi Pa b e β π := by
    intro π hπ
    have hpt : ∀ p ∈ (pairSupp Pa b e β).filter
          (fun p => (pairPiData Pa φ z0 β hβ b e p).1 = π),
        ‖β p.1‖ * ‖β p.2‖
        = pairWeightPi b e β π ((pairPiData Pa φ z0 β hβ b e p).2.1,
            (pairPiData Pa φ z0 β hβ b e p).2.2) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpS, hpπ⟩ := hp
      obtain ⟨-, hs2, hs3⟩ := pairPiData_spec hβ b e hpS
      obtain ⟨-, -, hcond, -, -⟩ := mem_pairSupp.mp hpS
      obtain ⟨-, -, -, hdvd⟩ := hcond
      rw [hpπ] at hs2 hs3
      simp only [pairWeightPi]
      rw [if_pos (by rw [hs2, hs3]; exact hdvd), hs2, hs3]
    have hinj : Set.InjOn (fun p : GaussianInt × GaussianInt =>
        ((pairPiData Pa φ z0 β hβ b e p).2.1, (pairPiData Pa φ z0 β hβ b e p).2.2))
        ↑((pairSupp Pa b e β).filter
          (fun p => (pairPiData Pa φ z0 β hβ b e p).1 = π)) := by
      intro p hp q hq heq
      have hpT : p ∈ (pairSupp Pa b e β).filter
          (fun p => (pairPiData Pa φ z0 β hβ b e p).1 = π) := hp
      have hqT : q ∈ (pairSupp Pa b e β).filter
          (fun p => (pairPiData Pa φ z0 β hβ b e p).1 = π) := hq
      rw [Finset.mem_filter] at hpT hqT
      obtain ⟨hpS, hpπ⟩ := hpT
      obtain ⟨hqS, hqπ⟩ := hqT
      obtain ⟨-, hp2, hp3⟩ := pairPiData_spec hβ b e hpS
      obtain ⟨-, hq2, hq3⟩ := pairPiData_spec hβ b e hqS
      rw [hpπ] at hp2 hp3
      rw [hqπ] at hq2 hq3
      have h1 : p.1 = q.1 := by rw [← hp2, ← hq2, congrArg Prod.fst heq]
      have h2 : p.2 = q.2 := by rw [← hp3, ← hq3, congrArg Prod.snd heq]
      exact Prod.ext h1 h2
    have hsub : ((pairSupp Pa b e β).filter
          (fun p => (pairPiData Pa φ z0 β hβ b e p).1 = π)).image
          (fun p : GaussianInt × GaussianInt =>
            ((pairPiData Pa φ z0 β hβ b e p).2.1, (pairPiData Pa φ z0 β hβ b e p).2.2))
        ⊆ (piBox Pa π (4 * b * e)) ×ˢ (piBox Pa π (4 * b * e)) := by
      intro q hq
      rw [Finset.mem_image] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      rw [Finset.mem_filter] at hp
      obtain ⟨hpS, hpπ⟩ := hp
      obtain ⟨hs1, hs2, hs3⟩ := pairPiData_spec hβ b e hpS
      obtain ⟨hbox1, hbox2, hcond, -, -⟩ := mem_pairSupp.mp hpS
      obtain ⟨-, hcn1, hcn2, -⟩ := hcond
      rw [hpπ] at hs1 hs2 hs3
      rw [bigPi, Finset.mem_filter] at hs1
      obtain ⟨-, hprime, -, -, -, -⟩ := hs1
      rw [Finset.mem_product]
      exact ⟨mem_piBox_of_mul_mem hprime.ne_zero hs2 hbox1 hcn1,
        mem_piBox_of_mul_mem hprime.ne_zero hs3 hbox2 hcn2⟩
    calc ∑ p ∈ (pairSupp Pa b e β).filter
            (fun p => (pairPiData Pa φ z0 β hβ b e p).1 = π), ‖β p.1‖ * ‖β p.2‖
        = ∑ p ∈ (pairSupp Pa b e β).filter
              (fun p => (pairPiData Pa φ z0 β hβ b e p).1 = π),
            pairWeightPi b e β π ((pairPiData Pa φ z0 β hβ b e p).2.1,
              (pairPiData Pa φ z0 β hβ b e p).2.2) := Finset.sum_congr rfl hpt
      _ = ∑ q ∈ ((pairSupp Pa b e β).filter
              (fun p => (pairPiData Pa φ z0 β hβ b e p).1 = π)).image
              (fun p : GaussianInt × GaussianInt =>
                ((pairPiData Pa φ z0 β hβ b e p).2.1,
                  (pairPiData Pa φ z0 β hβ b e p).2.2)),
            pairWeightPi b e β π q := (Finset.sum_image hinj).symm
      _ ≤ ∑ q ∈ (piBox Pa π (4 * b * e)) ×ˢ (piBox Pa π (4 * b * e)),
            pairWeightPi b e β π q :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (by intro q _ _; simp only [pairWeightPi]; split <;> positivity)
      _ = pairPi Pa b e β π := (pairPi_eq_sum_product Pa b e β π).symm
  calc Work.FIArea7.uniMode_pairInner Pa b e β
      = ∑ p ∈ (Work.FIPlan.gBox (Work.FITop.radN Pa)) ×ˢ (Work.FIPlan.gBox (Work.FITop.radN Pa)),
          pairWeight b e β p := hLHS1
    _ = ∑ p ∈ pairSupp Pa b e β, ‖β p.1‖ * ‖β p.2‖ := hLHS2
    _ = ∑ π ∈ bigPi Pa (4 * b * e),
          ∑ p ∈ (pairSupp Pa b e β).filter
            (fun p => (pairPiData Pa φ z0 β hβ b e p).1 = π), ‖β p.1‖ * ‖β p.2‖ := hfib.symm
    _ ≤ ∑ π ∈ bigPi Pa (4 * b * e), pairPi Pa b e β π := Finset.sum_le_sum hper

end

end Work.FIArea7
