/-
# `Work.FIArea3.JointCount.card_filter_le_le_pieces`

The number of points of the polar box with `d ∣ |z₂|²` and `e ∣ Δ(z₁,z₂)` is at most the
sum, over the *maximal* Gaussian-divisor pieces `w` of `{z : ℤ[i] | d ∣ |z|²}`, of the number
of box points in the piece `w ℤ[i]` that also satisfy `e ∣ Δ(z₁,·)`.

The only mathematical content is the covering statement

  `d ∣ |z|²  →  ∃ w ∈ maxPieceFinset d, w ∣ z`,

which combines the descent `maximal_piece_cover` (existence of a maximal piece generator `w₀ ∣ z`)
with the normalization of `w₀` into the fundamental domain `{0 < Re, 0 ≤ Im}` of the unit group
of `ℤ[i]`.  The normalization is the (unique) associate `ε·w₀` with `ε` a unit; the key point is
that `GaussPieceMax` — hence membership in `maxPieceFinset` — is invariant under multiplication
by a unit.  That invariance is proved here through the exact unit-equivariance of the Euclidean
`gcd`/`lcm` of `ℤ[i]` (`gcd (εa) (εb) = ε · gcd a b`, `lcm (εa) (εb) = ε · lcm a b`), which
transports to `gaussPieceGen d (ε u) = ε · gaussPieceGen d u`.
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.countDefs
import Submission.Work.FIArea3.JointCount.maxPieceDefs
import Submission.Work.FIArea3.JointCount.GaussPieceMax_arith
import Submission.Work.FIArea3.JointCount.maximal_piece_cover

namespace Work.FIArea3.JointCount

open Finset Work.FIPlan

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 1. Unit-equivariance of the Euclidean `gcd`/`lcm` of `ℤ[i]` -/

/-- Division in `ℤ[i]` (rounding quotient) is equivariant under multiplication by a unit. -/
lemma div_unit_mul (u : GaussianInt) (hu : IsUnit u) (a b : GaussianInt) :
    (u * b) / (u * a) = b / a := by
  have hnu : Zsqrtd.norm u ≠ 0 := by
    intro h
    have h1 := (Zsqrtd.norm_eq_one_iff (d := -1) (x := u)).mpr hu
    rw [h] at h1; simp at h1
  have hnum : u * b * star (u * a) = (Zsqrtd.norm u : GaussianInt) * (b * star a) := by
    rw [star_mul]
    rw [show u * b * (star a * star u) = (u * star u) * (b * star a) by ring]
    rw [← Zsqrtd.norm_eq_mul_conj u]
  have hden : Zsqrtd.norm (u * a) = Zsqrtd.norm u * Zsqrtd.norm a := Zsqrtd.norm_mul u a
  rw [GaussianInt.div_def, GaussianInt.div_def]
  apply Zsqrtd.ext
  · rw [hnum, hden]
    simp only [Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, mul_zero, zero_mul, add_zero]
    push_cast
    rw [mul_div_mul_left _ _ (by exact_mod_cast hnu : (↑(Zsqrtd.norm u) : ℚ) ≠ 0)]
  · rw [hnum, hden]
    simp only [Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast, zero_mul, add_zero]
    push_cast
    rw [mul_div_mul_left _ _ (by exact_mod_cast hnu : (↑(Zsqrtd.norm u) : ℚ) ≠ 0)]

/-- The Euclidean `gcd` of `ℤ[i]` is equivariant under multiplication by a unit. -/
lemma gcd_unit_mul (u : GaussianInt) (hu : IsUnit u) (a b : GaussianInt) :
    EuclideanDomain.gcd (u * a) (u * b) = u * EuclideanDomain.gcd a b := by
  revert u
  refine EuclideanDomain.GCD.induction a b (fun x => ?_) (fun a b ha IH => ?_)
  · intro u hu; simp
  · intro u hu
    rw [EuclideanDomain.gcd_val (u * a) (u * b)]
    have hmod : (u * b) % (u * a) = u * (b % a) := by
      rw [GaussianInt.mod_def, GaussianInt.mod_def, div_unit_mul u hu a b]; ring
    rw [hmod, IH u hu, ← EuclideanDomain.gcd_val a b]

/-- The Euclidean `lcm` of `ℤ[i]` is equivariant under multiplication by a unit. -/
lemma lcm_unit_mul (u : GaussianInt) (hu : IsUnit u) (a b : GaussianInt) :
    EuclideanDomain.lcm (u * a) (u * b) = u * EuclideanDomain.lcm a b := by
  by_cases hg : EuclideanDomain.gcd a b = 0
  · rw [EuclideanDomain.gcd_eq_zero_iff] at hg
    obtain ⟨rfl, rfl⟩ := hg; simp
  · have hne : u * EuclideanDomain.gcd a b ≠ 0 := mul_ne_zero hu.ne_zero hg
    apply mul_left_cancel₀ hne
    calc u * EuclideanDomain.gcd a b * EuclideanDomain.lcm (u*a) (u*b)
        = EuclideanDomain.gcd (u*a) (u*b) * EuclideanDomain.lcm (u*a) (u*b) := by
          rw [gcd_unit_mul u hu a b]
      _ = u*a * (u*b) := EuclideanDomain.gcd_mul_lcm _ _
      _ = u * EuclideanDomain.gcd a b * (u * EuclideanDomain.lcm a b) := by
          rw [show u * a * (u * b) = u * u * (a * b) by ring,
              (EuclideanDomain.gcd_mul_lcm a b).symm]
          ring

/-! ## 2. Invariance of the piece vocabulary under units -/

/-- The Gaussian norm of a unit is `1`. -/
lemma gnorm_unit (ε : GaussianInt) (hε : IsUnit ε) : Work.FIPlan.gnorm ε = 1 := by
  unfold Work.FIPlan.gnorm
  exact (Zsqrtd.norm_eq_one_iff (d := -1) (x := ε)).mpr hε

/-- A unit of `ℤ[i]` is its own conjugate-inverse: `ε · star ε = 1`. -/
lemma unit_mul_star (ε : GaussianInt) (hε : IsUnit ε) : ε * star ε = 1 := by
  rw [mul_star_eq_gnorm, gnorm_unit ε hε]; simp

/-- Multiplication by a unit preserves the Gaussian norm. -/
lemma gnorm_unit_mul (ε w : GaussianInt) (hε : IsUnit ε) :
    Work.FIPlan.gnorm (ε * w) = Work.FIPlan.gnorm w := by
  rw [gnorm_mul, gnorm_unit ε hε, one_mul]

/-- The piece generator is equivariant under multiplication of the witnessing divisor by a
unit: `gaussPieceGen d (ε u) = ε · gaussPieceGen d u`. -/
lemma gaussPieceGen_unit_mul (d : ℕ) (hd : 1 ≤ d) (u : GaussianInt) (hu : u ∣ (d : GaussianInt))
    (ε : GaussianInt) (hε : IsUnit ε) :
    gaussPieceGen d (ε * u) = ε * gaussPieceGen d u := by
  have hdcast : (d : GaussianInt) ≠ 0 := by
    rw [show (d : GaussianInt) = ((d:ℤ):GaussianInt) by simp]
    exact_mod_cast (by omega : (d:ℤ) ≠ 0)
  have hu0 : u ≠ 0 := ne_zero_of_dvd_ne_zero hdcast hu
  have hεu0 : ε * u ≠ 0 := mul_ne_zero hε.ne_zero hu0
  have hεstar : ε * star ε = 1 := unit_mul_star ε hε
  have hmul : u * ((d : GaussianInt) / u) = (d : GaussianInt) :=
    EuclideanDomain.mul_div_cancel' hu0 hu
  have hdiv : (d : GaussianInt) / (ε * u) = ((d : GaussianInt) / u) * star ε :=
    (EuclideanDomain.eq_div_of_mul_eq_right hεu0
      (by calc (ε * u) * (((d : GaussianInt) / u) * star ε)
            = (u * ((d : GaussianInt) / u)) * (ε * star ε) := by ring
          _ = d := by rw [hmul, hεstar]; ring)).symm
  rw [gaussPieceGen, gaussPieceGen, hdiv, star_mul,
    show star (star ε) = ε by simp, lcm_unit_mul ε hε u (star ((d : GaussianInt) / u))]

/-- "Being a piece generator" is invariant under multiplication by a unit. -/
lemma IsPieceGen_unit_mul (d : ℕ) (hd : 1 ≤ d) {w : GaussianInt} (hw : IsPieceGen d w)
    (ε : GaussianInt) (hε : IsUnit ε) : IsPieceGen d (ε * w) := by
  obtain ⟨u, hu, hwu⟩ := hw
  refine ⟨ε * u, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := hu
    exact ⟨star ε * c, by
      rw [hc, show ε * u * (star ε * c) = (ε * star ε) * (u * c) by ring,
        unit_mul_star ε hε, one_mul]⟩
  · rw [hwu, gaussPieceGen_unit_mul d hd u hu ε hε]

/-- "Being a maximal piece generator" is invariant under multiplication by a unit. -/
lemma GaussPieceMax_unit_mul (d : ℕ) (hd : 1 ≤ d) {w : GaussianInt} (hw : GaussPieceMax d w)
    (ε : GaussianInt) (hε : IsUnit ε) : GaussPieceMax d (ε * w) := by
  refine ⟨IsPieceGen_unit_mul d hd hw.1 ε hε, ?_⟩
  have hew : ε * w ∣ w :=
    ⟨star ε, by rw [show ε * w * star ε = (ε * star ε) * w by ring, unit_mul_star ε hε, one_mul]⟩
  intro v hv hvw
  exact dvd_trans hew (hw.2 v hv (dvd_trans hvw hew))

/-! ## 3. Membership in the box `gBox d` from a norm bound -/

/-- Membership in the box `gBox R` is membership of both coordinates in `[-R,R]`. -/
lemma mem_gBox {R : ℤ} {w : GaussianInt} :
    w ∈ Work.FIPlan.gBox R ↔ w.re ∈ Finset.Icc (-R) R ∧ w.im ∈ Finset.Icc (-R) R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    exact ⟨h1, h2⟩
  · intro h
    exact ⟨(w.re, w.im), Finset.mem_product.mpr h, rfl⟩

/-- `|z|²` as a rational integer equals `re² + im²`. -/
lemma gnorm_eq (z : GaussianInt) : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  rw [Work.FIPlan.gnorm, Zsqrtd.norm]
  have h : (0 : ℤ) ≤ z.re * z.re - (-1) * z.im * z.im := by
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  rw [Int.natAbs_of_nonneg h]; ring

lemma re_sq_le_gnorm (u : GaussianInt) : (u.re : ℤ) ^ 2 ≤ (Work.FIPlan.gnorm u : ℤ) := by
  rw [gnorm_eq]; nlinarith [sq_nonneg u.im]

lemma im_sq_le_gnorm (u : GaussianInt) : (u.im : ℤ) ^ 2 ≤ (Work.FIPlan.gnorm u : ℤ) := by
  rw [gnorm_eq]; nlinarith [sq_nonneg u.re]

/-- A Gaussian-integer norm bound `|u|² ≤ d²` bounds both coordinates by `d`. -/
lemma gnorm_sq_bound {u : GaussianInt} {d : ℕ} (h : Work.FIPlan.gnorm u ≤ d * d) :
    (u.re : ℤ) ^ 2 ≤ (d : ℤ) ^ 2 ∧ (u.im : ℤ) ^ 2 ≤ (d : ℤ) ^ 2 := by
  have h3 : (Work.FIPlan.gnorm u : ℤ) ≤ (d:ℤ)^2 := by
    have : (d:ℤ)^2 = ((d*d : ℕ) : ℤ) := by push_cast; ring
    rw [this]; exact_mod_cast h
  exact ⟨le_trans (re_sq_le_gnorm u) h3, le_trans (im_sq_le_gnorm u) h3⟩

lemma abs_re_le_of_gnorm {u : GaussianInt} {d : ℕ} (h : Work.FIPlan.gnorm u ≤ d * d) :
    |u.re| ≤ (d : ℤ) := by
  have hd : (0:ℤ) ≤ (d:ℤ) := by exact_mod_cast Nat.zero_le d
  obtain ⟨h1, _⟩ := gnorm_sq_bound h
  rw [abs_le]; exact ⟨by nlinarith [h1, hd, sq_nonneg (u.re + (d:ℤ))],
                      by nlinarith [h1, hd, sq_nonneg (u.re - (d:ℤ))]⟩

lemma abs_im_le_of_gnorm {u : GaussianInt} {d : ℕ} (h : Work.FIPlan.gnorm u ≤ d * d) :
    |u.im| ≤ (d : ℤ) := by
  have hd : (0:ℤ) ≤ (d:ℤ) := by exact_mod_cast Nat.zero_le d
  obtain ⟨_, h2⟩ := gnorm_sq_bound h
  rw [abs_le]; exact ⟨by nlinarith [h2, hd, sq_nonneg (u.im + (d:ℤ))],
                      by nlinarith [h2, hd, sq_nonneg (u.im - (d:ℤ))]⟩

/-! ## 4. The fundamental-domain representative of an associate class -/

lemma re_I_mul (w : GaussianInt) : ((⟨0,1⟩ : GaussianInt) * w).re = -w.im := by simp [Zsqrtd.re_mul]
lemma im_I_mul (w : GaussianInt) : ((⟨0,1⟩ : GaussianInt) * w).im = w.re := by simp [Zsqrtd.im_mul]
lemma re_mI_mul (w : GaussianInt) : ((⟨0,-1⟩ : GaussianInt) * w).re = w.im := by simp [Zsqrtd.re_mul]
lemma im_mI_mul (w : GaussianInt) : ((⟨0,-1⟩ : GaussianInt) * w).im = -w.re := by simp [Zsqrtd.im_mul]
lemma re_neg1_mul (w : GaussianInt) : ((-1 : GaussianInt) * w).re = -w.re := by simp
lemma im_neg1_mul (w : GaussianInt) : ((-1 : GaussianInt) * w).im = -w.im := by simp

/-- Every nonzero Gaussian integer has an associate `ε w` (`ε` a unit of `ℤ[i]`) in the
fundamental domain `{0 < Re, 0 ≤ Im}` of the unit group `{±1, ±i}`. -/
lemma exists_unit_fundamental (w : GaussianInt) (hw : w ≠ 0) :
    ∃ ε : GaussianInt, IsUnit ε ∧ 0 < (ε * w).re ∧ 0 ≤ (ε * w).im := by
  have h1u : IsUnit (1 : GaussianInt) := isUnit_one
  have hm1u : IsUnit (-1 : GaussianInt) := isUnit_one.neg
  have hIu : IsUnit (⟨0,1⟩ : GaussianInt) := by
    rw [← Zsqrtd.norm_eq_one_iff (d := -1)]; decide
  have hmIu : IsUnit (⟨0,-1⟩ : GaussianInt) := by
    rw [← Zsqrtd.norm_eq_one_iff (d := -1)]; decide
  rcases lt_trichotomy w.re 0 with ha | ha | ha
  · rcases lt_trichotomy w.im 0 with hb | hb | hb
    · exact ⟨-1, hm1u, by rw [re_neg1_mul]; linarith, by rw [im_neg1_mul]; linarith⟩
    · exact ⟨-1, hm1u, by rw [re_neg1_mul]; linarith, by rw [im_neg1_mul]; linarith⟩
    · exact ⟨⟨0,-1⟩, hmIu, by rw [re_mI_mul]; linarith, by rw [im_mI_mul]; linarith⟩
  · rcases lt_trichotomy w.im 0 with hb | hb | hb
    · exact ⟨⟨0,1⟩, hIu, by rw [re_I_mul]; linarith, by rw [im_I_mul]; linarith⟩
    · exact absurd (Zsqrtd.ext ha hb) hw
    · exact ⟨⟨0,-1⟩, hmIu, by rw [re_mI_mul]; linarith, by rw [im_mI_mul]; linarith⟩
  · rcases lt_trichotomy w.im 0 with hb | hb | hb
    · exact ⟨⟨0,1⟩, hIu, by rw [re_I_mul]; linarith, by rw [im_I_mul]; linarith⟩
    · exact ⟨1, h1u, by rw [one_mul]; linarith, by rw [one_mul]; linarith⟩
    · exact ⟨1, h1u, by rw [one_mul]; linarith, by rw [one_mul]; linarith⟩

/-! ## 5. The maximal pieces in normal form cover `{z : d ∣ |z|²}` -/

/-- A maximal piece generator is nonzero (for `d ≥ 1`). -/
lemma GaussPieceMax_ne_zero (d : ℕ) (hd : 1 ≤ d) {w : GaussianInt} (hw : GaussPieceMax d w) :
    w ≠ 0 := by
  obtain ⟨u, hu, rfl⟩ := hw.1
  exact gaussPieceGen_ne_zero hd hu

/-- Every `z` with `d ∣ |z|²` is divisible by some element of `maxPieceFinset d`. -/
lemma exists_maxPieceFinset_dvd (d : ℕ) (hd : 1 ≤ d) {z : GaussianInt}
    (hz : d ∣ Work.FIPlan.gnorm z) : ∃ w ∈ maxPieceFinset d, w ∣ z := by
  obtain ⟨w₀, hmax, hw₀z⟩ := (maximal_piece_cover d hd z).mp hz
  have hw₀0 : w₀ ≠ 0 := GaussPieceMax_ne_zero d hd hmax
  obtain ⟨ε, hε, hre, him⟩ := exists_unit_fundamental w₀ hw₀0
  refine ⟨ε * w₀, ?_, ?_⟩
  · rw [maxPieceFinset, Finset.mem_filter]
    refine ⟨?_, GaussPieceMax_unit_mul d hd hmax ε hε, hre, him⟩
    rw [mem_gBox]
    have hgn : Work.FIPlan.gnorm (ε * w₀) ≤ d * d := by
      rw [gnorm_unit_mul ε w₀ hε]
      exact (GaussPieceMax_arith d hd).2.1 w₀ hmax
    exact ⟨Finset.mem_Icc.mpr (abs_le.mp (abs_re_le_of_gnorm hgn)),
           Finset.mem_Icc.mpr (abs_le.mp (abs_im_le_of_gnorm hgn))⟩
  · obtain ⟨c, hc⟩ := hw₀z
    exact ⟨star ε * c, by
      rw [hc, show ε * w₀ * (star ε * c) = (ε * star ε) * (w₀ * c) by ring,
        unit_mul_star ε hε, one_mul]⟩

/-! ## 6. The lemma -/

theorem card_filter_le_le_pieces (Pa : Work.FITop.Params) (φ : ℝ) (z₁ : GaussianInt) (d e : ℕ)
    (hd : 1 ≤ d) :
    ((Work.FIArea3.JointCount.pairBoxFinset Pa φ z₁ d e).card : ℝ)
      ≤ ∑ w ∈ Work.FIArea3.JointCount.maxPieceFinset d,
          ((Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card : ℝ) := by
  have hsub : Work.FIArea3.JointCount.pairBoxFinset Pa φ z₁ d e ⊆
      (Work.FIArea3.JointCount.maxPieceFinset d).biUnion
        (fun w => Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e) := by
    intro z hz
    rw [Work.FIArea3.JointCount.pairBoxFinset, Finset.mem_filter] at hz
    obtain ⟨hzbox, hdvd, hed⟩ := hz
    obtain ⟨w, hwmem, hwz⟩ := exists_maxPieceFinset_dvd d hd hdvd
    rw [Finset.mem_biUnion]
    exact ⟨w, hwmem, Finset.mem_filter.mpr ⟨hzbox, hwz, hed⟩⟩
  calc ((Work.FIArea3.JointCount.pairBoxFinset Pa φ z₁ d e).card : ℝ)
      ≤ (((Work.FIArea3.JointCount.maxPieceFinset d).biUnion
          (fun w => Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ((∑ w ∈ Work.FIArea3.JointCount.maxPieceFinset d,
            (Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card) : ℕ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ = ∑ w ∈ Work.FIArea3.JointCount.maxPieceFinset d,
            ((Work.FIArea3.JointCount.jointPieceBoxFinset Pa φ z₁ w e).card : ℝ) := by
        rw [Nat.cast_sum]

end

end Work.FIArea3.JointCount
