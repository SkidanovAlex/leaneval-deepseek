/-
# `Submission.Work.FIArea3.LargeUBase` — the Gaussian-integer input of the `largeU` pair sum

Definitions and elementary lemmas used by `pairSumCrude6_largeU`:
* the content `gContent v = gcd(|v.re|,|v.im|)` of a Gaussian integer and its primitive part
  `gPrim v = v / gContent v`;
* the identity `Δ(z, z+v) = Im(z̄v) = z.re*v.im - z.im*v.re` and the description of the fibres of
  `z ↦ Im(z̄v)` as the cosets of `ℤ gPrim v` (`ker_im_star_mul`, `im_star_mul_eq_iff`);
* the distance estimate `‖z - z'‖ ≤ 10 θ√N` for `z, z'` in the polar box (5.14) (from
  `FIArea4.dist_polarBox_le`: the box lies in a disc of radius `5θ√N`),
  and its consequence: a fibre of `z ↦ Im(z̄v)` meets the polar box in at most
  `20 θ√N (gContent v)/|v| + 3` points.
-/
import Mathlib
import Submission.Work.FIArea3.BoxDefs
import Submission.Work.FIArea4.polarBox_card_le

set_option autoImplicit false

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## 1. The content and the primitive part of a Gaussian integer -/

/-- The content `gcd(|re|,|im|)` of a Gaussian integer. -/
def gContent (z : GaussianInt) : ℕ := Nat.gcd z.re.natAbs z.im.natAbs

/-- The primitive part `z / gcd(|re|,|im|)`. -/
def gPrim (z : GaussianInt) : GaussianInt :=
  ⟨z.re / (gContent z : ℤ), z.im / (gContent z : ℤ)⟩

lemma gContent_dvd_re (z : GaussianInt) : (gContent z : ℤ) ∣ z.re := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]; exact Nat.gcd_dvd_left _ _

lemma gContent_dvd_im (z : GaussianInt) : (gContent z : ℤ) ∣ z.im := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]; exact Nat.gcd_dvd_right _ _

lemma gContent_pos {z : GaussianInt} (hz : z ≠ 0) : 1 ≤ gContent z := by
  rw [gContent]
  rcases Nat.eq_zero_or_pos (Nat.gcd z.re.natAbs z.im.natAbs) with h | h
  · exfalso; rw [Nat.gcd_eq_zero_iff] at h
    exact hz (Zsqrtd.ext (Int.natAbs_eq_zero.mp h.1) (Int.natAbs_eq_zero.mp h.2))
  · exact h

lemma gPrim_re_mul_gContent (z : GaussianInt) :
    (gPrim z).re * (gContent z : ℤ) = z.re := by
  rw [gPrim]; simp only; rw [Int.ediv_mul_cancel (gContent_dvd_re z)]

lemma gPrim_im_mul_gContent (z : GaussianInt) :
    (gPrim z).im * (gContent z : ℤ) = z.im := by
  rw [gPrim]; simp only; rw [Int.ediv_mul_cancel (gContent_dvd_im z)]

lemma eq_gContent_mul_gPrim (z : GaussianInt) : z = (gContent z : GaussianInt) * gPrim z := by
  apply Zsqrtd.ext
  · show z.re = (((gContent z : GaussianInt)) * gPrim z).re
    rw [show (((gContent z : GaussianInt)) * gPrim z).re
        = (gContent z : ℤ) * (z.re / (gContent z : ℤ)) from by simp [gPrim]]
    rw [mul_comm, Int.ediv_mul_cancel (gContent_dvd_re z)]
  · show z.im = (((gContent z : GaussianInt)) * gPrim z).im
    rw [show (((gContent z : GaussianInt)) * gPrim z).im
        = (gContent z : ℤ) * (z.im / (gContent z : ℤ)) from by simp [gPrim]]
    rw [mul_comm, Int.ediv_mul_cancel (gContent_dvd_im z)]

lemma coprime_gPrim {z : GaussianInt} (hz : 1 ≤ gContent z) :
    Nat.Coprime (gPrim z).re.natAbs (gPrim z).im.natAbs := by
  have hc : 0 < gContent z := hz
  have h1 : (gPrim z).re.natAbs = z.re.natAbs / gContent z := by
    rw [gPrim]; show (z.re / (gContent z : ℤ)).natAbs = _
    rw [Int.natAbs_ediv, Int.natAbs_natCast]
    rw [if_pos (Or.inr (Or.inr (gContent_dvd_re z)))]; simp
  have h2 : (gPrim z).im.natAbs = z.im.natAbs / gContent z := by
    rw [gPrim]; show (z.im / (gContent z : ℤ)).natAbs = _
    rw [Int.natAbs_ediv, Int.natAbs_natCast]
    rw [if_pos (Or.inr (Or.inr (gContent_dvd_im z)))]; simp
  rw [h1, h2, gContent]; exact Nat.coprime_div_gcd_div_gcd hc

/-! ## 2. Norms -/

lemma gnorm_mul (a b : GaussianInt) : gnorm (a * b) = gnorm a * gnorm b := by
  rw [gnorm, gnorm, gnorm, Zsqrtd.norm_mul, Int.natAbs_mul]

lemma gnorm_intCast (k : ℤ) : gnorm (k : GaussianInt) = k.natAbs ^ 2 := by
  rw [gnorm]
  show ((k : GaussianInt).norm).natAbs = k.natAbs ^ 2
  have h : (k : GaussianInt).norm = k ^ 2 := by
    show ((k : GaussianInt).re * (k : GaussianInt).re
        - (-1) * ((k : GaussianInt).im * (k : GaussianInt).im)) = k ^ 2
    simp; ring
  rw [h, Int.natAbs_pow]

lemma gnorm_natCast (n : ℕ) : gnorm (n : GaussianInt) = n ^ 2 := by
  have := gnorm_intCast (n : ℤ)
  simpa using this

lemma gnorm_pos {z : GaussianInt} (hz : z ≠ 0) : 0 < gnorm z := by
  rw [gnorm]
  exact Int.natAbs_pos.mpr (fun h =>
    hz ((Zsqrtd.norm_eq_zero (by intro n; nlinarith [sq_nonneg n]) z).mp h))

lemma gnorm_gPrim_eq {v : GaussianInt} (hv : v ≠ 0) :
    (gnorm (gPrim v) : ℝ) = (gnorm v : ℝ) / (gContent v : ℝ) ^ 2 := by
  have h2 : (gnorm v : ℝ) = (gContent v : ℝ) ^ 2 * (gnorm (gPrim v) : ℝ) := by
    have h3 : gnorm v = gContent v ^ 2 * gnorm (gPrim v) := by
      conv_lhs => rw [eq_gContent_mul_gPrim v]
      rw [gnorm_mul, gnorm_natCast]

    exact_mod_cast h3
  have hg0 : ((gContent v : ℕ) : ℝ) ≠ 0 := by
    have := gContent_pos hv; positivity
  rw [h2]; field_simp

/-- `‖(gPrim v).toComplex‖ = |v| / gContent v`. -/
lemma norm_gPrim_toComplex {v : GaussianInt} (hv : v ≠ 0) :
    ‖(gPrim v).toComplex‖ = Real.sqrt ((gnorm v : ℕ) : ℝ) / (gContent v : ℝ) := by
  rw [Work.FIArea4.norm_toComplex_eq_sqrt_gnorm, gnorm_gPrim_eq hv]
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]

/-- `‖(z - z').toComplex‖ = √|z - z'|²`. -/
lemma norm_sub_toComplex (z z' : GaussianInt) :
    ‖z.toComplex - z'.toComplex‖ = Real.sqrt ((gnorm (z - z') : ℕ) : ℝ) := by
  rw [← map_sub, Work.FIArea4.norm_toComplex_eq_sqrt_gnorm]

/-- `|Im(z̄v)| ≤ |z| |v|`. -/
lemma im_le_norm_mul (z v : GaussianInt) :
    |(((star z * v).im : ℤ) : ℝ)|
      ≤ Real.sqrt ((gnorm z : ℕ) : ℝ) * Real.sqrt ((gnorm v : ℕ) : ℝ) := by
  have hstep : |(((star z * v).im : ℤ) : ℝ)| = |((star z * v).toComplex).im| := by
    rw [GaussianInt.intCast_im]
  rw [hstep]
  calc |((star z * v).toComplex).im| ≤ ‖(star z * v).toComplex‖ := Complex.abs_im_le_norm _
    _ = ‖(star z).toComplex * v.toComplex‖ := by rw [map_mul]
    _ = ‖(star z).toComplex‖ * ‖v.toComplex‖ := norm_mul _ _
    _ = ‖star z.toComplex‖ * ‖v.toComplex‖ := by
        congr 1
        have hstar : (star z).toComplex = star z.toComplex := by
          apply Complex.ext
          · rw [Complex.star_def, Complex.conj_re, ← GaussianInt.intCast_re z,
                ← GaussianInt.intCast_re (star z)]; rfl
          · rw [Complex.star_def, Complex.conj_im, ← GaussianInt.intCast_im z,
                ← GaussianInt.intCast_im (star z)]; simp
        rw [hstar]
    _ = ‖z.toComplex‖ * ‖v.toComplex‖ := by
        congr 1
        exact Complex.norm_conj _
    _ = Real.sqrt ((gnorm z : ℕ) : ℝ) * Real.sqrt ((gnorm v : ℕ) : ℝ) := by
        rw [Work.FIArea4.norm_toComplex_eq_sqrt_gnorm, Work.FIArea4.norm_toComplex_eq_sqrt_gnorm]

/-- `(star z * v).im = gContent v · (star z * gPrim v).im`: the values of `Im(z̄v)` are multiples
of the content of `v`. -/
lemma im_gContent_mul (z v : GaussianInt) :
    (star z * v).im = (gContent v : ℤ) * (star z * gPrim v).im := by
  conv_lhs => rw [eq_gContent_mul_gPrim v]
  rw [show star z * ((gContent v : GaussianInt) * gPrim v)
      = (gContent v : GaussianInt) * (star z * gPrim v) from by ring]
  rw [show (gContent v : GaussianInt) = (⟨(gContent v : ℤ), 0⟩ : GaussianInt) from rfl,
      Zsqrtd.im_mul]
  simp

/-! ## 3. The fibres of `z ↦ Im(z̄v)` -/

lemma im_star_mul_formula (z v : GaussianInt) :
    (star z * v).im = z.re * v.im - z.im * v.re := by
  rw [Zsqrtd.im_mul]; simp; ring

lemma im_star_mul_add (a b v : GaussianInt) :
    (star (a + b) * v).im = (star a * v).im + (star b * v).im := by
  rw [im_star_mul_formula (a+b) v, im_star_mul_formula a v, im_star_mul_formula b v]
  rw [show (a+b).re = a.re + b.re from rfl, show (a+b).im = a.im + b.im from rfl]
  ring

lemma intCast_mul_gPrim (v : GaussianInt) (k : ℤ) :
    (k : GaussianInt) * gPrim v = ⟨k * (gPrim v).re, k * (gPrim v).im⟩ := by
  apply Zsqrtd.ext
  · show ((k : GaussianInt) * gPrim v).re = k * (gPrim v).re
    rw [Zsqrtd.re_mul]; simp
  · show ((k : GaussianInt) * gPrim v).im = k * (gPrim v).im
    rw [Zsqrtd.im_mul]; simp

/-- The kernel of `z ↦ Im(z̄v)` is `ℤ · gPrim v` (for `v ≠ 0`). -/
lemma ker_im_star_mul {v : GaussianInt} (hv : v ≠ 0) (w : GaussianInt) :
    (star w * v).im = 0 ↔ ∃ k : ℤ, w = (k : GaussianInt) * gPrim v := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, gPrim v = ⟨a, b⟩ := ⟨(gPrim v).re, (gPrim v).im, rfl⟩
  have hg1 : 1 ≤ gContent v := gContent_pos hv
  have hg0 : (gContent v : ℤ) ≠ 0 := by
    have : (0:ℤ) < (gContent v : ℤ) := by exact_mod_cast hg1
    omega
  have hcop : IsCoprime a b := by
    have hthis := coprime_gPrim hg1
    rw [congrArg Zsqrtd.re hab, congrArg Zsqrtd.im hab] at hthis
    exact Int.isCoprime_iff_nat_coprime.mpr hthis
  have hva : a * (gContent v : ℤ) = v.re := by
    have := gPrim_re_mul_gContent v; rw [hab] at this; simpa using this
  have hvb : b * (gContent v : ℤ) = v.im := by
    have := gPrim_im_mul_gContent v; rw [hab] at this; simpa using this
  have hmul : ∀ k : ℤ, (k : GaussianInt) * gPrim v = ⟨k * a, k * b⟩ := by
    intro k; rw [intCast_mul_gPrim, hab]
  constructor
  · intro h
    obtain ⟨s, t, hst⟩ := hcop
    have hcross : w.re * b = w.im * a := by
      rw [im_star_mul_formula] at h
      have h1 : (gContent v : ℤ) * (w.re * b) = (gContent v : ℤ) * (w.im * a) := by
        calc (gContent v:ℤ) * (w.re * b)
            = w.re * (b * (gContent v:ℤ)) := by ring
          _ = w.re * v.im := by rw [hvb]
          _ = w.im * v.re := by linarith [h]
          _ = w.im * (a * (gContent v:ℤ)) := by rw [hva]
          _ = (gContent v:ℤ) * (w.im * a) := by ring
      exact mul_left_cancel₀ hg0 h1
    have hRe : (s * w.re + t * w.im) * a = w.re := by
      calc (s * w.re + t * w.im) * a = s * w.re * a + t * (w.im * a) := by ring
        _ = s * w.re * a + t * (w.re * b) := by rw [hcross.symm]
        _ = w.re * (s * a + t * b) := by ring
        _ = w.re := by rw [hst]; ring
    have hIm : (s * w.re + t * w.im) * b = w.im := by
      calc (s * w.re + t * w.im) * b = s * (w.re * b) + t * w.im * b := by ring
        _ = s * (w.im * a) + t * w.im * b := by rw [hcross]
        _ = w.im * (s * a + t * b) := by ring
        _ = w.im := by rw [hst]; ring
    exact ⟨s * w.re + t * w.im, by rw [hmul]; exact Zsqrtd.ext hRe.symm hIm.symm⟩
  · rintro ⟨k, rfl⟩
    rw [im_star_mul_formula, hmul]
    rw [← hvb, ← hva]; ring

/-- Two points have the same value of `z ↦ Im(z̄v)` iff they differ by an element of
`ℤ · gPrim v`. -/
lemma im_star_mul_eq_iff {v : GaussianInt} (hv : v ≠ 0) (z z' : GaussianInt) :
    (star z * v).im = (star z' * v).im ↔ ∃ k : ℤ, z = z' + (k : GaussianInt) * gPrim v := by
  have hd : ∀ a b : GaussianInt,
      (star a * v).im - (star b * v).im = (star (a - b) * v).im := by
    intro a b
    rw [im_star_mul_formula a v, im_star_mul_formula b v, im_star_mul_formula (a - b) v]
    rw [show (a - b).re = a.re - b.re from rfl, show (a - b).im = a.im - b.im from rfl]
    ring
  constructor
  · intro h
    have h0 : (star (z - z') * v).im = 0 := by rw [← hd z z', h]; ring
    obtain ⟨k, hk⟩ := (ker_im_star_mul hv (z - z')).mp h0
    exact ⟨k, by rw [← hk]; abel⟩
  · rintro ⟨k, hk⟩
    rw [hk, im_star_mul_add]
    rw [(ker_im_star_mul hv ((k : GaussianInt) * gPrim v)).mpr ⟨k, rfl⟩, add_zero]

/-! ## 4. The polar box is thin -/

/-- Any two points of the polar box (5.14) are within `10 θ√N`. -/
lemma polarBox_dist_le (Pa : Work.FITop.Params) (φ : ℝ) {z z' : GaussianInt}
    (hz : z ∈ polarBoxFinset Pa φ) (hz' : z' ∈ polarBoxFinset Pa φ) :
    ‖z.toComplex - z'.toComplex‖ ≤ 10 * (Pa.θ * Real.sqrt Pa.N) := by
  have hzpol : Work.FITop3.InPolarBox Pa φ z := (mem_polarBoxFinset.mp hz).2
  have hz'pol : Work.FITop3.InPolarBox Pa φ z' := (mem_polarBoxFinset.mp hz').2
  set c : ℂ := (Real.sqrt Pa.N : ℂ) * Complex.exp (((φ + Real.pi * Pa.θ : ℝ) : ℂ) * Complex.I)
    with hc
  have h1 : ‖z.toComplex - c‖ ≤ 5 * (Pa.θ * Real.sqrt Pa.N) := by
    rw [hc]
    have := Work.FIArea4.dist_polarBox_le Pa φ z hzpol
    linarith
  have h2 : ‖z'.toComplex - c‖ ≤ 5 * (Pa.θ * Real.sqrt Pa.N) := by
    rw [hc]
    have := Work.FIArea4.dist_polarBox_le Pa φ z' hz'pol
    linarith
  calc ‖z.toComplex - z'.toComplex‖ = ‖(z.toComplex - c) - (z'.toComplex - c)‖ := by ring_nf
    _ ≤ ‖z.toComplex - c‖ + ‖z'.toComplex - c‖ := norm_sub_le _ _
    _ ≤ 5 * (Pa.θ * Real.sqrt Pa.N) + 5 * (Pa.θ * Real.sqrt Pa.N) := add_le_add h1 h2
    _ = 10 * (Pa.θ * Real.sqrt Pa.N) := by ring

/-- A fibre of `z ↦ Im(z̄v)` meets the polar box in at most
`20 θ√N (gContent v)/|v| + 3` points. -/
lemma card_fiber_le (Pa : Work.FITop.Params) (φ : ℝ) (v : GaussianInt) (hv : v ≠ 0)
    (z₀ : GaussianInt) :
    (((polarBoxFinset Pa φ).filter
        (fun z => (star z * v).im = (star z₀ * v).im)).card : ℝ)
      ≤ 20 * (Pa.θ * Real.sqrt Pa.N) * (gContent v : ℝ)
          / Real.sqrt ((gnorm v : ℕ) : ℝ) + 3 := by
  have hRpos : 0 < Real.sqrt ((gnorm v : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast gnorm_pos hv)
  have hgnn : (0:ℝ) ≤ (gContent v : ℝ) := by positivity
  have hu0 : 0 ≤ Pa.θ * Real.sqrt Pa.N := mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
  have hg0 : (0:ℝ) < (gContent v : ℝ) := by have := gContent_pos hv; positivity
  have hbase : (0:ℝ) ≤ 20 * (Pa.θ * Real.sqrt Pa.N) * (gContent v : ℝ)
      / Real.sqrt ((gnorm v : ℕ) : ℝ) + 3 := by positivity
  have hwg := norm_gPrim_toComplex hv
  set S : Finset GaussianInt := (polarBoxFinset Pa φ).filter
      (fun z => (star z * v).im = (star z₀ * v).im) with hSdef
  have hgoal : (S.card : ℝ) ≤ 20 * (Pa.θ * Real.sqrt Pa.N) * (gContent v : ℝ)
      / Real.sqrt ((gnorm v : ℕ) : ℝ) + 3 := by
    rcases Finset.eq_empty_or_nonempty S with hemp | ⟨z₁, hz₁⟩
    · rw [hemp]; simp only [Finset.card_empty, Nat.cast_zero]; exact hbase
    · have hz₁K : z₁ ∈ polarBoxFinset Pa φ := (Finset.mem_filter.mp hz₁).1
      have hz₁Φ : (star z₁ * v).im = (star z₀ * v).im := (Finset.mem_filter.mp hz₁).2
      set M : ℕ := ⌈10 * (Pa.θ * Real.sqrt Pa.N) * (gContent v : ℝ)
          / Real.sqrt ((gnorm v : ℕ) : ℝ)⌉₊ with hMdef
      have hsub : S ⊆ (Finset.Icc (-(M:ℤ)) (M:ℤ)).image
          (fun k : ℤ => z₁ + (k : GaussianInt) * gPrim v) := by
        intro z hz
        have hzK : z ∈ polarBoxFinset Pa φ := (Finset.mem_filter.mp hz).1
        have hzΦ : (star z * v).im = (star z₁ * v).im := by
          rw [(Finset.mem_filter.mp hz).2, hz₁Φ]
        obtain ⟨k, hk⟩ := (im_star_mul_eq_iff hv z z₁).mp hzΦ
        refine Finset.mem_image.mpr ⟨k, ?_, hk.symm⟩
        have hzd : z - z₁ = (k : GaussianInt) * gPrim v := by rw [hk]; abel
        have hdist : ‖z.toComplex - z₁.toComplex‖ ≤ 10 * (Pa.θ * Real.sqrt Pa.N) :=
          polarBox_dist_le Pa φ hzK hz₁K
        have hnorm : ‖z.toComplex - z₁.toComplex‖
            = |((k:ℤ):ℝ)| * (Real.sqrt ((gnorm v : ℕ) : ℝ) / (gContent v : ℝ)) := by
          rw [← map_sub, hzd, map_mul, norm_mul, hwg, map_intCast, Complex.norm_intCast]
        have hkey : |((k:ℤ):ℝ)| * (Real.sqrt ((gnorm v : ℕ) : ℝ) / (gContent v : ℝ))
            ≤ 10 * (Pa.θ * Real.sqrt Pa.N) := by rw [← hnorm]; exact hdist
        have hk1 : |((k:ℤ):ℝ)| ≤ 10 * (Pa.θ * Real.sqrt Pa.N) * (gContent v : ℝ)
            / Real.sqrt ((gnorm v : ℕ) : ℝ) := by
          rw [le_div_iff₀ hRpos]
          have h2 : |((k:ℤ):ℝ)| * (Real.sqrt ((gnorm v : ℕ) : ℝ) / (gContent v : ℝ))
              * (gContent v : ℝ) = |((k:ℤ):ℝ)| * Real.sqrt ((gnorm v : ℕ) : ℝ) := by
            rw [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hg0)]
          have h3 := mul_le_mul_of_nonneg_right hkey hg0.le
          rw [h2] at h3
          linarith [h3]
        rw [Finset.mem_Icc]
        have hMge : 10 * (Pa.θ * Real.sqrt Pa.N) * (gContent v : ℝ)
            / Real.sqrt ((gnorm v : ℕ) : ℝ) ≤ (M:ℝ) := by
          rw [hMdef]; exact Nat.le_ceil _
        constructor
        · have h3 : (-(k) : ℤ) ≤ (M : ℤ) := by
            have h4 : (((-(k) : ℤ)) : ℝ) ≤ (((M : ℤ)) : ℝ) := by
              push_cast
              exact le_trans (neg_le_abs _) (le_trans hk1 hMge)
            exact_mod_cast h4
          omega
        · have h2 : (((k:ℤ):ℝ)) ≤ (M:ℝ) := le_trans (le_abs_self _) (le_trans hk1 hMge)
          have h4 : ((k : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by push_cast; exact h2
          exact_mod_cast h4
      have hcard1 : S.card ≤ (Finset.Icc (-(M:ℤ)) (M:ℤ)).card :=
        le_trans (Finset.card_le_card hsub) Finset.card_image_le
      have hcard3 : (Finset.Icc (-(M:ℤ)) (M:ℤ)).card = 2*M+1 := by
        rw [Int.card_Icc]; simp; omega
      have hMlt : (M:ℝ) < 10 * (Pa.θ * Real.sqrt Pa.N) * (gContent v : ℝ)
          / Real.sqrt ((gnorm v : ℕ) : ℝ) + 1 := by
        rw [hMdef]; exact Nat.ceil_lt_add_one (by positivity)
      have hbound : S.card ≤ 2*M+1 := by rw [← hcard3]; exact hcard1
      calc (S.card : ℝ) ≤ ((2*M+1 : ℕ) : ℝ) := by exact_mod_cast hbound
        _ = 2*(M:ℝ)+1 := by push_cast; ring
        _ ≤ 20 * (Pa.θ * Real.sqrt Pa.N) * (gContent v : ℝ)
              / Real.sqrt ((gnorm v : ℕ) : ℝ) + 3 := by
            have h2 : 2 * (M:ℝ) + 1 ≤ 2 * (10 * (Pa.θ * Real.sqrt Pa.N) * (gContent v : ℝ)
                / Real.sqrt ((gnorm v : ℕ) : ℝ)) + 3 := by linarith [hMlt]
            have h3 : 2 * (10 * (Pa.θ * Real.sqrt Pa.N) * (gContent v : ℝ)
                / Real.sqrt ((gnorm v : ℕ) : ℝ)) + 3
                = 20 * (Pa.θ * Real.sqrt Pa.N) * (gContent v : ℝ)
                  / Real.sqrt ((gnorm v : ℕ) : ℝ) + 3 := by ring
            linarith [h2, h3]
  exact hgoal

/-- `θ ≤ 1/10`.  (`θ = (log x)^{-A'}` with `A' ≥ 2^{20} ≥ 25` and `log x ≥ log 3 > 1.098`, so
`(log x)^{A'} ≥ (1.098)^{25} ≥ 10`.) -/
lemma theta_le_tenth (Pa : Work.FITop.Params) : Pa.θ ≤ (1:ℝ)/10 := by
  rw [Pa.hθ]
  have hx3 : (3:ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have h3pos : (0:ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3le : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
  have hlog3' : (1:ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hlogx1 : (1:ℝ) < Real.log (Pa.x : ℝ) := lt_of_lt_of_le hlog3' hlog3le
  have hx0 : (0:ℝ) < Real.log (Pa.x : ℝ) := by linarith
  have hA' : (25:ℝ) ≤ Pa.A' := by
    have h : (2:ℝ)^(20:ℕ) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
    have h2 : (25:ℝ) ≤ (2:ℝ)^(20:ℕ) := by norm_num
    linarith
  have h1 : (10:ℝ) ≤ (Real.log (Pa.x:ℝ)) ^ (25:ℕ) := by
    have ha := pow_le_pow_left₀ h3pos.le hlog3le 25
    have hb : (10:ℝ) ≤ (Real.log 3) ^ (25:ℕ) := by
      have h3 : (1.098:ℝ) ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
      have hc := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ (1.098:ℝ)) h3 25
      have hd : (10:ℝ) ≤ (1.098:ℝ)^(25:ℕ) := by norm_num
      linarith [hc]
    linarith [ha, hb]
  have h2 : (Real.log (Pa.x:ℝ)) ^ (25:ℕ) ≤ (Real.log (Pa.x:ℝ)) ^ Pa.A' := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hlogx1.le hA'
  have h3 : (10:ℝ) ≤ (Real.log (Pa.x:ℝ)) ^ Pa.A' := le_trans h1 h2
  have h4 : (((Real.log (Pa.x:ℝ)) ^ Pa.A')⁻¹ : ℝ) ≤ ((10:ℝ))⁻¹ := by
    rw [inv_le_inv₀ (Real.rpow_pos_of_pos hx0 Pa.A') (by norm_num : (0:ℝ) < 10)]
    exact h3
  rw [Real.rpow_neg hx0.le]
  simpa using h4

end

end Work.FIArea3
