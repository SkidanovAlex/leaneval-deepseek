/-
# §9 (9.5): the per-frequency weight sum in rectangular coordinates

*FI* §9 (9.5) bounds `Z(h₁,h₂) = Σ_{(z₁,z₂)=1} |β_{z₁}β_{z₂}| τ(Δ)³(Λ,Δ)|Δ|⁻¹`, `Λ = z₁h₁² − z₂h₂²`,
`Δ = Δ(z₁,z₂) = Im(z̄₁z₂)`.  Every object in the sum lives on the *rectangular* coordinates
`z_j = r_j + i s_j`: writing `Λ(r₁,r₂) = r₁h₁² − r₂h₂²`, `Λ(s₁,s₂) = s₁h₁² − s₂h₂²` (the real and
imaginary parts of `Λ`) and `Δ = r₁s₂ − r₂s₁`,

  `(Λ,Δ) = (|Λ(r₁,r₂)|, |Λ(s₁,s₂)|, |Δ|)`  (the gcd of the three absolute values),

so the whole sum is a four-fold sum over the coordinates.  This module fixes that vocabulary
(`dlt`, `tA`, `tB`, `cdg`, `ZB`) together with the right-hand side `UB` of the target, so that the
per-frequency bound `Work.FIArea2.Count.sec9_Z_bound` can be proved as

* `sec9Zsum Pa h ≤ ZB (radN Pa) h (√(ϑN))` — the rewriting into coordinates (dropping the
  coprimality indicator, which only makes the sum larger), and
* `ZB R h thr ≤ C ϑ^{-1/2}(log N)ᴷ UB R h` — the arithmetic core, split into the non-degenerate
  half `tA ≠ 0` (grouped in `(r₁,r₂)`) and the degenerate half `tA = 0` (grouped in `(s₁,s₂)`,
  where `h ≠ 0` and `Δ ≠ 0` force `tB ≠ 0`), each bounded by the *same* count of *FI* §9
  ("given `r₁,r₂` and any `Δ`, the number of `(s₁,s₂)` with `r₁s₂ − r₂s₁ = Δ` is
  `O(1 + (r₁,r₂)|I|/|r₁|) = O(ϑ^{-1/2}(r₁,r₂))`, using `|r₁| > √(ϑN)`").

The two halves use the divisor-sum input `Σ_{d|m} φ(d)τ(d)³/d ≤ τ(m)⁴` and the counting input
`Work.FIArea2.Count.class_delta_sum_le`.
-/
import Mathlib
import Submission.Work.FIArea2.Sec9AggDefs
import Submission.Work.FIArea2.Count.class_delta_sum_le

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Work.FIArea2.Count

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. Coordinate forms of `Δ`, `Λ`, `(Λ,Δ)` -/

/-- `Δ(z₁,z₂) = Im(z̄₁z₂) = r₁s₂ − r₂s₁` in rectangular coordinates. -/
def dlt (r1 s1 r2 s2 : ℤ) : ℕ := (r1 * s2 - r2 * s1).natAbs

/-- `Re Λ = r₁h₁² − r₂h₂²`. -/
def tA (h1 h2 r1 r2 : ℤ) : ℤ := r1 * h1 ^ 2 - r2 * h2 ^ 2

/-- `Im Λ = s₁h₁² − s₂h₂²`. -/
def tB (h1 h2 s1 s2 : ℤ) : ℤ := s1 * h1 ^ 2 - s2 * h2 ^ 2

/-- `(Λ,Δ)` in rectangular coordinates: the gcd of the three absolute values. -/
def cdg (h1 h2 r1 s1 r2 s2 : ℤ) : ℕ :=
  Nat.gcd (Nat.gcd (tA h1 h2 r1 r2).natAbs (tB h1 h2 s1 s2).natAbs) (dlt r1 s1 r2 s2)

/-- The four-fold coordinate form of the §9 weight sum (9.5), with the axis-avoidance threshold
`thr` (the target takes `thr = √(ϑN)`), *without* the coprimality indicator. -/
def ZW (h1 h2 r1 s1 r2 s2 : ℤ) : ℝ :=
  (((dlt r1 s1 r2 s2).divisors.card : ℝ) ^ 3 / ((dlt r1 s1 r2 s2) : ℝ))
    * (cdg h1 h2 r1 s1 r2 s2 : ℝ)

/-- The four-fold coordinate form of the §9 weight sum (9.5), with the axis-avoidance threshold
`thr` (the target takes `thr = √(ϑN)`), *without* the coprimality indicator. -/
def ZB (R : ℤ) (h1 h2 : ℤ) (thr : ℝ) : ℝ :=
  ∑ r1 ∈ Finset.Icc (-R) R, ∑ s1 ∈ Finset.Icc (-R) R,
    ∑ r2 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
      (if thr < |(r1 : ℝ)| ∧ thr < |(s1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ thr < |(s2 : ℝ)| then
        ZW h1 h2 r1 s1 r2 s2
      else 0)

/-- The non-degenerate half `Re Λ ≠ 0` of `ZB` (grouped in `(Re z₁, Re z₂)`). -/
def ZAc (R : ℤ) (h1 h2 : ℤ) (thr : ℝ) : ℝ :=
  ∑ r1 ∈ Finset.Icc (-R) R, ∑ s1 ∈ Finset.Icc (-R) R,
    ∑ r2 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
      (if thr < |(r1 : ℝ)| ∧ thr < |(s1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ thr < |(s2 : ℝ)|
          ∧ tA h1 h2 r1 r2 ≠ 0 then
        ZW h1 h2 r1 s1 r2 s2
      else 0)

/-- The degenerate half `Re Λ = 0` of `ZB` (grouped in `(Im z₁, Im z₂)`). -/
def ZBc (R : ℤ) (h1 h2 : ℤ) (thr : ℝ) : ℝ :=
  ∑ r1 ∈ Finset.Icc (-R) R, ∑ s1 ∈ Finset.Icc (-R) R,
    ∑ r2 ∈ Finset.Icc (-R) R, ∑ s2 ∈ Finset.Icc (-R) R,
      (if thr < |(r1 : ℝ)| ∧ thr < |(s1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ thr < |(s2 : ℝ)|
          ∧ tA h1 h2 r1 r2 = 0 then
        ZW h1 h2 r1 s1 r2 s2
      else 0)

/-- `ZB` splits pointwise into its two halves. -/
theorem ZB_eq_ZAc_add_ZBc (R : ℤ) (h1 h2 : ℤ) (thr : ℝ) :
    ZB R h1 h2 thr = ZAc R h1 h2 thr + ZBc R h1 h2 thr := by
  simp only [ZB, ZAc, ZBc, ZW]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro r1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s1 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro r2 _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro s2 _
  by_cases hind : (thr < |(r1 : ℝ)| ∧ thr < |(s1 : ℝ)| ∧ thr < |(r2 : ℝ)| ∧ thr < |(s2 : ℝ)|)
  · rw [if_pos hind]
    by_cases ht : tA h1 h2 r1 r2 = 0
    · rw [if_neg (fun hc => hc.2.2.2.2 ht),
        if_pos ⟨hind.1, hind.2.1, hind.2.2.1, hind.2.2.2, ht⟩]
      ring
    · rw [if_pos ⟨hind.1, hind.2.1, hind.2.2.1, hind.2.2.2, ht⟩,
        if_neg (fun hc => ht hc.2.2.2.2)]
      ring
  · rw [if_neg hind,
      if_neg (fun hc => hind ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩),
      if_neg (fun hc => hind ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1⟩)]
    ring

/-- The right-hand side of the target: the `(u₁,u₂)`-sum of `(u₁,u₂)τ₄(u₁h₁² − u₂h₂²)`. -/
def UB (R : ℤ) (h1 h2 : ℤ) : ℝ :=
  ∑ u1 ∈ Finset.Icc (-R) R, ∑ u2 ∈ Finset.Icc (-R) R,
    (Nat.gcd u1.natAbs u2.natAbs : ℝ) * (((tA h1 h2 u1 u2).natAbs.divisors.card : ℝ) ^ 4)

/-! ## 2. The dictionary between `GaussianInt` and coordinates -/

/-- `Re Λ(z₁,z₂) = (Re z₁)h₁² − (Re z₂)h₂²`. -/
lemma lam_re (z1 z2 : GaussianInt) (h1 h2 : ℤ) :
    (Lam z1 z2 h1 h2).re = tA h1 h2 z1.re z2.re := by
  simp only [Lam, tA, Zsqrtd.re_sub, Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast,
    mul_zero]
  ring

/-- `Im Λ(z₁,z₂) = (Im z₁)h₁² − (Im z₂)h₂²`. -/
lemma lam_im (z1 z2 : GaussianInt) (h1 h2 : ℤ) :
    (Lam z1 z2 h1 h2).im = tB h1 h2 z1.im z2.im := by
  simp only [Lam, tB, Zsqrtd.im_sub, Zsqrtd.im_mul, Zsqrtd.im_intCast, Zsqrtd.re_intCast,
    mul_zero]
  ring

/-- `Δ(z₁,z₂) = Re z₁ · Im z₂ − Im z₁ · Re z₂`. -/
lemma delta_eq (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z1 z2 = z1.re * z2.im - z1.im * z2.re := by
  simp only [Work.FIPlan.Delta, Zsqrtd.im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

/-- `|Δ(z₁,z₂)|` in coordinates. -/
lemma absDelta_eq (z1 z2 : GaussianInt) :
    Work.FIPlan.absDelta z1 z2 = dlt z1.re z1.im z2.re z2.im := by
  simp only [Work.FIPlan.absDelta, dlt]
  rw [delta_eq]
  ring_nf

/-- The Gaussian gcd `(Λ,Δ)` in coordinates. -/
lemma gcdDelta_eq (z1 z2 : GaussianInt) (h1 h2 : ℤ) :
    gcdDelta z1 z2 h1 h2 = cdg h1 h2 z1.re z1.im z2.re z2.im := by
  simp only [gcdDelta, cdg, lam_re, lam_im, absDelta_eq]

/-! ## 3. The box -/

/-- Membership in the Gaussian box `gBox R`. -/
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
    |(w.re : ℝ)| ≤ (R : ℝ) := by
  have h := (mem_gBox_iff.mp hw).1
  rw [Finset.mem_Icc] at h
  have h1 : (w.re : ℤ) ≤ R := h.2
  have h2 : -R ≤ (w.re : ℤ) := h.1
  have h1' : (w.re : ℝ) ≤ (R : ℝ) := by exact_mod_cast h1
  have h2' : -(R : ℝ) ≤ (w.re : ℝ) := by exact_mod_cast h2
  exact abs_le.mpr ⟨h2', h1'⟩

lemma abs_im_le_of_mem_gBox {R : ℤ} {w : GaussianInt} (hw : w ∈ Work.FIPlan.gBox R) :
    |(w.im : ℝ)| ≤ (R : ℝ) := by
  have h := (mem_gBox_iff.mp hw).2
  rw [Finset.mem_Icc] at h
  have h1 : (w.im : ℤ) ≤ R := h.2
  have h2 : -R ≤ (w.im : ℤ) := h.1
  have h1' : (w.im : ℝ) ≤ (R : ℝ) := by exact_mod_cast h1
  have h2' : -(R : ℝ) ≤ (w.im : ℝ) := by exact_mod_cast h2
  exact abs_le.mpr ⟨h2', h1'⟩

/-! ## 4. The right-hand side -/

/-- `UB` is `sec9Usumming`, verbatim. -/
theorem UB_eq_sec9Usumming (Pa : Work.FITop.Params) (h1 h2 : ℤ) :
    UB (Work.FITop.radN Pa) h1 h2 = sec9Usumming Pa h1 h2 := by
  simp only [UB, sec9Usumming, tA]


end

end Work.FIArea2.Count
