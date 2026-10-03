import Mathlib
import Submission.Work.FIArea7.FIsymbols

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

noncomputable section

/-! ## Auxiliary lemmas for the elementary pair count

The main theorem of this file bounds the number of `z₂` in the box `|re|, |im| ≤ R` satisfying
`c ∣ |Δ(z₁,z₂)|` for a fixed `z₁` whose real part is coprime to `c`.  The proof is the classical
"one residue class per value of `r₂`" count; the two ingredients are

* `mem_gBox_iff` — membership in `gBox R` in coordinates, and
* `card_le_div_of_pairwise_dvd` — a subset of `[−R,R]` whose elements are pairwise congruent
  modulo `c` has at most `(2R+1)/c + 1` elements. -/

/-- Membership in the box `gBox R`, in coordinates. -/
lemma mem_gBox_iff {R : ℤ} {z : GaussianInt} :
    z ∈ Work.FIPlan.gBox R ↔ -R ≤ z.re ∧ z.re ≤ R ∧ -R ≤ z.im ∧ z.im ≤ R := by
  rw [Work.FIPlan.gBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hp' : p ∈ (Finset.Icc (-R) R) ×ˢ (Finset.Icc (-R) R) := hp
    rw [Finset.mem_product] at hp'
    exact ⟨(Finset.mem_Icc.mp hp'.1).1, (Finset.mem_Icc.mp hp'.1).2,
      (Finset.mem_Icc.mp hp'.2).1, (Finset.mem_Icc.mp hp'.2).2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(z.re, z.im), ?_, ?_⟩
    · have : (z.re, z.im) ∈ (Finset.Icc (-R) R) ×ˢ (Finset.Icc (-R) R) := by
        rw [Finset.mem_product]
        exact ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, Finset.mem_Icc.mpr ⟨h3, h4⟩⟩
      exact this
    · exact Zsqrtd.ext rfl rfl

/-- The determinant in coordinates: `Δ(z₁,z₂) = r₁s₂ − r₂s₁`. -/
lemma Delta_eq (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z1 z2 = z1.re * z2.im - z1.im * z2.re := by
  rw [Work.FIPlan.Delta, Zsqrtd.im_mul]
  simp
  ring

/-- `c ∣ |Δ|` implies `(c : ℤ) ∣ Δ`. -/
lemma dvd_Delta_of_dvd_absDelta {c : ℕ} {z1 z2 : GaussianInt}
    (h : c ∣ Work.FIPlan.absDelta z1 z2) : (c : ℤ) ∣ Work.FIPlan.Delta z1 z2 := by
  have h1 : (c : ℤ) ∣ ((Work.FIPlan.Delta z1 z2).natAbs : ℤ) := by
    simpa only [Work.FIPlan.absDelta] using Int.ofNat_dvd.mpr h
  exact Int.dvd_natAbs.mp h1

/-- A subset of the integer interval `[−R,R]` whose elements are pairwise congruent modulo `c`
has at most `(2R+1)/c + 1` elements: consecutive elements of the set differ by at least `c`, and
the whole set fits in an interval of length `2R`. -/
lemma card_le_div_of_pairwise_dvd (R : ℤ) (c : ℕ) (hc : 0 < c) (U : Finset ℤ)
    (hsub : ∀ x ∈ U, x ∈ Finset.Icc (-R) R)
    (hcong : ∀ x ∈ U, ∀ y ∈ U, (c : ℤ) ∣ x - y) :
    U.card ≤ (2 * R + 1).toNat / c + 1 := by
  have hcZ : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hc
  rcases U.eq_empty_or_nonempty with hem | hne
  · rw [hem]
    exact Nat.zero_le _
  · set m : ℤ := U.min' hne with hmdef
    have hmU : m ∈ U := U.min'_mem hne
    have hle : ∀ x ∈ U, m ≤ x := fun x hx => U.min'_le x hx
    have hmIcc : m ∈ Finset.Icc (-R) R := hsub m hmU
    have hmIcc' : -R ≤ m ∧ m ≤ R := Finset.mem_Icc.mp hmIcc
    have hR0 : (0 : ℤ) ≤ R := by linarith [hmIcc'.1, hmIcc'.2]
    have h2R : (0 : ℤ) ≤ 2 * R := by linarith
    set f : ℤ → ℕ := fun x => ((x - m) / (c : ℤ)).toNat with hf
    have hconv : ((2 * R : ℤ) / (c : ℤ)).toNat = (2 * R).toNat / c := by
      have h : (2 * R : ℤ) = ((2 * R).toNat : ℤ) := (Int.toNat_of_nonneg h2R).symm
      conv_lhs => rw [h]
      rw [Int.ofNat_ediv_ofNat, Int.toNat_natCast]
    have hxm : ∀ x ∈ U, x - m ≤ 2 * R := by
      intro x hx
      have hxI : -R ≤ x ∧ x ≤ R := Finset.mem_Icc.mp (hsub x hx)
      linarith [hxI.2, hmIcc'.1]
    have hxm0 : ∀ x ∈ U, (0 : ℤ) ≤ x - m := by
      intro x hx
      linarith [hle x hx]
    have hbd : ∀ x ∈ U, f x < (2 * R + 1).toNat / c + 1 := by
      intro x hx
      have h1 : f x ≤ ((2 * R : ℤ) / (c : ℤ)).toNat := by
        simp only [hf]
        exact Int.toNat_le_toNat (Int.ediv_le_ediv hcZ (hxm x hx))
      rw [hconv] at h1
      have h2 : (2 * R).toNat / c ≤ (2 * R + 1).toNat / c :=
        Nat.div_le_div_right (Int.toNat_le_toNat (by omega))
      omega
    have hinj : Set.InjOn f (↑U : Set ℤ) := by
      intro x hx y hy hxy
      simp only [hf] at hxy
      have hx0 : (0 : ℤ) ≤ (x - m) / (c : ℤ) := Int.ediv_nonneg (hxm0 x hx) (le_of_lt hcZ)
      have hy0 : (0 : ℤ) ≤ (y - m) / (c : ℤ) := Int.ediv_nonneg (hxm0 y hy) (le_of_lt hcZ)
      have h1 : (x - m) / (c : ℤ) = (y - m) / (c : ℤ) := by
        have e1 : (((x - m) / (c : ℤ)).toNat : ℤ) = (x - m) / (c : ℤ) := Int.toNat_of_nonneg hx0
        have e2 : (((y - m) / (c : ℤ)).toNat : ℤ) = (y - m) / (c : ℤ) := Int.toNat_of_nonneg hy0
        have e3 : (((x - m) / (c : ℤ)).toNat : ℤ) = (((y - m) / (c : ℤ)).toNat : ℤ) := by
          exact_mod_cast hxy
        rw [e1, e2] at e3
        exact e3
      have hdx : (c : ℤ) ∣ x - m := hcong x hx m hmU
      have hdy : (c : ℤ) ∣ y - m := hcong y hy m hmU
      have m1 : (c : ℤ) * ((x - m) / (c : ℤ)) = x - m := Int.mul_ediv_cancel' hdx
      have m2 : (c : ℤ) * ((y - m) / (c : ℤ)) = y - m := Int.mul_ediv_cancel' hdy
      rw [h1] at m1
      linarith
    have hmaps2 : Set.MapsTo f (↑U : Set ℤ)
        (↑(Finset.range ((2 * R + 1).toNat / c + 1)) : Set ℕ) := by
      intro x hx
      simpa [Finset.mem_range] using hbd x hx
    have hfin := Finset.card_le_card_of_injOn f hmaps2 hinj
    simpa using hfin

/-- **The pair count used by the trivial estimates of *FI* §§17, 21–22.**

For a fixed Gaussian integer `z₁ = r₁ + is₁` with `r₁` coprime to `c`, the number of `z₂` in the
box `|re|, |im| ≤ R` with `c ∣ |Δ(z₁,z₂)|`, `Δ(z₁,z₂) = Im(z̄₁z₂) = r₁s₂ − r₂s₁`, is

  `≤ (2R+1)·((2R+1)/c + 1)`:

for each of the at most `2R+1` values of `r₂` the condition `r₁s₂ ≡ s₁r₂ (mod c)` determines `s₂`
in a single residue class mod `c` (this is where `(r₁,c) = 1` is used), and `[−R,R]` contains at
most `(2R+1)/c + 1` integers of any one class mod `c`.

This is the "elementary counting" that converts the congruence `4d ∣ |Δ|` (or `4bd ∣ |Δ|`) of the
area-7 sums into a bound of the shape `(box)/c + √(box)`, the input of *FI*'s trivial estimates
("we reduce the summation to `b ≤ X` and estimate the remaining sum trivially by `O(X^{−1}N²)`")
and of the fibre count in Lemma 21.2.

Verified numerically (no counterexample over `0 ≤ R ≤ 13`, `1 ≤ c ≤ 15`, `|r₁|,|s₁| ≤ 8`,
`(r₁,c) = 1`).  Without `(r₁,c) = 1` the bound is **false** (e.g. `R = 1`, `c = 2`,
`z₁ = −6 − 6i`: `Δ = 6(r₂ − s₂)` is always even, so all `9` values of `z₂` satisfy it, while the
bound is `6`); the general case carries the factor `gcd(r₁,c)`, which is why the coprimality is a
hypothesis here (the final assembly applies the count to the coprimality-restricted sums of §17,
where `(z₁, z₂) = 1` and primitivity give `(r₁, 4bd) = 1` in the ranges that matter). -/
theorem card_gBox_filter_dvd_absDelta (z1 : GaussianInt) (R : ℤ) (c : ℕ) (hc : 0 < c)
    (hcop : IsCoprime z1.re (c : ℤ)) :
    ((Work.FIPlan.gBox R).filter (fun z2 => c ∣ Work.FIPlan.absDelta z1 z2)).card
      ≤ (2 * R + 1).toNat * ((2 * R + 1).toNat / c + 1) := by
  set S : Finset GaussianInt :=
    (Work.FIPlan.gBox R).filter (fun z2 => c ∣ Work.FIPlan.absDelta z1 z2) with hS
  have hmaps : Set.MapsTo (fun z : GaussianInt => z.re) (↑S : Set GaussianInt)
      (↑(Finset.Icc (-R) R) : Set ℤ) := by
    intro z hz
    have hz' : z ∈ S := hz
    rw [hS, Finset.mem_filter] at hz'
    have h := mem_gBox_iff.mp hz'.1
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber : ∀ b ∈ Finset.Icc (-R) R,
      (S.filter (fun z => z.re = b)).card ≤ (2 * R + 1).toNat / c + 1 := by
    intro b hb
    set F : Finset GaussianInt := S.filter (fun z => z.re = b) with hF
    set U : Finset ℤ := F.image (fun z => z.im) with hU
    have hFU : U.card = F.card := by
      rw [hU]
      refine Finset.card_image_of_injOn ?_
      intro x hx y hy hxy
      have hx' : x ∈ S ∧ x.re = b := by
        have h2 : x ∈ S.filter (fun z => z.re = b) := hx
        exact Finset.mem_filter.mp h2
      have hy' : y ∈ S ∧ y.re = b := by
        have h2 : y ∈ S.filter (fun z => z.re = b) := hy
        exact Finset.mem_filter.mp h2
      exact Zsqrtd.ext (by rw [hx'.2, hy'.2]) hxy
    rw [← hFU]
    refine card_le_div_of_pairwise_dvd R c hc U ?_ ?_
    · intro x hx
      rw [hU] at hx
      obtain ⟨z, hzF, rfl⟩ := Finset.mem_image.mp hx
      have hzF' : z ∈ S ∧ z.re = b := by
        have h2 : z ∈ S.filter (fun z => z.re = b) := hzF
        exact Finset.mem_filter.mp h2
      have hzg : z ∈ Work.FIPlan.gBox R := (Finset.mem_filter.mp hzF'.1).1
      have h := mem_gBox_iff.mp hzg
      exact Finset.mem_Icc.mpr ⟨h.2.2.1, h.2.2.2⟩
    · intro x hx y hy
      rw [hU] at hx hy
      obtain ⟨z, hzF, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨w, hwF, rfl⟩ := Finset.mem_image.mp hy
      have hzF' : z ∈ S ∧ z.re = b := by
        have h2 : z ∈ S.filter (fun z => z.re = b) := hzF
        exact Finset.mem_filter.mp h2
      have hwF' : w ∈ S ∧ w.re = b := by
        have h2 : w ∈ S.filter (fun z => z.re = b) := hwF
        exact Finset.mem_filter.mp h2
      have hzP : c ∣ Work.FIPlan.absDelta z1 z := (Finset.mem_filter.mp hzF'.1).2
      have hwP : c ∣ Work.FIPlan.absDelta z1 w := (Finset.mem_filter.mp hwF'.1).2
      have hdz0 := dvd_Delta_of_dvd_absDelta hzP
      have hdw0 := dvd_Delta_of_dvd_absDelta hwP
      have hdz : (c : ℤ) ∣ z1.re * z.im - z1.im * b := by
        simpa [Delta_eq z1 z, hzF'.2] using hdz0
      have hdw : (c : ℤ) ∣ z1.re * w.im - z1.im * b := by
        simpa [Delta_eq z1 w, hwF'.2] using hdw0
      have hkey : (c : ℤ) ∣ z1.re * (z.im - w.im) := by
        have h := dvd_sub hdz hdw
        have he : z1.re * z.im - z1.im * b - (z1.re * w.im - z1.im * b)
            = z1.re * (z.im - w.im) := by ring_nf
        rwa [he] at h
      exact hcop.symm.dvd_of_dvd_mul_left hkey
  calc S.card = ∑ b ∈ Finset.Icc (-R) R, (S.filter (fun z => z.re = b)).card := hcard
    _ ≤ ∑ _b ∈ Finset.Icc (-R) R, ((2 * R + 1).toNat / c + 1) := Finset.sum_le_sum hfiber
    _ = (Finset.Icc (-R) R).card * ((2 * R + 1).toNat / c + 1) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (2 * R + 1).toNat * ((2 * R + 1).toNat / c + 1) := by
        rw [Int.card_Icc]
        congr 1
        ring_nf

end

end Work.FIArea7
