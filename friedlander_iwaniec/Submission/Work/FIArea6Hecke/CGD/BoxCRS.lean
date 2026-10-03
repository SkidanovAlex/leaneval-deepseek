import Mathlib
import Submission.Work.FIArea6Hecke.ConductorGaussSumDefs

/-!
# `Work.FIArea6Hecke.CGD.BoxCRS`

The box `gbox N = [0,N)² ⊂ ℤ[i]` is a complete residue system modulo `(N : ℤ[i])`,
and it has exactly `N * N` elements.

These are the two facts that let `condGaussSum`/`Gs` sum over the box instead of an
abstract complete residue system: every residue class mod `N` in `ℤ[i]` is hit exactly
once by the box, and the box has the expected cardinality.
-/

namespace Work.FIArea6Hecke.CGD

open Work.FIArea6Hecke.R

/-- Membership in `gbox N` is exactly the box condition `0 ≤ re < N`, `0 ≤ im < N`. -/
lemma mem_gbox_iff (N : ℕ) (s : GaussianInt) :
    s ∈ gbox N ↔ 0 ≤ s.re ∧ s.re < N ∧ 0 ≤ s.im ∧ s.im < N := by
  rw [gbox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_range] at h1 h2
    refine ⟨by simp, by simpa using (show (p.1 : ℤ) < N by exact_mod_cast h1),
            by simp, by simpa using (show (p.2 : ℤ) < N by exact_mod_cast h2)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(s.re.toNat, s.im.toNat), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [Finset.mem_range]; omega
    · rw [Finset.mem_range]; omega
    · ext <;> simp [h1, h3]

/-- The integer `(z % N).toNat` is a least non-negative residue of `z` modulo `N`. -/
lemma zmod_dvd_sub_toNat_emod (N : ℕ) (hN : N ≠ 0) (z : ℤ) :
    (N : ℤ) ∣ z - ((z % (N : ℤ)).toNat : ℤ) := by
  have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNne : (N : ℤ) ≠ 0 := ne_of_gt hNpos
  have h0 : (0 : ℤ) ≤ z % (N : ℤ) := Int.emod_nonneg _ hNne
  have ha : (((z % (N : ℤ)).toNat : ℤ)) = z % (N : ℤ) := Int.toNat_of_nonneg h0
  rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, ha,
      Int.emod_eq_of_lt h0 (Int.emod_lt_of_pos _ hNpos)]
  simp

/-- Two elements of `[0, N)` that are congruent modulo `N` coincide. -/
lemma int_eq_of_dvd_sub_of_mem (N : ℕ) {x a : ℤ}
    (hx0 : 0 ≤ x) (hxN : x < N) (ha0 : 0 ≤ a) (haN : a < N)
    (h : (N : ℤ) ∣ x - a) : x = a := by
  have hmod : x % (N : ℤ) = a % (N : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    exact Int.emod_eq_zero_of_dvd h
  rwa [Int.emod_eq_of_lt hx0 hxN, Int.emod_eq_of_lt ha0 haN] at hmod

/-- Divisibility in `ℤ[i]` by `(N : ℤ[i]) = ⟨N, 0⟩` is componentwise divisibility by `N`. -/
lemma gauss_dvd_re_im {N : ℕ} {z t : GaussianInt}
    (h : (N : GaussianInt) ∣ z - t) : (N : ℤ) ∣ z.re - t.re ∧ (N : ℤ) ∣ z.im - t.im := by
  obtain ⟨k, hk⟩ := h
  constructor
  · refine ⟨k.re, ?_⟩
    have hre := congrArg Zsqrtd.re hk
    rw [Zsqrtd.re_sub, Zsqrtd.re_mul] at hre
    simpa using hre
  · refine ⟨k.im, ?_⟩
    have him := congrArg Zsqrtd.im hk
    rw [Zsqrtd.im_sub, Zsqrtd.im_mul] at him
    simpa using him

/-- Conversely, componentwise divisibility by `N` gives divisibility by `(N : ℤ[i])`. -/
lemma gauss_dvd_of_re_im {N : ℕ} {z t : GaussianInt}
    (hr : (N : ℤ) ∣ z.re - t.re) (hi : (N : ℤ) ∣ z.im - t.im) :
    (N : GaussianInt) ∣ z - t := by
  obtain ⟨c, hc⟩ := hr
  obtain ⟨d, hd⟩ := hi
  refine ⟨⟨c, d⟩, ?_⟩
  ext <;> simp [Zsqrtd.re_sub, Zsqrtd.im_sub, hc, hd]

/-- The box `[0,N)²` is a complete residue system modulo `(N : ℤ[i])`, and has `N * N`
elements. -/
theorem BoxCRS (N : ℕ) (hN : N ≠ 0) :
    Work.FIArea6Hecke.R.IsCRS (N : GaussianInt) (Work.FIArea6Hecke.R.gbox N) ∧
      (Work.FIArea6Hecke.R.gbox N).card = N * N := by
  have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hNne : (N : ℤ) ≠ 0 := ne_of_gt hNpos
  constructor
  · intro z
    refine ⟨⟨((z.re % (N : ℤ)).toNat : ℤ), ((z.im % (N : ℤ)).toNat : ℤ)⟩,
      ⟨?_, ?_⟩, ?_⟩
    · rw [mem_gbox_iff]
      have ha : (((z.re % (N : ℤ)).toNat : ℤ)) = z.re % (N : ℤ) :=
        Int.toNat_of_nonneg (Int.emod_nonneg z.re hNne)
      have hb : (((z.im % (N : ℤ)).toNat : ℤ)) = z.im % (N : ℤ) :=
        Int.toNat_of_nonneg (Int.emod_nonneg z.im hNne)
      refine ⟨by simp, ?_, by simp, ?_⟩
      · rw [ha]; exact Int.emod_lt_of_pos z.re hNpos
      · rw [hb]; exact Int.emod_lt_of_pos z.im hNpos
    · apply gauss_dvd_of_re_im
      · exact zmod_dvd_sub_toNat_emod N hN z.re
      · exact zmod_dvd_sub_toNat_emod N hN z.im
    · rintro y ⟨hy, hydvd⟩
      rw [mem_gbox_iff] at hy
      obtain ⟨hy0, hyN, hy1, hy2⟩ := hy
      obtain ⟨hr, hi⟩ := gauss_dvd_re_im hydvd
      have hzr : (N : ℤ) ∣ z.re - ((z.re % (N : ℤ)).toNat : ℤ) :=
        zmod_dvd_sub_toNat_emod N hN z.re
      have hzi : (N : ℤ) ∣ z.im - ((z.im % (N : ℤ)).toNat : ℤ) :=
        zmod_dvd_sub_toNat_emod N hN z.im
      have ha0 : (0 : ℤ) ≤ ((z.re % (N : ℤ)).toNat : ℤ) := by positivity
      have haN : ((z.re % (N : ℤ)).toNat : ℤ) < N := by
        rw [Int.toNat_of_nonneg (Int.emod_nonneg z.re hNne)]
        exact Int.emod_lt_of_pos z.re hNpos
      have hb0 : (0 : ℤ) ≤ ((z.im % (N : ℤ)).toNat : ℤ) := by positivity
      have hbN : ((z.im % (N : ℤ)).toNat : ℤ) < N := by
        rw [Int.toNat_of_nonneg (Int.emod_nonneg z.im hNne)]
        exact Int.emod_lt_of_pos z.im hNpos
      have hyr : y.re = ((z.re % (N : ℤ)).toNat : ℤ) := by
        apply int_eq_of_dvd_sub_of_mem N hy0 hyN ha0 haN
        have := Int.dvd_sub hzr hr
        convert this using 1; ring
      have hyim : y.im = ((z.im % (N : ℤ)).toNat : ℤ) := by
        apply int_eq_of_dvd_sub_of_mem N hy1 hy2 hb0 hbN
        have := Int.dvd_sub hzi hi
        convert this using 1; ring
      ext <;> assumption
  · rw [gbox]
    have hf : Function.Injective
        (fun p : ℕ × ℕ => (⟨(p.1 : ℤ), (p.2 : ℤ)⟩ : GaussianInt)) := by
      intro p q h
      simp only [Zsqrtd.mk.injEq] at h
      exact Prod.ext (by exact_mod_cast h.1) (by exact_mod_cast h.2)
    rw [Finset.card_image_of_injective _ hf]
    exact (Finset.card_product (Finset.range N) (Finset.range N)).trans
      (by rw [Finset.card_range])

end Work.FIArea6Hecke.CGD
