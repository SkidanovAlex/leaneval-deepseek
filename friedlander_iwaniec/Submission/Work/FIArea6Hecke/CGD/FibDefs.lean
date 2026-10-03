/-
# `Work.FIArea6Hecke.CGD.FibDefs`

The elementary vocabulary for reducing sums over the box `gbox N = [0,N)² ⊂ ℤ[i]` to sums over
a complete residue system mod `M`, where `N = gnorm M` is the norm of `M`.

* `crsRed N z` — the coordinatewise `mod N` reduction of `z`; it always lies in `gbox N` and
  satisfies `((N:ℤ) : ℤ[i]) ∣ z - crsRed N z`;
* `crsFib M N s = {a ∈ gbox N : M ∣ a - s}` — the elements of the box congruent to `s` mod `M`.

The main fact supplied here is that `gbox N` is a complete residue system modulo `N`: two of its
elements congruent mod `N` are equal, and `crsRed` is the corresponding reduction map.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.CGD.CrsCalculus

set_option autoImplicit false

namespace Work.FIArea6Hecke.CGD

open scoped BigOperators

noncomputable section

/-- Coordinatewise reduction modulo `N`, landing in the box `[0,N)²`. -/
def crsRed (N : ℕ) (z : GaussianInt) : GaussianInt :=
  ⟨z.re % (N : ℤ), z.im % (N : ℤ)⟩

/-- The elements of the box `gbox N = [0,N)²` which are `≡ s` mod `M`. -/
def crsFib (M : GaussianInt) (N : ℕ) (s : GaussianInt) : Finset GaussianInt :=
  @Finset.filter GaussianInt (fun a => M ∣ a - s) (Classical.decPred _)
    (Work.FIArea6Hecke.R.gbox N)

@[simp] lemma crsRed_re (N : ℕ) (z : GaussianInt) : (crsRed N z).re = z.re % (N : ℤ) := rfl

@[simp] lemma crsRed_im (N : ℕ) (z : GaussianInt) : (crsRed N z).im = z.im % (N : ℤ) := rfl

/-- Membership in the box, in coordinates. -/
lemma mem_gbox {N : ℕ} {z : GaussianInt} :
    z ∈ Work.FIArea6Hecke.R.gbox N ↔
      0 ≤ z.re ∧ z.re < (N : ℤ) ∧ 0 ≤ z.im ∧ z.im < (N : ℤ) := by
  constructor
  · intro hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    rw [Finset.product_eq_sprod, Finset.mem_product] at hp
    simp only [Finset.mem_range] at hp
    refine ⟨Int.natCast_nonneg _, ?_, Int.natCast_nonneg _, ?_⟩
    · show (p.1 : ℤ) < (N : ℤ); exact_mod_cast hp.1
    · show (p.2 : ℤ) < (N : ℤ); exact_mod_cast hp.2
  · rintro ⟨h1, h2, h3, h4⟩
    refine Finset.mem_image.mpr ⟨(z.re.toNat, z.im.toNat), ?_, ?_⟩
    · rw [Finset.product_eq_sprod, Finset.mem_product]
      exact ⟨by rw [Finset.mem_range, Int.toNat_lt h1]; exact h2,
        by rw [Finset.mem_range, Int.toNat_lt h3]; exact h4⟩
    · ext <;> simp [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h3]

/-- The box `gbox N = [0,N)²` has `N * N` elements. -/
lemma gbox_card (N : ℕ) : (Work.FIArea6Hecke.R.gbox N).card = N * N := by
  have hinj : Function.Injective
      (fun p : ℕ × ℕ => (⟨(p.1 : ℤ), (p.2 : ℤ)⟩ : GaussianInt)) := by
    rintro ⟨p1, p2⟩ ⟨q1, q2⟩ h
    have h1 : (p1 : ℤ) = (q1 : ℤ) := by simpa using congrArg Zsqrtd.re h
    have h2 : (p2 : ℤ) = (q2 : ℤ) := by simpa using congrArg Zsqrtd.im h
    exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)
  unfold Work.FIArea6Hecke.R.gbox
  rw [Finset.product_eq_sprod, Finset.card_image_of_injective _ hinj]
  simp [Finset.card_product]

/-- The coordinatewise `N`-reduction is `N`-congruent to the identity. -/
lemma crsRed_dvd (N : ℕ) (z : GaussianInt) : ((N : ℤ) : GaussianInt) ∣ z - crsRed N z := by
  refine ⟨⟨z.re / (N : ℤ), z.im / (N : ℤ)⟩, ?_⟩
  have hre : z.re - (crsRed N z).re = (N : ℤ) * (z.re / (N : ℤ)) := by
    simp only [crsRed_re]
    have := Int.emod_add_mul_ediv z.re (N : ℤ)
    linarith
  have him : z.im - (crsRed N z).im = (N : ℤ) * (z.im / (N : ℤ)) := by
    simp only [crsRed_im]
    have := Int.emod_add_mul_ediv z.im (N : ℤ)
    linarith
  ext
  · rw [Zsqrtd.re_sub, hre, Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
    ring
  · rw [Zsqrtd.im_sub, him, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast]
    ring

/-- `crsRed N` depends only on the class modulo `N`. -/
lemma crsRed_eq_of_dvd {N : ℕ} {x y : GaussianInt}
    (h : ((N : ℤ) : GaussianInt) ∣ x - y) : crsRed N x = crsRed N y := by
  obtain ⟨c, hc⟩ := h
  have hxre : x.re = y.re + (N : ℤ) * c.re := by
    have h2 := congrArg Zsqrtd.re hc
    simp only [Zsqrtd.re_sub, Zsqrtd.re_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast,
      mul_zero] at h2
    linarith
  have hxim : x.im = y.im + (N : ℤ) * c.im := by
    have h2 := congrArg Zsqrtd.im hc
    simp only [Zsqrtd.im_sub, Zsqrtd.im_mul, Zsqrtd.re_intCast, Zsqrtd.im_intCast] at h2
    linarith
  ext <;> simp only [crsRed_re, crsRed_im, hxre, hxim, Int.add_mul_emod_self_left]

/-- `crsRed` fixes the box pointwise. -/
lemma crsRed_id_of_mem_gbox {N : ℕ} {z : GaussianInt}
    (hz : z ∈ Work.FIArea6Hecke.R.gbox N) : crsRed N z = z := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_gbox.mp hz
  ext <;> simp only [crsRed_re, crsRed_im, Int.emod_eq_of_lt h1 h2, Int.emod_eq_of_lt h3 h4]

/-- `crsRed N` lands in the box. -/
lemma crsRed_mem_gbox {N : ℕ} (hN : 0 < N) (z : GaussianInt) :
    crsRed N z ∈ Work.FIArea6Hecke.R.gbox N := by
  rw [mem_gbox]
  have hN' : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  exact ⟨Int.emod_nonneg _ (ne_of_gt hN'), Int.emod_lt_of_pos _ hN',
    Int.emod_nonneg _ (ne_of_gt hN'), Int.emod_lt_of_pos _ hN'⟩

/-- Two box elements congruent modulo `N` coincide (the box is a CRS modulo `N`). -/
lemma eq_of_mem_gbox_of_dvd {N : ℕ} {a b : GaussianInt}
    (ha : a ∈ Work.FIArea6Hecke.R.gbox N) (hb : b ∈ Work.FIArea6Hecke.R.gbox N)
    (h : ((N : ℤ) : GaussianInt) ∣ a - b) : a = b := by
  rw [← crsRed_id_of_mem_gbox ha, ← crsRed_id_of_mem_gbox hb]
  exact crsRed_eq_of_dvd h

/-- Membership in a fibre, unfolded. -/
lemma mem_crsFib {M : GaussianInt} {N : ℕ} {s a : GaussianInt} :
    a ∈ crsFib M N s ↔ a ∈ Work.FIArea6Hecke.R.gbox N ∧ M ∣ a - s := by
  classical
  rw [crsFib, Finset.mem_filter]

end

end Work.FIArea6Hecke.CGD
