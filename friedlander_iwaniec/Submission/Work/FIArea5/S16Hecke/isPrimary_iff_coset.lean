import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs

namespace Work.FIArea5.S16Hecke

open Work.FIPlan

/-- `(1+i)^3 = -2 + 2i` in `ℤ[i]`. -/
private lemma one_add_I_cubed :
    (1 + (⟨0,1⟩ : GaussianInt)) ^ 3 = (⟨-2, 2⟩ : GaussianInt) := by decide

/-- Coordinates of the coset element `1 + (1+i)³(a+bi)`. -/
private lemma coset_re (a b : ℤ) :
    (1 + (⟨-2,2⟩ : GaussianInt) * ⟨a,b⟩).re = 1 - 2*a - 2*b := by
  simp [Zsqrtd.re_mul]; ring

private lemma coset_im (a b : ℤ) :
    (1 + (⟨-2,2⟩ : GaussianInt) * ⟨a,b⟩).im = 2*a - 2*b := by
  simp [Zsqrtd.im_mul]; ring

/-- **The primary condition is a lattice coset.**  A Gaussian integer is primary
(`z.re` odd, `z.im` even, `z.im ≡ z.re - 1 (mod 4)`) if and only if it lies in the coset
`1 + (1+i)³ℤ[i]` of the lattice `(1+i)³ℤ[i]` (of covolume `8`).  This is the form in which the
theta series of a Grössencharacter is summed (over the primary coset), and it is what allows the
periodic weight `w ↦ χ(1 + (1+i)³w)` of Poisson summation to be introduced.

Proof: `(1+i)³ = -2+2i`, so `z = 1 + (1+i)³(a+bi) = (1-2a-2b) + i(2a-2b)`; conversely for primary
`z` put `w = ((z.re - 1) + i z.im)/(1+i)³`, whose coordinates are
`(z.im - (z.re-1))/4` and `-(z.im + (z.re-1))/4`, both integers by the primary congruences. -/
theorem isPrimary_iff_coset (z : GaussianInt) :
    Work.FIPlan.IsPrimary z ↔ ∃ w : GaussianInt, z = 1 + (1 + (⟨0,1⟩ : GaussianInt))^3 * w := by
  constructor
  · -- primary `z` lies in the coset
    intro hz
    obtain ⟨hodd, heven, hmod⟩ := hz
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨m, hm0⟩ := heven
    have hm : z.im = 2 * m := by omega
    -- `4 ∣ (z.re - 1) - z.im = 2(k - m)`
    have hdvd : (4:ℤ) ∣ (z.re - 1) - z.im := Int.modEq_iff_dvd.mp hmod
    rw [hk, hm] at hdvd
    obtain ⟨t, ht⟩ := hdvd
    have hm' : m = k - 2 * t := by omega
    refine ⟨⟨-t, t - k⟩, ?_⟩
    rw [one_add_I_cubed]
    ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_add, Zsqrtd.im_add,
      Zsqrtd.re_one, Zsqrtd.im_one] <;> omega
  · -- every point of the coset is primary
    rintro ⟨w, rfl⟩
    obtain ⟨a, b, rfl⟩ : ∃ a b, w = ⟨a, b⟩ := ⟨w.re, w.im, by ext <;> rfl⟩
    rw [one_add_I_cubed]
    refine ⟨?_, ?_, ?_⟩
    · rw [coset_re]; exact ⟨-a-b, by ring⟩
    · rw [coset_im]; exact ⟨a-b, by ring⟩
    · rw [coset_im, coset_re, Int.modEq_iff_dvd]; exact ⟨-a, by ring⟩

end Work.FIArea5.S16Hecke
