/-
# `Submission.Work.FIArea6Hecke.R.HeckeDiscRed`

The reduction of a Gaussian integer into the fundamental box `[0, 4d-1]^2` of `Z[i]/(4d)`.

For a character `χ` modulo `4d` (`IsCharMod4dStrict`) the *period box*
`B = {z | z primary, 0 ≤ z.re ≤ 4d-1, 0 ≤ z.im ≤ 4d-1}` is a complete set of primary residues
modulo `4d`; the map `red d z = (z.re % 4d) + i (z.im % 4d)` is the canonical representative of the
class of `z`, and its basic properties (`red d z ∈ gBox (4d-1)`, `4d ∣ red d z - z`, and later
`IsPrimary z → IsPrimary (red d z)`) are what make `B` closed under `z ↦ red (z·α)` for primary `α`.
-/
import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea5.S16Hecke.primaryAux

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open Work.FIPlan

noncomputable section

/-- **The canonical representative modulo `4d`** of a Gaussian integer, taken coordinate-wise in
`[0, 4d-1]`: `red d z = (z.re % 4d) + i (z.im % 4d)`. -/
def red (d : ℕ) (z : GaussianInt) : GaussianInt :=
  ⟨z.re % ((4 * d : ℕ) : ℤ), z.im % ((4 * d : ℕ) : ℤ)⟩

/-- `4d` is a multiple of `red d z - z`: the reduction only changes the class modulo `4d`. -/
lemma red_sub_dvd (d : ℕ) (z : GaussianInt) :
    ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ red d z - z := by
  refine ⟨⟨-(z.re / (((4 * d : ℕ) : ℤ))), -(z.im / (((4 * d : ℕ) : ℤ)))⟩, ?_⟩
  ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_sub, Zsqrtd.im_sub, red,
    Zsqrtd.re_intCast, Zsqrtd.im_intCast]
  · have h := Int.emod_add_mul_ediv z.re (((4 * d : ℕ) : ℤ))
    linear_combination h
  · have h := Int.emod_add_mul_ediv z.im (((4 * d : ℕ) : ℤ))
    linear_combination h

/-- The reduction of any Gaussian integer lies in the box `gBox (4d-1)`. -/
lemma red_mem_gBox (d : ℕ) (hd : 1 ≤ d) (z : GaussianInt) :
    red d z ∈ Work.FIPlan.gBox (((4 * d : ℕ) : ℤ) - 1) := by
  rw [Work.FIArea5.S16Hecke.mem_gBox_iff]
  have hN : (0 : ℤ) < (((4 * d : ℕ) : ℤ)) := by
    have : 1 ≤ 4 * d := by omega
    exact_mod_cast this
  refine ⟨?_, ?_⟩ <;> simp only [red] <;> rw [Finset.mem_Icc]
  · exact ⟨by have := Int.emod_nonneg z.re (ne_of_gt hN); omega,
      by have := Int.emod_lt_of_pos z.re hN; omega⟩
  · exact ⟨by have := Int.emod_nonneg z.im (ne_of_gt hN); omega,
      by have := Int.emod_lt_of_pos z.im hN; omega⟩

/-- The reduction is the identity on the points of the fundamental box. -/
lemma red_eq_self_of_mem (d : ℕ) (hd : 1 ≤ d) {z : GaussianInt}
    (hz : z ∈ Work.FIPlan.gBox (((4 * d : ℕ) : ℤ) - 1))
    (hre : 0 ≤ z.re) (him : 0 ≤ z.im) : red d z = z := by
  obtain ⟨hzr, hzi⟩ := Work.FIArea5.S16Hecke.mem_gBox_iff.mp hz
  rw [Finset.mem_Icc] at hzr hzi
  have hN : (0 : ℤ) < (((4 * d : ℕ) : ℤ)) := by
    have : 1 ≤ 4 * d := by omega
    exact_mod_cast this
  ext <;> simp only [red]
  · exact Int.emod_eq_of_lt hre (by omega)
  · exact Int.emod_eq_of_lt him (by omega)

/-- The reduction depends only on the class modulo `4d`. -/
lemma red_congr (d : ℕ) {z w : GaussianInt}
    (h : ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - w) : red d z = red d w := by
  obtain ⟨c, hc⟩ := h
  have hre : (((4 * d : ℕ) : ℤ)) ∣ z.re - w.re := by
    refine ⟨c.re, ?_⟩
    have := congrArg Zsqrtd.re hc
    simpa [Zsqrtd.re_sub, Zsqrtd.re_mul] using this
  have him : (((4 * d : ℕ) : ℤ)) ∣ z.im - w.im := by
    refine ⟨c.im, ?_⟩
    have := congrArg Zsqrtd.im hc
    simpa [Zsqrtd.im_sub, Zsqrtd.im_mul] using this
  ext <;> simp only [red]
  · rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    exact (Int.dvd_iff_emod_eq_zero).mp hre
  · rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    exact (Int.dvd_iff_emod_eq_zero).mp him

/-- **Two box points with non-negative coordinates that are congruent modulo `4d` are equal.** -/
lemma box_eq_of_dvd_sub (d : ℕ) (hd : 1 ≤ d) {z w : GaussianInt}
    (hz : z ∈ Work.FIPlan.gBox (((4 * d : ℕ) : ℤ) - 1))
    (hw : w ∈ Work.FIPlan.gBox (((4 * d : ℕ) : ℤ) - 1))
    (hzre : 0 ≤ z.re) (hzim : 0 ≤ z.im) (hwre : 0 ≤ w.re) (hwim : 0 ≤ w.im)
    (h : ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ z - w) : z = w := by
  have h1 : red d z = z := red_eq_self_of_mem d hd hz hzre hzim
  have h2 : red d w = w := red_eq_self_of_mem d hd hw hwre hwim
  have h3 : red d z = red d w := red_congr d h
  rw [h1, h2] at h3
  exact h3

/-- `(1+i)^3` divides `4d` in `ℤ[i]`: `(1+i)^3·(-d(1+i)) = 4d` because `(1+i)^4 = -4`.  This is
what makes the *class* of a primary element modulo `4d` again primary. -/
lemma one_add_I_cube_dvd_fourD (d : ℕ) :
    ((1 + (⟨0,1⟩ : GaussianInt)) ^ 3) ∣ ((((4 * d : ℕ) : ℤ)) : GaussianInt) := by
  refine ⟨-(((d : ℤ)) : GaussianInt) * (1 + (⟨0,1⟩ : GaussianInt)), ?_⟩
  have h4 : ((1 + (⟨0,1⟩ : GaussianInt)) ^ 4) = (-4 : GaussianInt) := by decide
  have : (1 + (⟨0,1⟩ : GaussianInt)) ^ 3
        * (-(((d : ℤ)) : GaussianInt) * (1 + (⟨0,1⟩ : GaussianInt)))
      = -(((d : ℤ)) : GaussianInt) * ((1 + (⟨0,1⟩ : GaussianInt)) ^ 4) := by ring
  rw [this, h4]
  push_cast
  ring

end

end Work.FIArea6Hecke.R
