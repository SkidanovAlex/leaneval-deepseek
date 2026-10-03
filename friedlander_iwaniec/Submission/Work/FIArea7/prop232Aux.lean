/-
# `Submission.Work.FIArea7.prop232Aux` — elementary lemmas for the assembly of *FI* Prop. 23.2

These are the small `ℤ[i]`-and-box facts that the reduction of *FI* (23.11)/(23.12) to the two
linear-form bounds needs:

* `mem_gBox_sqrt_of_gnorm_le` — the disc `|z|² ≤ N` lies in the box `gBox (⌊√N⌋)`;
* `isCoprime_of_coprime_gnorm` — coprime *norms* give coprime Gaussian integers, so that the
  coprimality condition `(z,w) = 1` in `K∗` is implied by `(|z|², |w|²) = 1`.
-/
import Mathlib
import Submission.Work.FIArea7.prop232Defs
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_norm_mul

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- `|Re z|² ≤ |z|²`. -/
lemma sq_natAbs_re_le_gnorm (z : GaussianInt) : z.re.natAbs ^ 2 ≤ Work.FIPlan.gnorm z := by
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, pow_two]
  exact Nat.le_add_right _ _

/-- `|Im z|² ≤ |z|²`. -/
lemma sq_natAbs_im_le_gnorm (z : GaussianInt) : z.im.natAbs ^ 2 ≤ Work.FIPlan.gnorm z := by
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, pow_two]
  exact Nat.le_add_left _ _

/-- A primary Gaussian integer has odd norm (a copy under a name that does not clash with the
similarly named lemma of `Work.FIArea7.KInner_bound_good`). -/
lemma gnorm_odd_of_primary {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) :
    Odd (Work.FIPlan.gnorm z) := odd_gnorm_of_isPrimary hz

/-- `‖z‖_{ℂ} = √|z|²` (a copy under a name that does not clash with
`Work.FIArea7.norm_toComplex_eq_sqrt`). -/
lemma norm_toComplex_sqrt (z : GaussianInt) :
    ‖z.toComplex‖ = Real.sqrt (((Work.FIPlan.gnorm z : ℕ)) : ℝ) := by
  have h2 : (((Work.FIPlan.gnorm z : ℕ)) : ℝ) = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
    have h3 : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 := Work.FIArea7.norm_eq z
    have h4 : (((Work.FIPlan.gnorm z : ℕ)) : ℤ) = z.re ^ 2 + z.im ^ 2 := by rw [← h3]
    exact_mod_cast h4
  have h : ‖z.toComplex‖ ^ 2 = (((Work.FIPlan.gnorm z : ℕ)) : ℝ) := by
    rw [Complex.sq_norm, Complex.normSq_apply, h2]
    rw [show (z.toComplex).re = (z.re : ℝ) from (GaussianInt.intCast_re z).symm,
      show (z.toComplex).im = (z.im : ℝ) from (GaussianInt.intCast_im z).symm]
    ring
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

/-- `‖ψ(z)‖ ≤ 1` for the Grössencharacter (17.17) whenever `‖χ‖ ≤ 1`. -/
lemma grossenChar_norm_le_one (chi : GaussianInt → ℂ) (k : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (z : GaussianInt) :
    ‖grossenChar chi k z‖ ≤ 1 := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [grossenChar]
    rcases eq_or_ne k 0 with rfl | hk
    · simpa using hchi 0
    · rw [show ((0 : GaussianInt) : ℂ) / ((‖((0 : GaussianInt) : ℂ)‖ : ℝ) : ℂ) = 0 by simp,
        zero_zpow _ hk, mul_zero, norm_zero]
      norm_num
  · have hzC : (z : ℂ) ≠ 0 := fun h => hz (GaussianInt.toComplex_injective (by simpa using h))
    have hnorm : ‖(z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      exact div_self (by simpa using hzC)
    have h1 : ‖grossenChar chi k z‖ ≤ ‖chi z‖ := by
      rw [grossenChar, norm_mul, norm_zpow, hnorm, one_zpow, mul_one]
    exact le_trans h1 (hchi z)

/-- The disc `|z|² ≤ N` is contained in the box `gBox (⌊√N⌋)`. -/
lemma mem_gBox_sqrt_of_gnorm_le {z : GaussianInt} {N : ℕ} (h : Work.FIPlan.gnorm z ≤ N) :
    z ∈ Work.FIPlan.gBox ((Nat.sqrt N : ℕ) : ℤ) := by
  have hre : z.re.natAbs ≤ Nat.sqrt N := by
    rw [Nat.le_sqrt, ← pow_two]
    exact le_trans (sq_natAbs_re_le_gnorm z) h
  have him : z.im.natAbs ≤ Nat.sqrt N := by
    rw [Nat.le_sqrt, ← pow_two]
    exact le_trans (sq_natAbs_im_le_gnorm z) h
  refine mem_gBox_mk_iff.mpr ⟨?_, ?_⟩
  · rw [Finset.mem_Icc]
    constructor <;> omega
  · rw [Finset.mem_Icc]
    constructor <;> omega

/-- Every divisor of `z` has norm dividing `|z|²`. -/
lemma gnorm_dvd_gnorm_of_dvd' {d z : GaussianInt} (h : d ∣ z) :
    Work.FIPlan.gnorm d ∣ Work.FIPlan.gnorm z := by
  obtain ⟨c, rfl⟩ := h
  rw [Work.FIArea7.gnorm_mul]
  exact dvd_mul_right _ _

/-- **The terms of the disc sum vanish for non-primitive `w`**: if `w` is primary but
`(w.re, w.im) ≠ 1` (so some `d ≥ 2` divides `w.re` and `w.im`), then `d` divides both coordinates
of `w * z` for *every* `z`, and `w * z` has nonzero real part as soon as `z` is primary; hence
`[w z] = 0`. -/
lemma JKSym_mul_eq_zero_of_not_isCoprime_re_im {w z : GaussianInt}
    (hw : Work.FIPlan.IsPrimary w) (hz : Work.FIPlan.IsPrimary z)
    (hnc : ¬ IsCoprime w.re w.im) : Work.FIArea7.JKSym (w * z) = 0 := by
  obtain ⟨hrw, hsw, _⟩ := hw
  obtain ⟨hrz, hsz, _⟩ := hz
  let d : ℕ := Int.gcd w.re w.im
  have hd_ne1 : d ≠ 1 := fun h => hnc (Int.isCoprime_iff_gcd_eq_one.mpr h)
  have hdvd_re : (d : ℤ) ∣ w.re := Int.gcd_dvd_left w.re w.im
  have hdvd_im : (d : ℤ) ∣ w.im := Int.gcd_dvd_right w.re w.im
  have hd_ne0 : d ≠ 0 := by
    intro h
    have h0 : (0 : ℤ) ∣ w.re := by simpa [h] using hdvd_re
    rcases h0 with ⟨k, hk⟩
    rw [zero_mul] at hk
    exact Int.not_odd_zero (hk ▸ hrw)
  -- `d` divides both coordinates of `w * z`
  have hdvd_a : (d : ℤ) ∣ (w * z).re := by
    rw [Work.FIArea7.re_mul]
    exact Int.dvd_sub (hdvd_re.mul_right z.re) (hdvd_im.mul_right z.im)
  have hdvd_b : (d : ℤ) ∣ (w * z).im := by
    rw [Work.FIArea7.im_mul]
    exact Int.dvd_add (hdvd_re.mul_right z.im) (hdvd_im.mul_right z.re)
  -- `w * z` has odd (hence nonzero) real part
  have hodd : Odd (w * z).re := by
    rw [Work.FIArea7.re_mul]
    exact (hrw.mul hrz).sub_even (hsw.mul_right z.im)
  have hre0 : (w * z).re ≠ 0 := fun h => Int.not_odd_zero (h ▸ hodd)
  have hdvd_a_nat : d ∣ (w * z).re.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
    exact hdvd_a
  have hdvd_b_nat : d ∣ (w * z).im.natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
    exact hdvd_b
  have hdvd_gcd : d ∣ ((w * z).im).gcd (↑((w * z).re.natAbs)) := by
    rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact Nat.dvd_gcd hdvd_b_nat hdvd_a_nat
  have hgcd_ne1 : ((w * z).im).gcd (↑((w * z).re.natAbs)) ≠ 1 := by
    intro h
    exact hd_ne1 (Nat.eq_one_of_dvd_one (h ▸ hdvd_gcd))
  have hzero : jacobiSym (w * z).im (w * z).re.natAbs = 0 := by
    rw [jacobiSym.eq_zero_iff]
    exact ⟨Int.natAbs_ne_zero.mpr hre0, hgcd_ne1⟩
  rw [JKSym, JKCoeff, hzero]
  simp

/-- Coprime norms imply coprime Gaussian integers: `(z,w) = 1` follows from
`(|z|², |w|²) = 1`. -/
lemma isCoprime_of_coprime_gnorm {z w : GaussianInt}
    (h : Nat.Coprime (Work.FIPlan.gnorm z) (Work.FIPlan.gnorm w)) : IsCoprime z w :=
  IsRelPrime.isCoprime fun d hdz hdw => by
    have h3 : Work.FIPlan.gnorm d ∣ 1 := by
      rw [← h]
      exact Nat.dvd_gcd (gnorm_dvd_gnorm_of_dvd' hdz) (gnorm_dvd_gnorm_of_dvd' hdw)
    rw [← Zsqrtd.norm_eq_one_iff]
    exact Nat.eq_one_of_dvd_one h3

/-- The primary elements of norm `≤ N` lie in the box `gBox (⌊√N⌋)`. -/
lemma primarySet_subset_gBox_sqrt {n N : ℕ} (h : n ≤ N) :
    primarySet n ⊆ Work.FIPlan.gBox ((Nat.sqrt N : ℕ) : ℤ) := by
  intro z hz
  exact mem_gBox_sqrt_of_gnorm_le (by rw [gnorm_of_mem_primarySet hz]; exact h)

end

end Work.FIArea7
