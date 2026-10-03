import Mathlib
import Submission.Work.FIArea7.multEps_separation
import Submission.Work.FIArea7.FIsymbols

namespace Work.FIArea7

/-! ## The multiplier rule (20.5)/(20.6) in the form needed by §22

`multEps_separation` evaluates `2·ε(w,z)·(u,v)_∞` for `w = u+iv`, `z = r+is` **provided**
`v ≠ 0` and `r ≠ 0`.  In the applications the second entry `z` is primary, so `r = z.re` is odd
and hence non-zero; but the first entry `w` may a priori be a rational integer (`w.im = 0`), and
then the separation lemma does not apply directly.  The present file closes that gap: the
primitiveness hypothesis `IsCoprime w.re w.im` forces `w.re = ±1` when `w.im = 0`, and the primary
condition then gives `w.re = 1`, for which both sides evaluate to `2`.

The two ingredients are

* `primary_re_eq_one_of_im_zero` — the degenerate case just described;
* `multEpsHilbert_int` — the integer identity, proved by `multEps_separation` when `w.im ≠ 0`
  and by direct evaluation when `w.im = 0`.

The target `multEpsHilbert` is the `ℂ`-valued form in which §22 uses the rule. -/

/-- In the degenerate case `w.im = 0`, primitivity of the coordinates (together with the primary
condition `w.im ≡ w.re - 1 (mod 4)`) forces `w.re = 1`. -/
lemma primary_re_eq_one_of_im_zero {w : GaussianInt} (hw : Work.FIPlan.IsPrimary w)
    (hc : IsCoprime w.re w.im) (hw0 : w.im = 0) : w.re = 1 := by
  have hunit : IsUnit w.re := isCoprime_zero_right.mp (by rw [hw0] at hc; exact hc)
  rcases Int.isUnit_iff.mp hunit with h | h
  · exact h
  · exfalso
    have h3 : w.im ≡ w.re - 1 [ZMOD 4] := hw.2.2
    rw [hw0] at h3
    have hmod : w.re ≡ 1 [ZMOD 4] := by
      rw [Int.modEq_iff_dvd] at h3 ⊢
      obtain ⟨k, hk⟩ := h3
      exact ⟨-k, by linarith⟩
    rw [h, Int.modEq_iff_dvd] at hmod
    norm_num at hmod

/-- **(20.5)/(20.6) as an identity in `ℤ`.**  For primary `w, z` with `IsCoprime w.re w.im`,
`2·MultEps w z·(w.re, w.im)_∞ = 1 + sign(w.im·z.re) − (sign w.im − sign z.re)·sign(Re(wz))`. -/
lemma multEpsHilbert_int {w z : GaussianInt}
    (hw : Work.FIPlan.IsPrimary w) (hc : IsCoprime w.re w.im) (hz : Work.FIPlan.IsPrimary z) :
    2 * MultEps w z * HilbertInf w.re w.im
      = 1 + Int.sign (w.im * z.re) - (Int.sign w.im - Int.sign z.re) * Int.sign ((w * z).re) := by
  have hzeq : ({ re := z.re, im := z.im } : GaussianInt) = z := by ext <;> simp
  have hweq : ({ re := w.re, im := w.im } : GaussianInt) = w := by ext <;> simp
  have hre : (w * z).re = w.re * z.re - w.im * z.im := Work.FIArea7.re_mul w z
  have hzr : z.re ≠ 0 := by
    obtain ⟨k, hk⟩ := hz.1
    intro h; rw [h] at hk; omega
  by_cases hw0 : w.im = 0
  · -- degenerate case `w` rational: then `w.re = 1` and both sides equal `2`
    have hwr : w.re = 1 := primary_re_eq_one_of_im_zero hw hc hw0
    have hM : MultEps w z = 1 := by
      unfold MultEps
      rw [hwr, hw0]
      split <;> simp [HilbertInf]
    have hH : HilbertInf w.re w.im = 1 := by rw [hwr, hw0]; simp [HilbertInf]
    rw [hM, hH, hw0, hre, hwr, hw0]
    simp only [one_mul, zero_mul, Int.sign_zero, sub_zero]
    rcases lt_trichotomy z.re 0 with h | h | h
    · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
    · exact absurd h hzr
    · rw [Int.sign_eq_one_of_pos h]; norm_num
  · -- non-degenerate case: `multEps_separation` applies
    have hne : w.re * z.re - w.im * z.im ≠ 0 := by
      intro h
      have h1 : Odd (w.re * z.re) := Odd.mul hw.1 hz.1
      have h2 : Even (w.im * z.im) := Even.mul_right hw.2.1 z.im
      obtain ⟨k, hk⟩ := h1
      obtain ⟨m, hm⟩ := h2
      omega
    have hsep := Work.FIArea7.multEps_separation w.re w.im z.re z.im hw0 hzr hne
    rw [hweq, hzeq, ← hre] at hsep
    exact hsep

/-- **(20.5)/(20.6) in the `ℂ`-valued form of §22.** -/
theorem multEpsHilbert {w z : GaussianInt}
    (hw : Work.FIPlan.IsPrimary w) (hc : IsCoprime w.re w.im) (hz : Work.FIPlan.IsPrimary z) :
    2 * (Work.FIArea7.MultEps w z : ℂ) * (Work.FIArea7.HilbertInf w.re w.im : ℂ)
      = 1 + (Int.sign (w.im * z.re) : ℂ)
        - ((Int.sign w.im - Int.sign z.re : ℤ) : ℂ) * (Int.sign ((w * z).re) : ℂ) := by
  have hZ := multEpsHilbert_int hw hc hz
  have hcast : ((2 * MultEps w z * HilbertInf w.re w.im : ℤ) : ℂ)
      = ((1 + Int.sign (w.im * z.re)
          - (Int.sign w.im - Int.sign z.re) * Int.sign ((w * z).re) : ℤ) : ℂ) := by
    rw [hZ]
  push_cast at hcast
  push_cast
  exact hcast

end Work.FIArea7
