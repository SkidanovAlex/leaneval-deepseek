import Mathlib
import Submission.Work.FIArea7.FIsymbols

namespace Work.FIArea7

/-! ## The two sign identities behind the multiplier rule (20.5)/(20.6)

The multiplier symbol `MultEps` of *FI* §20 is built from the Hilbert symbols at `∞`
of the real and imaginary parts of the two Gaussian integers.  The lemma
`multEps_separation` below separates the dependence: the combination
`2 · MultEps w z · (u,v)_∞` depends only on the *signs* of `v`, `r` and of `Re(wz)`.

The two arithmetic facts it rests on are the following; they are pure sign
computations on `ℤ` (there is no number theory left, only the four sign patterns
of `v` and `r` combined with the branch `ur > vs` resp. `ur < vs`).

* In the branch `ur > vs` the quantity to evaluate is `2 · (r,−v)_∞`.
* In the branch `ur < vs` the quantity to evaluate is `2 · (−r,v)_∞`. -/

lemma hilb_key_pos (v r : ℤ) (hv : v ≠ 0) (hr : r ≠ 0) :
    2 * HilbertInf r (-v) = 1 + Int.sign (v * r) - (Int.sign v - Int.sign r) := by
  rcases lt_trichotomy v 0 with hv' | hv' | hv'
  · rcases lt_trichotomy r 0 with hr' | hr' | hr'
    · have hH : HilbertInf r (-v) = 1 := by unfold HilbertInf; rw [if_neg (by omega)]
      rw [hH, Int.sign_mul, Int.sign_eq_neg_one_of_neg hv', Int.sign_eq_neg_one_of_neg hr']
      norm_num
    · exact absurd hr' hr
    · have hH : HilbertInf r (-v) = 1 := by unfold HilbertInf; rw [if_neg (by omega)]
      rw [hH, Int.sign_mul, Int.sign_eq_neg_one_of_neg hv', Int.sign_eq_one_of_pos hr']
      norm_num
  · exact absurd hv' hv
  · rcases lt_trichotomy r 0 with hr' | hr' | hr'
    · have hH : HilbertInf r (-v) = -1 := by unfold HilbertInf; rw [if_pos (by omega)]
      rw [hH, Int.sign_mul, Int.sign_eq_one_of_pos hv', Int.sign_eq_neg_one_of_neg hr']
      norm_num
    · exact absurd hr' hr
    · have hH : HilbertInf r (-v) = 1 := by unfold HilbertInf; rw [if_neg (by omega)]
      rw [hH, Int.sign_mul, Int.sign_eq_one_of_pos hv', Int.sign_eq_one_of_pos hr']
      norm_num

lemma hilb_key_neg (v r : ℤ) (hv : v ≠ 0) (hr : r ≠ 0) :
    2 * HilbertInf (-r) v = 1 + Int.sign (v * r) + (Int.sign v - Int.sign r) := by
  rcases lt_trichotomy v 0 with hv' | hv' | hv'
  · rcases lt_trichotomy r 0 with hr' | hr' | hr'
    · have hH : HilbertInf (-r) v = 1 := by unfold HilbertInf; rw [if_neg (by omega)]
      rw [hH, Int.sign_mul, Int.sign_eq_neg_one_of_neg hv', Int.sign_eq_neg_one_of_neg hr']
      norm_num
    · exact absurd hr' hr
    · have hH : HilbertInf (-r) v = -1 := by unfold HilbertInf; rw [if_pos (by omega)]
      rw [hH, Int.sign_mul, Int.sign_eq_neg_one_of_neg hv', Int.sign_eq_one_of_pos hr']
      norm_num
  · exact absurd hv' hv
  · rcases lt_trichotomy r 0 with hr' | hr' | hr'
    · have hH : HilbertInf (-r) v = 1 := by unfold HilbertInf; rw [if_neg (by omega)]
      rw [hH, Int.sign_mul, Int.sign_eq_one_of_pos hv', Int.sign_eq_neg_one_of_neg hr']
      norm_num
    · exact absurd hr' hr
    · have hH : HilbertInf (-r) v = 1 := by unfold HilbertInf; rw [if_neg (by omega)]
      rw [hH, Int.sign_mul, Int.sign_eq_one_of_pos hv', Int.sign_eq_one_of_pos hr']
      norm_num

/-- **(20.5)/(20.6), separated form.**  For `w = u+iv`, `z = r+is` with `v, r ≠ 0` and
`Re(wz) = ur − vs ≠ 0`, the multiplier `ε(w,z)` satisfies
`2 ε(w,z)·(u,v)_∞ = 1 + sign(vr) − (sign v − sign r)·sign(ur − vs)`. -/
theorem multEps_separation (u v r s : ℤ) (hv : v ≠ 0) (hr : r ≠ 0)
    (hne : u * r - v * s ≠ 0) :
    2 * MultEps (⟨u, v⟩ : GaussianInt) (⟨r, s⟩ : GaussianInt) * HilbertInf u v
      = 1 + Int.sign (v * r)
          - (Int.sign v - Int.sign r) * Int.sign (u * r - v * s) := by
  have hH : ∀ x y : ℤ, HilbertInf x y * HilbertInf x y = 1 := by
    intro x y; unfold HilbertInf; split_ifs <;> norm_num
  simp only [MultEps]
  rcases lt_trichotomy (v * s) (u * r) with hlt | heq | hgt
  · -- branch `ur > vs`: MultEps = (u,v)_∞ (r,−v)_∞, and the left factor cancels
    rw [if_pos (by linarith : u * r > v * s)]
    rw [Int.sign_eq_one_of_pos (by linarith : 0 < u * r - v * s)]
    simp only [mul_one]
    rw [← hilb_key_pos v r hv hr]
    calc 2 * (HilbertInf u v * HilbertInf r (-v)) * HilbertInf u v
        = 2 * HilbertInf r (-v) * (HilbertInf u v * HilbertInf u v) := by ring
      _ = 2 * HilbertInf r (-v) := by rw [hH]; ring
  · exact absurd (by linarith : u * r - v * s = 0) hne
  · -- branch `ur < vs`: MultEps = (u,v)_∞ (−r,v)_∞
    rw [if_neg (by linarith : ¬ u * r > v * s)]
    rw [Int.sign_eq_neg_one_of_neg (by linarith : u * r - v * s < 0)]
    have he : 1 + Int.sign (v * r) - (Int.sign v - Int.sign r) * (-1)
        = 1 + Int.sign (v * r) + (Int.sign v - Int.sign r) := by ring
    rw [he, ← hilb_key_neg v r hv hr]
    calc 2 * (HilbertInf u v * HilbertInf (-r) v) * HilbertInf u v
        = 2 * HilbertInf (-r) v * (HilbertInf u v * HilbertInf u v) := by ring
      _ = 2 * HilbertInf (-r) v := by rw [hH]; ring

end Work.FIArea7
