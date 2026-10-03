/-
# `Submission.Work.FIArea7.reflSign_separable` — the separability of the reflection sign

The sign

  `reflSign z₁ z₂ = 1` if `r₁r₂ > 0`, `= 1` if `r₁` and `Δ(z₁,z₂)` have the same sign,
  `= -1` otherwise

of `ReflectAlg` is *not* a function of the residue classes of `(r₁,r₂)` mod 8, but on the polar
box (5.14) of *FI* it is **separable**: either it is identically `1`, or it is the product
`sign(r₁)·sign(r₂)` of a function of `z₁` with a function of `z₂`.  This is what lets the
reflection of §17 be absorbed into a *product* of two sums.

The only input is the geometry of the sector: `4θ < 1` means the sector (5.12)
`φ < α ≤ φ + 2πθ` has angular width `2πθ < π/2`, so

* the principal arguments of all box points lie in a real interval of length `2πθ < π/2`,
  hence pairwise differ by less than `π/2`;
* `Δ(z₁,z₂) = |z₁||z₂|·sin(α₂ − α₁)` (proved here from `Work.FIArea4.im_starRingEnd_mul`),
  so on the box the sign of `Δ(z₁,z₂)` is exactly the sign of `α₂ − α₁`;
* since the box contains no point with `re = 0` (primitivity: `re` is odd) and the sign of `re` is
  the sign of `cos α`, an interval of length `< π/2` meets the zeros of `cos` at most once, so the
  relative order of "`re > 0`-points" and "`re < 0`-points" is *uniform*:
  either every positive-`re` point has smaller argument than every negative-`re` point, or
  conversely.  `reflSign ≡ 1` in the first case and `reflSign = sign(r₁)sign(r₂)` in the second.
-/
import Mathlib
import Submission.Work.FIArea7.ReflectAlg
import Submission.Work.FITop3.Defs3
import Submission.Work.FIArea4.absDelta_le_sector

set_option autoImplicit false

namespace Work.FIArea7

attribute [local instance] Classical.propDecidable

variable {Pa : Work.FITop.Params} {φ : ℝ}

/-! ## 1. The angular window of the polar box -/

/-- `4θ < 1` gives `2πθ < π/2`: the sector (5.12) spans less than a right angle. -/
lemma two_pi_theta_lt_pi_div_two (hθ : 4 * Pa.θ < 1) :
    2 * Real.pi * Pa.θ < Real.pi / 2 := by
  have h := Real.pi_pos
  nlinarith

/-- The sector hypothesis of the polar box (5.14): the principal argument lies in
`(φ, φ + 2πθ]`. -/
lemma box_arg_bounds {z : GaussianInt} (hz : Work.FITop3.InPolarBox Pa φ z) :
    φ < (z : ℂ).arg ∧ (z : ℂ).arg ≤ φ + 2 * Real.pi * Pa.θ := hz.2.2.2

/-- The window is non-degenerate as soon as it contains a point. -/
lemma two_pi_theta_pos {z : GaussianInt} (hz : Work.FITop3.InPolarBox Pa φ z) :
    0 < 2 * Real.pi * Pa.θ := by
  obtain ⟨ha, hb⟩ := box_arg_bounds hz
  linarith

/-- Any two arguments in the polar box differ by less than `π/2`. -/
lemma box_arg_diff_lt_pi_div_two (hθ : 4 * Pa.θ < 1) {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2) :
    |(z1 : ℂ).arg - (z2 : ℂ).arg| < Real.pi / 2 := by
  obtain ⟨h1a, h1b⟩ := box_arg_bounds h1
  obtain ⟨h2a, h2b⟩ := box_arg_bounds h2
  have hL := two_pi_theta_lt_pi_div_two (Pa := Pa) hθ
  rw [abs_lt]
  constructor <;> linarith

/-! ## 2. The box points, and `Δ` against the arguments -/

/-- A box point has odd real part (primitivity), in particular `re ≠ 0`. -/
lemma box_re_ne_zero {z : GaussianInt} (hz : Work.FITop3.InPolarBox Pa φ z) : z.re ≠ 0 := by
  obtain ⟨hodd, -, -⟩ := hz.1
  obtain ⟨k, hk⟩ := hodd
  omega

/-- A box point is a non-zero complex number. -/
lemma box_toComplex_ne_zero {z : GaussianInt} (hz : Work.FITop3.InPolarBox Pa φ z) :
    (z : ℂ) ≠ 0 := by
  intro h
  have hz0 : z = 0 := GaussianInt.toComplex_eq_zero.mp h
  exact box_re_ne_zero hz (by rw [hz0]; rfl)

/-- The real part of a box point is positive in `ℂ` as soon as it is in `ℤ[i]`. -/
lemma re_pos_toComplex {z : GaussianInt} (h : 0 < z.re) : 0 < (z : ℂ).re := by
  rw [← GaussianInt.intCast_re]; exact_mod_cast h

/-- The real part of a box point is negative in `ℂ` as soon as it is in `ℤ[i]`. -/
lemma re_neg_toComplex {z : GaussianInt} (h : z.re < 0) : (z : ℂ).re < 0 := by
  rw [← GaussianInt.intCast_re]; exact_mod_cast h

/-- `Δ(z₁,z₂) = |z₁||z₂|·sin(α₂ − α₁)` for the determinant `Δ(z₁,z₂) = Im(z̄₁z₂)`. -/
lemma Delta_cast_eq (z1 z2 : GaussianInt) :
    (Work.FIPlan.Delta z1 z2 : ℝ)
      = ‖(z1 : ℂ)‖ * ‖(z2 : ℂ)‖ * Real.sin ((z2 : ℂ).arg - (z1 : ℂ).arg) := by
  rw [Work.FIPlan.Delta, GaussianInt.intCast_im, GaussianInt.toComplex_mul,
      GaussianInt.toComplex_star]
  exact Work.FIArea4.im_starRingEnd_mul (z1 : ℂ) (z2 : ℂ)

/-- On the polar box, `α₁ < α₂` forces `Δ(z₁,z₂) > 0` (the angular difference is in `(0, π)`). -/
lemma Delta_pos_of_arg_lt (hθ : 4 * Pa.θ < 1) {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2)
    (h : (z1 : ℂ).arg < (z2 : ℂ).arg) : 0 < Work.FIPlan.Delta z1 z2 := by
  have hdiff := box_arg_diff_lt_pi_div_two (Pa := Pa) (φ := φ) hθ h1 h2
  have hlt : (z2 : ℂ).arg - (z1 : ℂ).arg < Real.pi := by
    have := (abs_lt.mp hdiff).1
    linarith [Real.pi_pos]
  have hp1 : (0 : ℝ) < ‖(z1 : ℂ)‖ := norm_pos_iff.mpr (box_toComplex_ne_zero h1)
  have hp2 : (0 : ℝ) < ‖(z2 : ℂ)‖ := norm_pos_iff.mpr (box_toComplex_ne_zero h2)
  have hreal : (0 : ℝ) < (Work.FIPlan.Delta z1 z2 : ℝ) := by
    rw [Delta_cast_eq]
    exact mul_pos (mul_pos hp1 hp2) (Real.sin_pos_of_pos_of_lt_pi (by linarith) hlt)
  exact Int.cast_pos.mp hreal

/-- On the polar box, `α₂ < α₁` forces `Δ(z₁,z₂) < 0`. -/
lemma Delta_neg_of_arg_gt (hθ : 4 * Pa.θ < 1) {z1 z2 : GaussianInt}
    (h1 : Work.FITop3.InPolarBox Pa φ z1) (h2 : Work.FITop3.InPolarBox Pa φ z2)
    (h : (z2 : ℂ).arg < (z1 : ℂ).arg) : Work.FIPlan.Delta z1 z2 < 0 := by
  have hdiff := box_arg_diff_lt_pi_div_two (Pa := Pa) (φ := φ) hθ h1 h2
  have hgt : -Real.pi < (z2 : ℂ).arg - (z1 : ℂ).arg := by
    have := (abs_lt.mp hdiff).2
    linarith [Real.pi_pos]
  have hp1 : (0 : ℝ) < ‖(z1 : ℂ)‖ := norm_pos_iff.mpr (box_toComplex_ne_zero h1)
  have hp2 : (0 : ℝ) < ‖(z2 : ℂ)‖ := norm_pos_iff.mpr (box_toComplex_ne_zero h2)
  have hreal : (Work.FIPlan.Delta z1 z2 : ℝ) < 0 := by
    rw [Delta_cast_eq]
    exact mul_neg_of_pos_of_neg (mul_pos hp1 hp2)
      (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) hgt)
  exact_mod_cast hreal

/-! ## 3. The sign of `re` in terms of the argument -/

/-- `re z > 0` iff the principal argument lies in `(-π/2, π/2)`. -/
lemma abs_arg_lt_of_re_pos {z : ℂ} (hz : 0 < z.re) : |z.arg| < Real.pi / 2 :=
  Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)

/-- `re z < 0` iff the principal argument lies outside `[-π/2, π/2]`. -/
lemma abs_arg_gt_of_re_neg {z : ℂ} (hz : z.re < 0) : Real.pi / 2 < |z.arg| := by
  have : ¬ (|z.arg| ≤ Real.pi / 2) := by
    rw [Complex.abs_arg_le_pi_div_two_iff]
    linarith
  exact lt_of_not_ge this

/-! ## 4. The dichotomy of the orientations -/

/-- **The orientation dichotomy.**  The polar box splits its points into those with `re > 0` and
those with `re < 0`; the arguments of the two classes are then *uniformly ordered*: either every
positive-`re` point has smaller argument than every negative-`re` point, or the opposite.

Indeed the arguments of all box points lie in an interval of length `2πθ < π/2`, and `cos` vanishes
there at most once, while its sign is the sign of `re`. -/
lemma arg_dichotomy (hθ : 4 * Pa.θ < 1) :
    (∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 →
        Work.FITop3.InPolarBox Pa φ z2 → 0 < z1.re → z2.re < 0 →
        (z1 : ℂ).arg < (z2 : ℂ).arg) ∨
    (∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 →
        Work.FITop3.InPolarBox Pa φ z2 → 0 < z1.re → z2.re < 0 →
        (z2 : ℂ).arg < (z1 : ℂ).arg) := by
  by_cases h : ∃ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 ∧
      Work.FITop3.InPolarBox Pa φ z2 ∧ 0 < z1.re ∧ z2.re < 0 ∧ (z1 : ℂ).arg < (z2 : ℂ).arg
  · -- some positive-`re` point precedes some negative-`re` point: the orientation is uniform
    left
    obtain ⟨w1, w2, hw1, hw2, hw1re, hw2re, hw12⟩ := h
    have hw1abs : |(w1 : ℂ).arg| < Real.pi / 2 := abs_arg_lt_of_re_pos (re_pos_toComplex hw1re)
    have hw1gt : -(Real.pi / 2) < (w1 : ℂ).arg := (abs_lt.mp hw1abs).1
    have hw2abs : Real.pi / 2 < |(w2 : ℂ).arg| := abs_arg_gt_of_re_neg (re_neg_toComplex hw2re)
    -- the crossing of the imaginary axis happens at `α = π/2 (mod 2π)`; in particular both
    -- witnesses lie strictly inside the right half of the window
    have hw2pos : Real.pi / 2 < (w2 : ℂ).arg := by
      rcases lt_abs.mp hw2abs with h' | h'
      · exact h'
      · have h'' : (w2 : ℂ).arg < -(Real.pi / 2) := by linarith
        exact absurd hw12 (not_lt.mpr (le_of_lt (lt_trans h'' hw1gt)))
    have hw1pos : 0 < (w1 : ℂ).arg := by
      have := (abs_lt.mp (box_arg_diff_lt_pi_div_two (Pa := Pa) (φ := φ) hθ hw1 hw2)).1
      linarith
    -- every box point has argument within `π/2` of `arg w₁`, hence inside `(-π/2, π)`
    intro z1 z2 hz1 hz2 hz1re hz2re
    have hz1abs : |(z1 : ℂ).arg| < Real.pi / 2 := abs_arg_lt_of_re_pos (re_pos_toComplex hz1re)
    have hz2abs : Real.pi / 2 < |(z2 : ℂ).arg| := abs_arg_gt_of_re_neg (re_neg_toComplex hz2re)
    have hz1lt : (z1 : ℂ).arg < Real.pi / 2 := (abs_lt.mp hz1abs).2
    have hlow : -(Real.pi / 2) < (z2 : ℂ).arg := by
      have := (abs_lt.mp (box_arg_diff_lt_pi_div_two (Pa := Pa) (φ := φ) hθ hz2 hw1)).1
      linarith
    have hz2gt : Real.pi / 2 < (z2 : ℂ).arg := by
      rcases lt_abs.mp hz2abs with h' | h'
      · exact h'
      · exfalso; linarith
    linarith
  · -- no positive-`re` point precedes a negative-`re` one: the opposite orientation
    right
    intro z1 z2 hz1 hz2 hz1re hz2re
    have hz1abs : |(z1 : ℂ).arg| < Real.pi / 2 := abs_arg_lt_of_re_pos (re_pos_toComplex hz1re)
    have hz2abs : Real.pi / 2 < |(z2 : ℂ).arg| := abs_arg_gt_of_re_neg (re_neg_toComplex hz2re)
    have hle : (z2 : ℂ).arg ≤ (z1 : ℂ).arg :=
      not_lt.mp (fun hlt => h ⟨z1, z2, hz1, hz2, hz1re, hz2re, hlt⟩)
    refine lt_of_le_of_ne hle ?_
    intro heq
    rw [heq] at hz2abs
    linarith [(abs_lt.mp hz1abs).2]

/-! ## 5. The separability of `reflSign` -/

theorem reflSign_separable {Pa : Work.FITop.Params} {φ : ℝ} (hθ : 4 * Pa.θ < 1) :
    (∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 → Work.FITop3.InPolarBox Pa φ z2 →
        Work.FIArea7.reflSign z1 z2 = 1) ∨
    (∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 → Work.FITop3.InPolarBox Pa φ z2 →
        Work.FIArea7.reflSign z1 z2
          = (if 0 < z1.re then (1 : ℤ) else -1) * (if 0 < z2.re then (1 : ℤ) else -1)) := by
  rcases arg_dichotomy (Pa := Pa) (φ := φ) hθ with hd | hd
  · left
    intro z1 z2 h1 h2
    have hr1 := box_re_ne_zero h1
    have hr2 := box_re_ne_zero h2
    rw [reflSign]
    by_cases hprod : 0 < z1.re * z2.re
    · rw [if_pos hprod]
    · rw [if_neg hprod]
      have hcond : (0 < z1.re ∧ 0 < Work.FIPlan.Delta z1 z2) ∨
          (z1.re < 0 ∧ Work.FIPlan.Delta z1 z2 < 0) := by
        rcases lt_trichotomy z1.re 0 with h | h | h
        · -- `re z₁ < 0`, so `re z₂ > 0`; use the dichotomy with the roles swapped
          have hz2 : 0 < z2.re := by
            rcases lt_trichotomy z2.re 0 with h2' | h2' | h2'
            · exfalso; nlinarith
            · exact absurd h2' hr2
            · exact h2'
          exact Or.inr ⟨h, Delta_neg_of_arg_gt (Pa := Pa) (φ := φ) hθ h1 h2
            (hd z2 z1 h2 h1 hz2 h)⟩
        · exact absurd h hr1
        · have hz2 : z2.re < 0 := by
            rcases lt_trichotomy z2.re 0 with h2' | h2' | h2'
            · exact h2'
            · exact absurd h2' hr2
            · exfalso; nlinarith
          exact Or.inl ⟨h, Delta_pos_of_arg_lt (Pa := Pa) (φ := φ) hθ h1 h2
            (hd z1 z2 h1 h2 h hz2)⟩
      rw [if_pos hcond]
  · right
    intro z1 z2 h1 h2
    have hr1 := box_re_ne_zero h1
    have hr2 := box_re_ne_zero h2
    rw [reflSign]
    by_cases h1p : 0 < z1.re
    · by_cases h2p : 0 < z2.re
      · rw [if_pos (mul_pos h1p h2p), if_pos h1p, if_pos h2p]
        norm_num
      · have h2n : z2.re < 0 := lt_of_le_of_ne (le_of_not_gt h2p) hr2
        have hD : Work.FIPlan.Delta z1 z2 < 0 :=
          Delta_neg_of_arg_gt (Pa := Pa) (φ := φ) hθ h1 h2 (hd z1 z2 h1 h2 h1p h2n)
        have hprod : ¬ (0 < z1.re * z2.re) := by nlinarith
        have hcond : ¬ ((0 < z1.re ∧ 0 < Work.FIPlan.Delta z1 z2) ∨
            (z1.re < 0 ∧ Work.FIPlan.Delta z1 z2 < 0)) := by
          rintro (⟨-, hh⟩ | ⟨hh, -⟩)
          · linarith
          · linarith
        rw [if_neg hprod, if_neg hcond, if_pos h1p, if_neg h2p]
        norm_num
    · have h1n : z1.re < 0 := lt_of_le_of_ne (le_of_not_gt h1p) hr1
      by_cases h2p : 0 < z2.re
      · have hD : 0 < Work.FIPlan.Delta z1 z2 :=
          Delta_pos_of_arg_lt (Pa := Pa) (φ := φ) hθ h1 h2 (hd z2 z1 h2 h1 h2p h1n)
        have hprod : ¬ (0 < z1.re * z2.re) := by nlinarith
        have hcond : ¬ ((0 < z1.re ∧ 0 < Work.FIPlan.Delta z1 z2) ∨
            (z1.re < 0 ∧ Work.FIPlan.Delta z1 z2 < 0)) := by
          rintro (⟨hh, -⟩ | ⟨-, hh⟩)
          · linarith
          · linarith
        rw [if_neg hprod, if_neg hcond, if_neg h1p, if_pos h2p]
        norm_num
      · have h2n : z2.re < 0 := lt_of_le_of_ne (le_of_not_gt h2p) hr2
        have hprod : 0 < z1.re * z2.re := by nlinarith
        rw [if_pos hprod, if_neg h1p, if_neg h2p]
        norm_num

end Work.FIArea7
