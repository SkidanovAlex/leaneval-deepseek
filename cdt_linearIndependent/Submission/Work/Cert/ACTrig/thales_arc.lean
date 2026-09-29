import Mathlib
import Submission.Work.Cert.Spec

/-!
# `thales_arc`: the arc of a circle lies inside the disk on its chord

For `0 ≤ s ≤ τ ≤ 1/4` and `Rr ≥ 0`, the point `Rr·e^{2πis}` lies in the closed disk whose
diameter is the chord `[Rr, Rr·e^{2πiτ}]` — i.e. it is at distance at most half the chord
length from the midpoint `Rr(1 + e^{2πiτ})/2` of that chord.

Writing `a = 2πs`, `b = 2πτ` (so `0 ≤ a ≤ b ≤ π/2`), the statement is equivalent to the real
trigonometric inequality `1 + cos b - cos a - cos (a - b) ≤ 0`, which follows from
`1 - cos (a-b) = 2 sin²((b-a)/2)` and `cos b - cos a = -2 sin((a+b)/2) sin((b-a)/2)`
together with the monotonicity of `sin` on `[0, π/2]`.
-/

namespace Work.Cert.ACTrig

/-- `rot t = e^{2πit}` written with the argument as a real number. -/
lemma rot_eq_exp (t : ℝ) :
    Submission.CDTPlan.rot t = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  unfold Submission.CDTPlan.rot
  congrm Complex.exp ?_
  push_cast
  ring

/-- The exponential difference of `thales_arc`, in real coordinates. -/
lemma exp_split (a b : ℝ) :
    Complex.exp (a * Complex.I) - (1 + Complex.exp (b * Complex.I)) / 2
      = ((Real.cos a - (1 + Real.cos b) / 2 : ℝ) : ℂ)
        + ((Real.sin a - Real.sin b / 2 : ℝ) : ℂ) * Complex.I := by
  rw [Complex.exp_ofReal_mul_I a, Complex.exp_ofReal_mul_I b]
  push_cast
  ring

/-- Squared distance from `e^{ia}` to the midpoint of the chord `[1, e^{ib}]`. -/
lemma normSq_exp_split (a b : ℝ) :
    Complex.normSq (Complex.exp (a * Complex.I) - (1 + Complex.exp (b * Complex.I)) / 2)
      = 3 / 2 + Real.cos b / 2 - Real.cos a - Real.cos (a - b) := by
  rw [exp_split, Complex.normSq_add_mul_I, Real.cos_sub]
  nlinarith [Real.cos_sq_add_sin_sq a, Real.cos_sq_add_sin_sq b]

/-- Squared length of the chord `[1, e^{ib}]`. -/
lemma sq_norm_chord (b : ℝ) :
    ‖1 - Complex.exp (b * Complex.I)‖ ^ 2 = 2 - 2 * Real.cos b := by
  have hsplit : (1 : ℂ) - Complex.exp (b * Complex.I)
      = ((1 - Real.cos b : ℝ) : ℂ) + ((-Real.sin b : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_ofReal_mul_I b]
    push_cast
    ring
  rw [Complex.sq_norm, hsplit, Complex.normSq_add_mul_I]
  nlinarith [Real.cos_sq_add_sin_sq b]

/-- The trigonometric core: for `0 ≤ a ≤ b ≤ π/2`, `1 + cos b - cos a - cos (a - b) ≤ 0`. -/
lemma cos_arc_ineq (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    1 + Real.cos b - Real.cos a - Real.cos (a - b) ≤ 0 := by
  have hd0 : 0 ≤ (b - a) / 2 := by linarith
  have hde : (b - a) / 2 ≤ (a + b) / 2 := by linarith
  have he2 : (a + b) / 2 ≤ Real.pi / 2 := by linarith
  have hsin : Real.sin ((b - a) / 2) ≤ Real.sin ((a + b) / 2) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) he2 hde
  have hsin0 : 0 ≤ Real.sin ((b - a) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hd0 (by linarith [Real.pi_pos])
  have key : 1 + Real.cos b - Real.cos a - Real.cos (a - b)
      = 2 * Real.sin ((b - a) / 2)
          * (Real.sin ((b - a) / 2) - Real.sin ((a + b) / 2)) := by
    have h1 : Real.cos (a - b) = 1 - 2 * Real.sin ((b - a) / 2) ^ 2 := by
      have h : a - b = -(2 * ((b - a) / 2)) := by ring
      rw [h, Real.cos_neg, Real.cos_two_mul, Real.sin_sq]
      ring
    have h2 : Real.cos b - Real.cos a
        = -2 * Real.sin ((a + b) / 2) * Real.sin ((b - a) / 2) := by
      rw [Real.cos_sub_cos b a]
      ring
    have e1 : 1 + Real.cos b - Real.cos a - Real.cos (a - b)
        = (1 - Real.cos (a - b)) + (Real.cos b - Real.cos a) := by ring
    rw [e1, h1, h2]
    ring
  rw [key]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

/-- The unit-circle form of `thales_arc`: for `0 ≤ a ≤ b ≤ π/2` the point `e^{ia}` lies in the
closed disk with diameter the chord `[1, e^{ib}]`. -/
lemma exp_arc_le (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ Real.pi / 2) :
    ‖Complex.exp (a * Complex.I) - (1 + Complex.exp (b * Complex.I)) / 2‖
      ≤ ‖1 - Complex.exp (b * Complex.I)‖ / 2 := by
  have hE : ‖Complex.exp (a * Complex.I) - (1 + Complex.exp (b * Complex.I)) / 2‖ ^ 2
      = 3 / 2 + Real.cos b / 2 - Real.cos a - Real.cos (a - b) := by
    rw [Complex.sq_norm]
    exact normSq_exp_split a b
  have hF : ‖1 - Complex.exp (b * Complex.I)‖ ^ 2 = 2 - 2 * Real.cos b := sq_norm_chord b
  have htrig := cos_arc_ineq a b ha hab hb
  have hsq : ‖Complex.exp (a * Complex.I) - (1 + Complex.exp (b * Complex.I)) / 2‖ ^ 2
      ≤ (‖1 - Complex.exp (b * Complex.I)‖ / 2) ^ 2 := by
    have h2' : (‖1 - Complex.exp (b * Complex.I)‖ / 2) ^ 2
        = ‖1 - Complex.exp (b * Complex.I)‖ ^ 2 / 4 := by ring
    rw [h2', hE, hF]
    nlinarith [htrig]
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity)] at h

/-- A circular arc lies inside the disk built on its chord ("Thales"), in the form needed for the
Theorem-A contour certificate. -/
theorem thales_arc (Rr τ s : ℝ) (hR : 0 ≤ Rr) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1/4) (hs0 : 0 ≤ s)
    (hs : s ≤ τ) :
    ‖Rr * Submission.CDTPlan.rot s - Rr * (1 + Submission.CDTPlan.rot τ) / 2‖ ≤
      Rr * ‖1 - Submission.CDTPlan.rot τ‖ / 2 := by
  have ha0 : 0 ≤ 2 * Real.pi * s := mul_nonneg (by positivity) hs0
  have hab : 2 * Real.pi * s ≤ 2 * Real.pi * τ := mul_le_mul_of_nonneg_left hs (by positivity)
  have hb1 : 2 * Real.pi * τ ≤ 2 * Real.pi * (1 / 4) := mul_le_mul_of_nonneg_left hτ (by positivity)
  have hb : 2 * Real.pi * τ ≤ Real.pi / 2 := by linarith
  have hkey := exp_arc_le (2 * Real.pi * s) (2 * Real.pi * τ) ha0 hab hb
  have hcore : ‖Submission.CDTPlan.rot s - (1 + Submission.CDTPlan.rot τ) / 2‖
      ≤ ‖1 - Submission.CDTPlan.rot τ‖ / 2 := by
    rw [rot_eq_exp s, rot_eq_exp τ]
    exact hkey
  have h1 : Rr * Submission.CDTPlan.rot s - Rr * (1 + Submission.CDTPlan.rot τ) / 2
      = (Rr : ℂ) * (Submission.CDTPlan.rot s - (1 + Submission.CDTPlan.rot τ) / 2) := by
    ring
  rw [h1]
  have h2 : ‖(Rr : ℂ) * (Submission.CDTPlan.rot s - (1 + Submission.CDTPlan.rot τ) / 2)‖
      = Rr * ‖Submission.CDTPlan.rot s - (1 + Submission.CDTPlan.rot τ) / 2‖ := by
    rw [norm_mul]
    simp [abs_of_nonneg hR]
  rw [h2]
  calc Rr * ‖Submission.CDTPlan.rot s - (1 + Submission.CDTPlan.rot τ) / 2‖
      ≤ Rr * (‖1 - Submission.CDTPlan.rot τ‖ / 2) := mul_le_mul_of_nonneg_left hcore hR
    _ = Rr * ‖1 - Submission.CDTPlan.rot τ‖ / 2 := by ring

end Work.Cert.ACTrig
