import Mathlib

/-!
# E2b core: exp-pullback periodicity and circle/arc integral identities

The E2b deformation is done in the `w`-plane (`X = exp w`).  For an
integrand `h : ℂ → ℂ` (in the application `h = g·p·q·X⁻¹`, holomorphic off
the hedgehog) the pulled-back 1-form is

    pull h w := h (exp w) · exp w.

This module records the elementary integral facts that make the w-plane cell
telescoping work:

1. `pull_periodic`: `pull h` is periodic with period `2π·I`
   (`exp` is `2πi`-periodic), so radial and arc integrals of `pull h` are
   invariant under shifting their angle bounds by `2π`
   (`radInt_add_two_pi`, `arcInt_add_two_pi`);
2. `circle_eq_arc`: the circle integral of `h` over `|X| = exp B` equals
   `I • arcInt (pull h) B 0 (2π)` (change of variables `X = exp(B + iθ)`,
   `dX = I·exp(B+iθ) dθ`; Mathlib's `circleIntegral` uses exactly the
   parametrization `θ ↦ circleMap 0 R θ = R·exp(iθ)` with
   `deriv_circleMap`), so by periodicity it is `I • arcInt (pull h) B c
   (c + 2π)` over *any* full window.

(radial/arc integrals as in `Submission.Fold`: `radInt F a b c :=
∫ x in a..b, F (x + c·I)`, `arcInt F u c d := ∫ y in c..d, F (u + y·I)`.)

No sorries may remain; do not change the statements of the declarations.
-/

noncomputable section

open scoped Complex Real Interval
open Complex

namespace Submission.E2bCore

/-- The exp-pullback of `h` (the 1-form `h(exp w)·exp w·dw`). -/
def pull (h : ℂ → ℂ) (w : ℂ) : ℂ := h (Complex.exp w) * Complex.exp w

/-- `pull h` is `2πi`-periodic (because `exp` is). -/
lemma pull_periodic (h : ℂ → ℂ) (w : ℂ) :
    pull h (w + (2 * Real.pi) * Complex.I) = pull h w := by
  unfold pull
  have hexp : Complex.exp (w + (2 * Real.pi) * Complex.I) = Complex.exp w := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (Complex.exp_periodic w)
  rw [hexp]

/-- Radial-side integral along the ray at angle `c` (Re from `a` to `b`). -/
def radInt (F : ℂ → ℂ) (a b c : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, F (x + c * Complex.I))

/-- Arc integral at `Re = u` (radius `e^u`), angular range `[c,d]`. -/
def arcInt (F : ℂ → ℂ) (u c d : ℝ) : ℂ :=
  (∫ y : ℝ in c..d, F (u + y * Complex.I))

/-- Radial integrals are invariant under shifting the angle by `2π`
(periodicity of the pullback). -/
lemma radInt_add_two_pi (h : ℂ → ℂ) (a b c : ℝ) :
    radInt (pull h) a b (c + 2 * Real.pi) = radInt (pull h) a b c := by
  unfold radInt
  apply congrArg (fun f : ℝ → ℂ => ∫ x : ℝ in a..b, f x)
  funext x
  have hs : (x : ℂ) + (c + 2 * Real.pi : ℝ) * Complex.I
      = ((x : ℂ) + (c : ℂ) * Complex.I) + (2 * Real.pi) * Complex.I := by
    norm_num [Complex.ofReal_add, Complex.ofReal_mul]
    ring
  rw [hs]
  exact pull_periodic h ((x : ℂ) + (c : ℂ) * Complex.I)

/-- Arc integrals are invariant under shifting the whole window by `2π`
(periodicity of the pullback). -/
lemma arcInt_add_two_pi (h : ℂ → ℂ) (u c d : ℝ) :
    arcInt (pull h) u (c + 2 * Real.pi) (d + 2 * Real.pi) = arcInt (pull h) u c d := by
  unfold arcInt
  rw [← intervalIntegral.integral_comp_add_right (f := fun y : ℝ => pull h (u + y * Complex.I))
      (a := c) (b := d) (d := 2 * Real.pi)]
  congr 1
  funext y
  have hs : (u : ℂ) + (y + 2 * Real.pi : ℝ) * Complex.I
      = ((u : ℂ) + (y : ℂ) * Complex.I) + (2 * Real.pi) * Complex.I := by
    norm_num [Complex.ofReal_add, Complex.ofReal_mul]
    ring
  rw [hs]
  exact pull_periodic h ((u : ℂ) + (y : ℂ) * Complex.I)

/-- The full-window arc integral does not depend on the starting angle
(periodicity): `arcInt (pull h) B c (c + 2π) = arcInt (pull h) B 0 (2π)` for
every `c`.  (Proof: split `[c, c+2π]` at `0` and `2π`; the two outer pieces
are translates of each other by periodicity.) -/
lemma arcInt_window_shift (h : ℂ → ℂ) (B c : ℝ) :
    arcInt (pull h) B c (c + 2 * Real.pi) = arcInt (pull h) B 0 (2 * Real.pi) := by
  unfold arcInt
  let F : ℝ → ℂ := fun y => pull h (B + y * Complex.I)
  have hper : Function.Periodic F (2 * Real.pi) := by
    intro y
    unfold F
    have hs : (B : ℂ) + ((y + 2 * Real.pi : ℝ) : ℂ) * Complex.I
        = ((B : ℂ) + (y : ℂ) * Complex.I) + (2 * Real.pi) * Complex.I := by
      norm_num [Complex.ofReal_add, Complex.ofReal_mul]
      ring
    rw [hs]
    exact pull_periodic h ((B : ℂ) + (y : ℂ) * Complex.I)
  simpa [F] using (hper.intervalIntegral_add_eq c 0)

/-- `circleMap 0 (exp B) θ = exp (B + θ·I)`. -/
lemma circleMap_zero_exp {B : ℝ} (θ : ℝ) :
    circleMap (0 : ℂ) (Real.exp B) θ = Complex.exp (B + θ * Complex.I) := by
  rw [circleMap_zero, Complex.exp_add, ← Complex.ofReal_exp]

/-- **Circle integral = full-window arc integral.**  The circle integral of
`h` over `|X| = exp B` (Mathlib parametrization `circleMap 0 (exp B)`,
`deriv_circleMap`) equals `I • arcInt (pull h) B 0 (2π)`; hence, with
`arcInt_window_shift`, it equals `I • arcInt (pull h) B c (c + 2π)` for any
window start `c`. -/
lemma circle_eq_arc (h : ℂ → ℂ) (B : ℝ) :
    (∮ z in C((0 : ℂ), Real.exp B), h z) =
      Complex.I • arcInt (pull h) B 0 (2 * Real.pi) := by
  calc
    (∮ z in C((0 : ℂ), Real.exp B), h z)
        = (∫ θ : ℝ in 0..2 * Real.pi,
            Complex.I • (h (Complex.exp ((B : ℂ) + (θ : ℂ) * Complex.I)) *
              Complex.exp ((B : ℂ) + (θ : ℂ) * Complex.I))) := by
          rw [circleIntegral]
          refine intervalIntegral.integral_congr ?_
          intro θ hθ
          dsimp only
          rw [deriv_circleMap, circleMap_zero_exp]
          simp [smul_eq_mul]
          ring
    _ = Complex.I • (∫ θ : ℝ in 0..2 * Real.pi,
            h (Complex.exp ((B : ℂ) + (θ : ℂ) * Complex.I)) *
              Complex.exp ((B : ℂ) + (θ : ℂ) * Complex.I)) := by
          rw [intervalIntegral.integral_smul]
    _ = Complex.I • arcInt (pull h) B 0 (2 * Real.pi) := by
          rfl

/-- The full window version of `circle_eq_arc`, for a window `[c, c + 2π]`. -/
lemma circle_eq_arc_window (h : ℂ → ℂ) (B c : ℝ) :
    (∮ z in C((0 : ℂ), Real.exp B), h z) =
      Complex.I • arcInt (pull h) B c (c + 2 * Real.pi) := by
  rw [circle_eq_arc, arcInt_window_shift]

end Submission.E2bCore

end
