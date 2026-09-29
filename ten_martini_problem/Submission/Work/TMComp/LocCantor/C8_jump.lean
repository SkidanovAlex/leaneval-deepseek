import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.GlueDefs
import Submission.Work.TMComp.Kotani.cayley_defect
import Submission.Work.TMComp.Kotani.Psi_bounds
import Submission.Work.TMComp.Kotani.ell_defect_le
import Submission.Work.TMComp.Kotani.EllDerivDefs
import Submission.Work.TMComp.Kotani.mfun_props

/-!
# C8: the jump of `cayley ∘ Ψ` is controlled by the (K2)-integrand

The extension step of Kotani's theorem (`Kotani/kotani_local.lean`, `RedC8/rectangle_extension`)
needs, for a sequence `ε_j ↓ 0`, the *Euclidean* smallness of the jump of `cayley ∘ Ψ` across
the real axis,

`J_j := ‖cayley (Ψ (E₀+iε_j) y) - cayley (Ψ (E₀-iε_j) y)‖`,

in `L¹(dE)` for (a.e.) phase `y`.  The route's two available bounds are

* `J ≤ 2 (1/N₁ + 1/N₂)` — from `‖Ψ(E₀±iε)‖ ≤ 1/N_{1,2}` (`Psi_bounds.inv_norm_le`) and the
  elementary `‖cayley u - cayley v‖ ≤ 2(‖u‖ + ‖v‖)`; useful when `N₁,N₂` are large;
* `J ≤ 2 ‖a-c‖ / ‖defect‖` — Schwarz–Pick (`cayley_Psi_jump_le`); useful when the defect is large.

Neither is small on its own, and `RedC8/NOTES_route.md` records this as the gap of the route
("a fully rigorous treatment must split into these two regimes").  The two bounds are in fact
*simultaneously* enough: with `q := 1/N₁ + 1/N₂`, the (K2) identity

`K2 = im(defect) · ‖a-c‖² / (N₁ N₂ ‖defect‖²)`,   `im(defect) = N₁ + N₂ = q·N₁N₂`,

gives `(‖a-c‖/‖defect‖)² = K2 / q`, hence `J² ≤ 4 K2 / q`; combined with `J ≤ 2q` this gives

  `J³ = J·J² ≤ (2q)·(4K2/q) = 8 K2`,

i.e. the *cube* of the jump is bounded by the (K2)-integrand, with no case distinction and no
boundedness hypothesis on `N₁,N₂`.  In particular `K2 → 0` (which the (K2)-integral bound
supplies at a.e. `(E,y)`) forces `J → 0`, and then `∫_K J dE → 0` by dominated convergence
(`J ≤ 2` always, since `cayley` maps `ℍ` into the unit disc).
-/

open MeasureTheory Filter Topology Set
open Work.TMComp.Kotani

noncomputable section

namespace Work.TMComp.LocCantor

/-- The **(K2)-integrand**: the right-hand side of `K2_pointwise_eq`, the nonnegative quantity
whose `y`-integral is bounded by `4 (ℓ/ε - ∂_εℓ)` (`K2_integral_le`). -/
def K2 (α lam : ℝ) (E : ℂ) (y : ℝ) : ℝ :=
  (defect α lam E y).im
    * ‖(mfun α lam E y - E / 2) - (sigSec α lam E y - star E / 2)‖ ^ 2
    / (N1 α lam E y * N2 α lam E y * ‖defect α lam E y‖ ^ 2)

/-- `im(defect) = N₁ + N₂`. -/
theorem defect_im_eq (α lam : ℝ) {E : ℂ} (_hE : 0 < E.im) (y : ℝ) :
    (defect α lam E y).im = N1 α lam E y + N2 α lam E y := by
  have h1 : sSec α lam E y = star (sigSec α lam E y) := (conj_sigSec α lam E y).symm
  rw [defect, h1, N1, N2]
  simp only [Complex.sub_im, Complex.star_def, Complex.conj_im]
  ring

/-- `im(defect) > 0` for `Im E > 0`. -/
theorem defect_im_pos (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (y : ℝ) :
    0 < (defect α lam E y).im := by
  rw [defect_im_eq α lam hE y]
  linarith [N1_pos α lam E hE y, N2_pos α lam E hE y]

/-- The (K2)-integrand is nonnegative. -/
theorem K2_nonneg (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (y : ℝ) : 0 ≤ K2 α lam E y := by
  have h1 : 0 < (defect α lam E y).im := defect_im_pos α lam hE y
  have h2 : 0 < N1 α lam E y := N1_pos α lam E hE y
  have h3 : 0 < N2 α lam E y := N2_pos α lam E hE y
  have h4 : (0 : ℝ) < ‖defect α lam E y‖ ^ 2 := by
    have h5 : defect α lam E y ≠ 0 := defect_ne_zero α lam hE y
    have h6 : (0 : ℝ) < ‖defect α lam E y‖ := norm_pos_iff.mpr h5
    positivity
  rw [K2]
  exact div_nonneg (mul_nonneg (le_of_lt h1) (sq_nonneg _))
    (mul_pos (mul_pos h2 h3) h4).le

/-- `q = 1/N₁ + 1/N₂ = (N₁+N₂)/(N₁N₂)`. -/
theorem one_div_N1_add (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (y : ℝ) :
    1 / N1 α lam E y + 1 / N2 α lam E y
      = (N1 α lam E y + N2 α lam E y) / (N1 α lam E y * N2 α lam E y) := by
  have h2 : N1 α lam E y ≠ 0 := ne_of_gt (N1_pos α lam E hE y)
  have h3 : N2 α lam E y ≠ 0 := ne_of_gt (N2_pos α lam E hE y)
  field_simp
  ring

/-- **The key algebraic identity.**  With `a := m - E/2`, `c := σ - conj E/2` and
`B := a - conj c = defect`, the squared "defect ratio" is the (K2)-integrand divided by
`q = 1/N₁ + 1/N₂`. -/
theorem norm_sq_div_defect_sq_eq (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (y : ℝ) :
    ‖(mfun α lam E y - E / 2) - (sigSec α lam E y - star E / 2)‖ ^ 2
        / ‖defect α lam E y‖ ^ 2
      = K2 α lam E y / (1 / N1 α lam E y + 1 / N2 α lam E y) := by
  have h1 : 0 < (defect α lam E y).im := defect_im_pos α lam hE y
  have h2 : 0 < N1 α lam E y := N1_pos α lam E hE y
  have h3 : 0 < N2 α lam E y := N2_pos α lam E hE y
  have h4 : (0 : ℝ) < ‖defect α lam E y‖ ^ 2 := by
    have h5 : defect α lam E y ≠ 0 := defect_ne_zero α lam hE y
    have h6 : (0 : ℝ) < ‖defect α lam E y‖ := norm_pos_iff.mpr h5
    positivity
  rw [one_div_N1_add α lam hE y, K2, defect_im_eq α lam hE y]
  field_simp

/-- `r + i ≠ 0` for `r` in the upper half plane. -/
theorem add_I_ne_zero {r : ℂ} (hr : 0 < r.im) : r + Complex.I ≠ 0 := by
  intro h
  have h1 := congrArg Complex.im h
  simp at h1
  linarith

/-- For `u v` in the upper half plane, `‖cayley u - cayley v‖ ≤ 2(‖u‖ + ‖v‖)`. -/
theorem cayley_sub_le_two_mul (u v : ℂ) (hu : 0 < u.im) (hv : 0 < v.im) :
    ‖cayley u - cayley v‖ ≤ 2 * (‖u‖ + ‖v‖) := by
  have hu' : u + Complex.I ≠ 0 := add_I_ne_zero hu
  have hv' : v + Complex.I ≠ 0 := add_I_ne_zero hv
  have h1 : u.im + 1 ≤ ‖u + Complex.I‖ := by
    have h := Complex.im_le_norm (u + Complex.I)
    simpa using h
  have h2 : v.im + 1 ≤ ‖v + Complex.I‖ := by
    have h := Complex.im_le_norm (v + Complex.I)
    simpa using h
  have h3 : (1 : ℝ) ≤ (u.im + 1) * (v.im + 1) := by nlinarith [hu, hv]
  have h4 : (u.im + 1) * (v.im + 1) ≤ ‖u + Complex.I‖ * ‖v + Complex.I‖ :=
    mul_le_mul h1 h2 (by linarith) (by positivity)
  have hden : (1 : ℝ) ≤ ‖u + Complex.I‖ * ‖v + Complex.I‖ := le_trans h3 h4
  have hnum : ‖2 * Complex.I * (u - v)‖ = 2 * ‖u - v‖ := by
    rw [norm_mul, norm_mul]
    simp
  rw [cayley_sub_eq u v hu' hv', norm_div, hnum, norm_mul]
  have htri : ‖u - v‖ ≤ ‖u‖ + ‖v‖ := by
    calc ‖u - v‖ = ‖u + (-v)‖ := by ring_nf
      _ ≤ ‖u‖ + ‖-v‖ := norm_add_le _ _
      _ = ‖u‖ + ‖v‖ := by rw [norm_neg]
  have hpos : (0 : ℝ) < ‖u + Complex.I‖ * ‖v + Complex.I‖ := lt_of_lt_of_le one_pos hden
  rw [div_le_iff₀ hpos]
  nlinarith [htri, hden, norm_nonneg u, norm_nonneg v]

/-! ## The two sides -/

/-- On the upper side, `Ψ = -1/(m - E/2)`, written with the real parameter `E₀/2`. -/
theorem Psi_eq_inv_upper (α lam : ℝ) (E₀ ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    Psi α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
      = -1 / ((mfun α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
            - ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E₀ / 2 : ℝ) : ℂ)) := by
  have hEpos : 0 < ((E₀ : ℂ) + (ε : ℂ) * Complex.I).im := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, add_zero]
    linarith
  rw [Psi, glued_of_pos α lam hEpos y]
  congr 1
  push_cast
  ring

/-- On the lower side, `Ψ = -1/(σ - conj E/2)` (with `σ` at the conjugate energy). -/
theorem Psi_eq_inv_lower (α lam : ℝ) (E₀ ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    Psi α lam ((E₀ : ℂ) - (ε : ℂ) * Complex.I) y
      = -1 / ((sigSec α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
            + ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E₀ / 2 : ℝ) : ℂ)) := by
  have hstar : star ((E₀ : ℂ) - (ε : ℂ) * Complex.I) = (E₀ : ℂ) + (ε : ℂ) * Complex.I := by
    simp only [Complex.star_def, star_sub, star_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hneg : ((E₀ : ℂ) - (ε : ℂ) * Complex.I).im < 0 := by
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, sub_zero]
    linarith
  rw [Psi, glued_of_neg α lam hneg hstar y]
  congr 1
  push_cast
  ring

/-! ## The two bounds on the jump -/

/-- First bound: `J ≤ 2 (1/N₁ + 1/N₂)` (from the `Ψ`-bounds). -/
theorem Psi_jump_le_two_q (α lam : ℝ) (E₀ ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    ‖cayley (Psi α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y)
        - cayley (Psi α lam ((E₀ : ℂ) - (ε : ℂ) * Complex.I) y)‖
      ≤ 2 * (1 / N1 α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
          + 1 / N2 α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y) := by
  set E : ℂ := (E₀ : ℂ) + (ε : ℂ) * Complex.I with hEdef
  have hEim : E.im = ε := by
    rw [hEdef]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, add_zero]
    ring
  have hE : 0 < E.im := by rw [hEim]; exact hε
  have hXim : ((mfun α lam E y - ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E₀ / 2 : ℝ) : ℂ)).im
      = N1 α lam E y := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, sub_zero, N1]
    ring
    rw [hEim]
  have hYim : ((sigSec α lam E y + ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E₀ / 2 : ℝ) : ℂ)).im
      = N2 α lam E y := by
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, add_zero, N2]
    ring
    rw [hEim]
  have hXne : (mfun α lam E y - ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E₀ / 2 : ℝ) : ℂ) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.im h
    rw [hXim] at h1
    simp at h1
    linarith [N1_pos α lam E hE y]
  have hYne : (sigSec α lam E y + ((ε / 2 : ℝ) : ℂ) * Complex.I) - ((E₀ / 2 : ℝ) : ℂ) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.im h
    rw [hYim] at h1
    simp at h1
    linarith [N2_pos α lam E hE y]
  have h1 : ‖-1 / ((mfun α lam E y - ((ε / 2 : ℝ) : ℂ) * Complex.I)
      - ((E₀ / 2 : ℝ) : ℂ))‖ ≤ 1 / N1 α lam E y :=
    inv_norm_le _ hXim (N1_pos α lam E hE y)
  have h2 : ‖-1 / ((sigSec α lam E y + ((ε / 2 : ℝ) : ℂ) * Complex.I)
      - ((E₀ / 2 : ℝ) : ℂ))‖ ≤ 1 / N2 α lam E y :=
    inv_norm_le _ hYim (N2_pos α lam E hE y)
  have hXu : 0 < ((mfun α lam E y - ((ε / 2 : ℝ) : ℂ) * Complex.I)
      - ((E₀ / 2 : ℝ) : ℂ)).im := by rw [hXim]; exact N1_pos α lam E hE y
  have hYu : 0 < ((sigSec α lam E y + ((ε / 2 : ℝ) : ℂ) * Complex.I)
      - ((E₀ / 2 : ℝ) : ℂ)).im := by rw [hYim]; exact N2_pos α lam E hE y
  have hP : 0 < (-1 / ((mfun α lam E y - ((ε / 2 : ℝ) : ℂ) * Complex.I)
      - ((E₀ / 2 : ℝ) : ℂ))).im := by
    rw [neg_one_div_im hXne]
    exact div_pos hXu (by positivity)
  have hQ : 0 < (-1 / ((sigSec α lam E y + ((ε / 2 : ℝ) : ℂ) * Complex.I)
      - ((E₀ / 2 : ℝ) : ℂ))).im := by
    rw [neg_one_div_im hYne]
    exact div_pos hYu (by positivity)
  have hupper := Psi_eq_inv_upper α lam E₀ ε hε y
  have hlower := Psi_eq_inv_lower α lam E₀ ε hε y
  have hEeq : (E₀ : ℂ) + (ε : ℂ) * Complex.I = E := hEdef.symm
  rw [hEeq] at hupper hlower
  rw [hupper, hlower]
  calc ‖cayley (-1 / ((mfun α lam E y - ((ε / 2 : ℝ) : ℂ) * Complex.I)
        - ((E₀ / 2 : ℝ) : ℂ)))
      - cayley (-1 / ((sigSec α lam E y + ((ε / 2 : ℝ) : ℂ) * Complex.I)
        - ((E₀ / 2 : ℝ) : ℂ)))‖
      ≤ 2 * (‖-1 / ((mfun α lam E y - ((ε / 2 : ℝ) : ℂ) * Complex.I)
            - ((E₀ / 2 : ℝ) : ℂ))‖
          + ‖-1 / ((sigSec α lam E y + ((ε / 2 : ℝ) : ℂ) * Complex.I)
            - ((E₀ / 2 : ℝ) : ℂ))‖) := cayley_sub_le_two_mul _ _ hP hQ
    _ ≤ 2 * (1 / N1 α lam E y + 1 / N2 α lam E y) := by linarith

/-- Second bound (Schwarz–Pick): `J ≤ 2‖a-c‖/‖defect‖`. -/
theorem Psi_jump_le_two_defect_ratio (α lam : ℝ) (E₀ ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    ‖cayley (Psi α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y)
        - cayley (Psi α lam ((E₀ : ℂ) - (ε : ℂ) * Complex.I) y)‖
      ≤ 2 * ‖(mfun α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
              - ((E₀ : ℂ) + (ε : ℂ) * Complex.I) / 2)
            - (sigSec α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
              - star ((E₀ : ℂ) + (ε : ℂ) * Complex.I) / 2)‖
          / ‖defect α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y‖ := by
  have h := cayley_Psi_jump_le α lam E₀ ε hε y
  have hEE : ((E₀ : ℂ) + (ε : ℂ) * Complex.I) - star ((E₀ : ℂ) + (ε : ℂ) * Complex.I)
      = 2 * Complex.I * (ε : ℂ) := by
    rw [Complex.star_def, Complex.sub_conj]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, add_zero]
    push_cast
    ring
  have hstar : star ((E₀ : ℂ) + (ε : ℂ) * Complex.I)
      = ((E₀ : ℂ) + (ε : ℂ) * Complex.I) - 2 * Complex.I * (ε : ℂ) := by
    rw [← hEE]; ring
  have hkey : (mfun α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
          - ((ε / 2 : ℝ) : ℂ) * Complex.I)
        - (sigSec α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
          + ((ε / 2 : ℝ) : ℂ) * Complex.I)
      = (mfun α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
          - ((E₀ : ℂ) + (ε : ℂ) * Complex.I) / 2)
        - (sigSec α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y
          - star ((E₀ : ℂ) + (ε : ℂ) * Complex.I) / 2) := by
    rw [hstar]
    push_cast
    ring
  rw [hkey] at h
  exact h

/-! ## The cube bound -/

/-- **Main pointwise bound.**  The cube of the jump of `cayley ∘ Ψ` is bounded by eight times
the (K2)-integrand, with no boundedness hypothesis on the imaginary parts. -/
theorem Psi_jump_cube_le_eight_K2 (α lam : ℝ) (E₀ ε : ℝ) (hε : 0 < ε) (y : ℝ) :
    ‖cayley (Psi α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y)
        - cayley (Psi α lam ((E₀ : ℂ) - (ε : ℂ) * Complex.I) y)‖ ^ 3
      ≤ 8 * K2 α lam ((E₀ : ℂ) + (ε : ℂ) * Complex.I) y := by
  set E : ℂ := (E₀ : ℂ) + (ε : ℂ) * Complex.I with hEdef
  have hEim : E.im = ε := by
    rw [hEdef]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, add_zero]
    ring
  have hE : 0 < E.im := by rw [hEim]; exact hε
  set J : ℝ := ‖cayley (Psi α lam E y)
    - cayley (Psi α lam ((E₀ : ℂ) - (ε : ℂ) * Complex.I) y)‖ with hJdef
  have hJ0 : 0 ≤ J := by rw [hJdef]; positivity
  set Nr : ℝ := ‖(mfun α lam E y - E / 2) - (sigSec α lam E y - star E / 2)‖ with hNrdef
  set Dr : ℝ := ‖defect α lam E y‖ with hDrdef
  set Q : ℝ := 1 / N1 α lam E y + 1 / N2 α lam E y with hQdef
  have hQpos : 0 < Q := by
    rw [hQdef]
    have h1 := N1_pos α lam E hE y
    have h2 := N2_pos α lam E hE y
    positivity
  have hQne : Q ≠ 0 := ne_of_gt hQpos
  have hJq : J ≤ 2 * Q := by
    rw [hJdef, hQdef, hEdef]
    exact Psi_jump_le_two_q α lam E₀ ε hε y
  have hJd : J ≤ 2 * Nr / Dr := by
    rw [hJdef, hNrdef, hDrdef, hEdef]
    exact Psi_jump_le_two_defect_ratio α lam E₀ ε hε y
  have hident : Nr ^ 2 / Dr ^ 2 = K2 α lam E y / Q := by
    rw [hNrdef, hDrdef, hQdef]
    exact norm_sq_div_defect_sq_eq α lam hE y
  have hJsq : J ^ 2 ≤ 4 * K2 α lam E y / Q := by
    have hBnn : (0 : ℝ) ≤ 2 * Nr / Dr := div_nonneg (by positivity) (norm_nonneg _)
    have h1 : J ^ 2 ≤ (2 * Nr / Dr) ^ 2 := by nlinarith [hJd, hJ0, hBnn]
    have h2 : (2 * Nr / Dr) ^ 2 = 4 * (Nr ^ 2 / Dr ^ 2) := by ring
    rw [h2, hident] at h1
    have h3 : 4 * (K2 α lam E y / Q) = 4 * K2 α lam E y / Q := by ring
    linarith [h1, h3]
  have hcube : J ^ 3 = J * J ^ 2 := by ring
  rw [hcube]
  have hfin : J * J ^ 2 ≤ (2 * Q) * (4 * K2 α lam E y / Q) :=
    mul_le_mul hJq hJsq (sq_nonneg J) (by linarith)
  have heq : (2 * Q) * (4 * K2 α lam E y / Q) = 8 * K2 α lam E y := by
    field_simp
    ring
  linarith [hfin, heq]

end Work.TMComp.LocCantor
