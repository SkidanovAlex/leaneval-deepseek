import Mathlib
import Submission.Work.EQ.Defs

set_option linter.unusedSimpArgs false

/-! Local dynamics of the equichordal half-map `eqU` near its fixed point `A₁ = -1/2`.

This file fixes the coordinates in which the local theory is done: `ζ = P - A₁`, and, for
`ζ = x + i y`, the real functions `locX`, `locY` with `locU a ζ = locX a x y + i·locY a x y`.
Everything else (one-step and two-step estimates, the invariant `χ`, the leaf argument) is built
on these in `Submission/Work/EQ/hetero_leaf.lean`. -/

namespace Work.EQ

open Complex

/-- `w = (1+a)/2 = |A₁ - O₂|`, the distance from the left fixed point `A₁ = -1/2` to `O₂ = a/2`. -/
noncomputable def locW (a : ℝ) : ℝ := (1 + a) / 2

/-- The half-map `eqU` transported to the coordinate `ζ = P - A₁`.

It is the exact identity `eqU a (A₁ + ζ) = A₁ + locU a ζ` (Lemma `eqU_add` below). -/
noncomputable def locU (a : ℝ) (ζ : ℂ) : ℂ :=
  1 - ζ + (ζ - ((locW a : ℝ) : ℂ)) / ((‖ζ - ((locW a : ℝ) : ℂ)‖ : ℝ) : ℂ)

/-- `locR a x y = ‖(x + i y) - w‖`. -/
noncomputable def locR (a x y : ℝ) : ℝ := Real.sqrt ((x - locW a) ^ 2 + y ^ 2)

/-- Real part of `locU a (x + i y)`. -/
noncomputable def locX (a x y : ℝ) : ℝ := 1 - x + (x - locW a) / locR a x y

/-- Imaginary part of `locU a (x + i y)`. -/
noncomputable def locY (a x y : ℝ) : ℝ := -y + y / locR a x y

/-- The `y`-multiplier of one application of `locU`: `locY a x y = y * locLy a x y`. -/
noncomputable def locLy (a x y : ℝ) : ℝ := (1 - locR a x y) / locR a x y

/-- The half-map on real coordinate pairs. -/
noncomputable def locFn (a : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (locX a p.1 p.2, locY a p.1 p.2)

/-- The two-step map `T = eqU ∘ eqU` in coordinates. -/
noncomputable def locT (a : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := locFn a (locFn a p)

/-- The `x`-displacement of the two-step map: `(locT a p).1 = p.1 + locA a p`. -/
noncomputable def locA (a : ℝ) (p : ℝ × ℝ) : ℝ := (locT a p).1 - p.1

/-- The `y`-multiplier of the two-step map: `(locT a p).2 = p.2 * locM a p`. -/
noncomputable def locM (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  locLy a p.1 p.2 * locLy a (locFn a p).1 (locFn a p).2

theorem eqU_add (a : ℝ) (ζ : ℂ) :
    eqU a ((-(1/2) : ℂ) + ζ) = (-(1/2) : ℂ) + locU a ζ := by
  rw [eqU, locU, locW]
  have h1 : ((-(1/2) : ℂ) + ζ - (((a : ℝ) / 2 : ℝ) : ℂ)) = (ζ - (((1 + a) / 2 : ℝ) : ℂ)) := by
    push_cast; ring
  rw [h1]; ring

theorem locR_nonneg (a x y : ℝ) : 0 ≤ locR a x y := Real.sqrt_nonneg _

theorem norm_sub_w (a x y : ℝ) :
    ‖((x : ℂ) + (y : ℂ) * I) - ((locW a : ℝ) : ℂ)‖ = locR a x y := by
  rw [locR, locW, Complex.norm_def, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_ofNat, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_im, add_im, add_re, sub_re]
  congr 1
  ring

theorem locU_re (a x y : ℝ) : (locU a ((x : ℂ) + (y : ℂ) * I)).re = locX a x y := by
  simp only [locU, locX, norm_sub_w, Complex.add_re, Complex.sub_re, Complex.one_re,
    Complex.div_ofReal_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  ring

theorem locU_im (a x y : ℝ) : (locU a ((x : ℂ) + (y : ℂ) * I)).im = locY a x y := by
  simp only [locU, locY, norm_sub_w, Complex.add_im, Complex.sub_im, Complex.one_im,
    Complex.div_ofReal_im, Complex.ofReal_im, Complex.ofReal_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  ring

theorem locU_eq (a x y : ℝ) :
    locU a ((x : ℂ) + (y : ℂ) * I) = ((locX a x y : ℝ) : ℂ) + ((locY a x y : ℝ) : ℂ) * I := by
  refine Complex.ext ?_ ?_
  · simpa using locU_re a x y
  · simpa using locU_im a x y

theorem locY_eq_mul (a x y : ℝ) (h : locR a x y ≠ 0) :
    locY a x y = y * locLy a x y := by
  have hr : locR a x y * (locR a x y)⁻¹ = 1 := mul_inv_cancel₀ h
  rw [locY, locLy, div_eq_mul_inv, div_eq_mul_inv, sub_mul, one_mul, hr]
  ring

theorem locT_fst (a : ℝ) (p : ℝ × ℝ) : (locT a p).1 = p.1 + locA a p := by
  rw [locA]; ring

theorem locT_snd (a : ℝ) (p : ℝ × ℝ) (h1 : locR a p.1 p.2 ≠ 0)
    (h2 : locR a (locFn a p).1 (locFn a p).2 ≠ 0) :
    (locT a p).2 = p.2 * locM a p := by
  set L := locLy a (locFn a p).1 (locFn a p).2 with hL
  have e1 : (locFn a p).2 = locY a p.1 p.2 := rfl
  have e2 : (locT a p).2 = locY a (locFn a p).1 (locFn a p).2 := rfl
  have e3 : locY a (locFn a p).1 (locFn a p).2 = (locFn a p).2 * L := by
    rw [hL]; exact locY_eq_mul a _ _ h2
  have e4 : (locFn a p).2 = p.2 * locLy a p.1 p.2 := by
    rw [e1]; exact locY_eq_mul a _ _ h1
  rw [e2, e3, e4, locM, ← hL]
  ring

theorem locT_eq (a : ℝ) (p : ℝ × ℝ) (h1 : locR a p.1 p.2 ≠ 0)
    (h2 : locR a (locFn a p).1 (locFn a p).2 ≠ 0) :
    locT a p = (p.1 + locA a p, p.2 * locM a p) :=
  Prod.ext (locT_fst a p) (locT_snd a p h1 h2)

end Work.EQ
