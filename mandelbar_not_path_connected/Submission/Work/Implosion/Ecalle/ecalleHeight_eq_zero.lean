/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The equator of the Écalle coordinate in the purely imaginary parameter case

Hubbard–Schleicher, *Multicorns are not path connected*, consider the normal form
`f(ζ) = ζ + (ζ² − a²)h(ζ)` with `a = iλ` purely imaginary, `λ > 0`
(`Submission/Work/Implosion/Basic.lean`).  The two fixed points are then `±iλ`,
and the cut `ℓ = [−a,a]` is a *vertical* segment: its Écalle coordinate is the
vertical line `Re u = π/(2λ)` (`ecalCoord_cutPt_re` in
`Submission/Work/Implosion/Ecalle.lean`).

The present lemma is the complementary statement for the *real axis*: every real
point `x` has **Écalle height zero**, i.e. lies on the equator `Im u = 0` of the
Écalle cylinder.  It is the elementary observation behind the fact that the
incoming and outgoing petals of the normal form meet the real axis along the
equator.

The reason is that `m_a(x) = (x + iλ)/(x − iλ)` is a quotient of conjugate
numbers, hence has modulus `1`; writing `w = m_a(x)` we have `‖w‖ = 1`, so
`Re (log w) = log ‖w‖ = 0`, and
`u = log w / (2a) = log w / (2λ i)` is therefore purely *real*.  Hence
`Im u = 0`.

Note on notation: `I` below denotes `Complex.I`; `open Complex` is required for
that identifier to resolve (this workspace sets `autoImplicit = false`).  The
theorem statement itself is unchanged.
-/
import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Complex

namespace Work.Implosion.Ecalle

/-- Complex numbers with the same `normSq` have the same norm. -/
theorem norm_eq_of_normSq_eq {z w : ℂ} (h : Complex.normSq z = Complex.normSq w) :
    ‖z‖ = ‖w‖ := by
  have hsq : ‖z‖ ^ 2 = ‖w‖ ^ 2 := by rw [Complex.sq_norm, Complex.sq_norm, h]
  have := congrArg Real.sqrt hsq
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using this

/-- `x + iλ` and `x − iλ` (real `x`, `λ`) are complex conjugates, hence have the
same modulus. -/
theorem norm_add_mul_I_sub_mul_I (lam x : ℝ) :
    ‖(x : ℂ) + (lam : ℂ) * I‖ = ‖(x : ℂ) - (lam : ℂ) * I‖ :=
  norm_eq_of_normSq_eq (by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im]
    ring)

/-- **The equator of the Écalle coordinate for `a = iλ`** (`λ > 0`): every real
point `x` has Écalle height `0`, i.e. `Im u(x) = 0` where
`u(ζ) = log((ζ+a)/(ζ−a))/(2a)`. -/
theorem ecalleHeight_eq_zero (lam : ℝ) (hlam : 0 < lam) (x : ℝ) :
    ecalleHeight ((lam : ℂ) * I) ((x : ℂ)) = 0 := by
  -- `x − iλ ≠ 0`, since `normSq (x − iλ) = x² + λ² > 0`.
  have hden : (x : ℂ) - (lam : ℂ) * I ≠ 0 := by
    rw [← Complex.normSq_pos, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    nlinarith [sq_nonneg x, sq_pos_of_pos hlam]
  -- `m_a(x) = (x + iλ)/(x − iλ)` is a quotient of conjugate numbers: modulus `1`.
  have hnorm1 : ‖mobius ((lam : ℂ) * I) ((x : ℂ))‖ = 1 := by
    rw [mobius, norm_div, norm_add_mul_I_sub_mul_I lam x,
      div_self (norm_ne_zero_iff.mpr hden)]
  -- hence `Re log (m_a x) = log 1 = 0`.
  have hlogre : (Complex.log (mobius ((lam : ℂ) * I) ((x : ℂ)))).re = 0 := by
    rw [Complex.log_re, hnorm1, Real.log_one]
  -- and `2a = 2λ·i` is purely imaginary, so `log (m_a x)/(2a)` is real.
  have hwre : (2 * ((lam : ℂ) * I)).re = 0 := by simp [Complex.mul_re]
  rw [ecalleHeight, ecalCoord, Complex.div_im, hlogre, hwre]
  simp

end Work.Implosion.Ecalle
