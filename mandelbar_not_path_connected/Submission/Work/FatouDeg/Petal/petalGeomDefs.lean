/-
Copyright: subproject `Submission/Work/FatouDeg/Petal/` of `mandelbar_not_path_connected`.

Ported verbatim from `Submission/Work/MultiPetal/` of the same project, with the exponent
hypothesis `4 ≤ m` weakened to `3 ≤ m` (see `Submission/Work/FatouDeg/NOTES.md`).

# Shared definitions for the one-step geometry of the multi-petal germ

This file collects the definitions and elementary (purely algebraic / trigonometric) lemmas used
by `Work.FatouDeg.Petal.petalGeomAux` and by the auxiliary lemmas delegated alongside it.

Writing `c > 0` for the slope of a sector `c |Im z| < Re z`:

* `pgTheta c = arctan (1 / c)` is the half-angle of that sector;
* `pgSfun c z = Re z - c * Im z` is the (signed) "distance to the boundary" of the sector;
* `pgx m G z = z ^ (m - 1) * (1 - z * G z)`, so that `Pfun m G z = z * (1 - pgx m G z)`.
-/
import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Topology
open Set Filter Metric

namespace Work.FatouDeg.Petal

/-! ## The half-angle `pgTheta` and its sine and cosine -/

/-- The half-angle of the sector `c |Im z| < Re z`: `arctan (1/c)`. -/
def pgTheta (c : ℝ) : ℝ := Real.arctan (1 / c)

theorem pgSqrt_one_add_inv_sq (c : ℝ) (hc : 0 < c) :
    Real.sqrt (1 + (1 / c) ^ 2) = Real.sqrt (1 + c ^ 2) / c := by
  have hsq : 1 + (1 / c) ^ 2 = (1 + c ^ 2) / c ^ 2 := by field_simp; ring
  rw [hsq, Real.sqrt_div' (1 + c ^ 2) (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hc]

theorem pgSinTheta (c : ℝ) (hc : 0 < c) :
    Real.sqrt (1 + c ^ 2) * Real.sin (pgTheta c) = 1 := by
  rw [pgTheta, Real.sin_arctan, pgSqrt_one_add_inv_sq c hc]
  have hc2 : (0 : ℝ) < 1 + c ^ 2 := by positivity
  field_simp

theorem pgCosTheta (c : ℝ) (hc : 0 < c) :
    Real.sqrt (1 + c ^ 2) * Real.cos (pgTheta c) = c := by
  rw [pgTheta, Real.cos_arctan, pgSqrt_one_add_inv_sq c hc]
  field_simp

/-- `cos α - c sin α = √(1+c²) sin (pgTheta c - α)`. -/
theorem pgCosSub (c α : ℝ) (hc : 0 < c) :
    Real.cos α - c * Real.sin α = Real.sqrt (1 + c ^ 2) * Real.sin (pgTheta c - α) := by
  rw [Real.sin_sub, mul_sub, ← mul_assoc, ← mul_assoc, pgSinTheta c hc, pgCosTheta c hc,
    one_mul]

/-- `cos α + c sin α = √(1+c²) sin (pgTheta c + α)`. -/
theorem pgCosAdd (c α : ℝ) (hc : 0 < c) :
    Real.cos α + c * Real.sin α = Real.sqrt (1 + c ^ 2) * Real.sin (pgTheta c + α) := by
  rw [Real.sin_add, mul_add, ← mul_assoc, ← mul_assoc, pgSinTheta c hc, pgCosTheta c hc,
    one_mul]

/-! ## The sector functional `pgSfun` -/

/-- `pgSfun c z = Re z - c * Im z`. -/
def pgSfun (c : ℝ) (z : ℂ) : ℝ := z.re - c * z.im

/-- `pgSfun (-c) z = Re z + c * Im z`. -/
theorem pgSfun_neg (c : ℝ) (z : ℂ) : pgSfun (-c) z = z.re + c * z.im := by
  rw [pgSfun]; ring

theorem pgSfun_add (c : ℝ) (z w : ℂ) :
    pgSfun c (z + w) = pgSfun c z + pgSfun c w := by
  rw [pgSfun, pgSfun, pgSfun, Complex.add_re, Complex.add_im]; ring

theorem pgSfun_sub (c : ℝ) (z w : ℂ) :
    pgSfun c (z - w) = pgSfun c z - pgSfun c w := by
  rw [pgSfun, pgSfun, pgSfun, Complex.sub_re, Complex.sub_im]; ring

theorem pgSfun_eq_re (c : ℝ) (z : ℂ) : pgSfun c z = ((1 + ↑c * Complex.I) * z).re := by
  rw [pgSfun, Complex.mul_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re,
    Complex.I_im]
  simp

theorem pgSfun_abs_le (c : ℝ) (z : ℂ) : |pgSfun c z| ≤ Real.sqrt (1 + c ^ 2) * ‖z‖ := by
  have h1 : ((1 + ↑c * Complex.I) : ℂ).re = 1 := by simp
  have h2 : ((1 + ↑c * Complex.I) : ℂ).im = c := by simp
  have hns : Complex.normSq (1 + ↑c * Complex.I) = 1 + c ^ 2 := by
    rw [Complex.normSq_apply, h1, h2]; ring
  rw [pgSfun_eq_re]
  calc |((1 + ↑c * Complex.I) * z).re| ≤ ‖(1 + ↑c * Complex.I) * z‖ := Complex.abs_re_le_norm _
    _ = ‖(1 + ↑c * Complex.I)‖ * ‖z‖ := norm_mul _ _
    _ = Real.sqrt (1 + c ^ 2) * ‖z‖ := by
        rw [Complex.norm_def, hns]

/-- The polar expression of `pgSfun` at `z ≠ 0`. -/
theorem pgSfun_arg (c : ℝ) {z : ℂ} (hz : z ≠ 0) :
    pgSfun c z = ‖z‖ * (Real.cos z.arg - c * Real.sin z.arg) := by
  have h1 : z.re = ‖z‖ * Real.cos z.arg := by rw [Complex.cos_arg hz]; field_simp
  have h2 : z.im = ‖z‖ * Real.sin z.arg := by rw [Complex.sin_arg]; field_simp
  rw [pgSfun, h1, h2]; ring

/-- The polar expression of `pgSfun` at a power. -/
theorem pgPow_eq (m : ℕ) {z : ℂ} (_hz : z ≠ 0) :
    z ^ m = ↑(‖z‖ ^ m) * (↑(Real.cos (m * z.arg)) + ↑(Real.sin (m * z.arg)) * Complex.I) := by
  conv_lhs => rw [← Complex.norm_mul_cos_add_sin_mul_I z]
  rw [mul_pow, Complex.ofReal_pow]
  rw [Complex.cos_add_sin_mul_I_pow m ↑z.arg]
  have hm1 : (↑m : ℂ) * ↑z.arg = ↑(m * z.arg) := by push_cast; ring
  rw [hm1, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem pgSfun_pow (c : ℝ) (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    pgSfun c (z ^ m) = ‖z‖ ^ m * (Real.cos (m * z.arg) - c * Real.sin (m * z.arg)) := by
  have h1 : (z ^ m).re = ‖z‖ ^ m * Real.cos (m * z.arg) := by
    rw [pgPow_eq m hz, Complex.re_ofReal_mul]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
  have h2 : (z ^ m).im = ‖z‖ ^ m * Real.sin (m * z.arg) := by
    rw [pgPow_eq m hz, Complex.im_ofReal_mul]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  rw [pgSfun, h1, h2]; ring

/-! ## The correction term `pgx` -/

/-- `pgx m G z = z ^ (m - 1) * (1 - z * G z)`, so that `Pfun m G z = z * (1 - pgx m G z)`. -/
def pgx (m : ℕ) (G : Polynomial ℂ) (z : ℂ) : ℂ := z ^ (m - 1) * (1 - z * G.eval z)

theorem Pfun_eq_mul_one_sub_pgx (m : ℕ) (hm : 1 ≤ m) (G : Polynomial ℂ) (z : ℂ) :
    Pfun m G z = z * (1 - pgx m G z) := by
  have h2 : z ^ (m + 1) = z ^ m * z := by rw [pow_succ]
  have h1 : z ^ m = z * z ^ (m - 1) := by rw [← pow_succ', Nat.sub_add_cancel hm]
  rw [Pfun, pgx, h2, h1]
  ring

end Work.FatouDeg.Petal
