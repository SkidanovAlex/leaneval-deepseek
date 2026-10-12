import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseRowsFS.Theta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.ssb_summable_Kt_image`

The heat kernel `Kt s` (`Work.BoseRowsFS.Kt`) is a Gaussian of variance `s`, so its values on the
translated lattice `z + ℓ·ℤ³` decay like `e^{-c‖m‖²}` and the lattice sum converges for every
`ℓ, s > 0` and every `z : ℝ³`.

The proof factors the summand over the three coordinates.  By
`Work.BoseRowsFS.norm_sq_add_smul_vecZ`,

`‖z + ℓ·vecZ m‖² = Σ_i (z_i + ℓ·m_i)²`,

hence

`exp (-‖z + ℓ·vecZ m‖²/(4s)) = ∏_i exp (-((z_i + ℓ·m_i)²/(4s)))`

(`Real.exp_sum`), and each one-dimensional factor is summable over `ℤ`
(`summable_exp_shift_gauss_int`, a shift-and-rename of the classical Gaussian sum
`Commons.Analysis.Fourier.summable_exp_neg_mul_sq_int`).  Summability of the product over
`Fin 3 → ℤ` is `Work.BoseRowsFS.summable_pi3_prod_of_nonneg`, and the constant prefactor
`(4πs)^{-3/2}` of `Kt` is pulled out with `Summable.mul_left`.
-/

noncomputable section

namespace Work.BoseRowsFS

open MeasureTheory MeasureTheory.Measure

set_option autoImplicit false

/-! ## 1. The shifted one-dimensional Gaussian sum over `ℤ` -/

/-- **The shifted Gaussian over `ℤ` is summable**: for `ℓ, t > 0` and `z : ℝ`,
`Σ_{n∈ℤ} e^{-(z+ℓn)²/(4t)} < ∞`.  The shift costs only the factor `e^{z²/(2t)}`, because
`(z+ℓn)² ≥ ℓ²n²/2 - z²`; the remaining sum is the classical Gaussian
`Σ_{n∈ℤ} e^{-(ℓ²/8t)n²}`. -/
lemma summable_exp_shift_gauss_int {ℓ t z : ℝ} (hℓ : 0 < ℓ) (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-((z + ℓ * (n : ℝ)) ^ 2 / (4 * t)))) := by
  have hbase : Summable fun n : ℤ => Real.exp (-(ℓ ^ 2 / (8 * t) * (n : ℝ) ^ 2)) := by
    have h := Commons.Analysis.Fourier.summable_exp_neg_mul_sq_int (c := ℓ ^ 2 / (8 * t))
      (by positivity)
    refine h.congr (fun n => ?_)
    congr 1
    ring
  refine Summable.of_norm_bounded (g := fun n : ℤ =>
    Real.exp (z ^ 2 / (2 * t)) * Real.exp (-(ℓ ^ 2 / (8 * t) * (n : ℝ) ^ 2)))
    (hbase.mul_left _) fun n => ?_
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hkey : ℓ ^ 2 * (n : ℝ) ^ 2 / 2 - z ^ 2 ≤ (z + ℓ * (n : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (ℓ * (n : ℝ) + 2 * z)]
  have h4t : (0 : ℝ) < 4 * t := by positivity
  have hL : (4 * t) * -((z + ℓ * (n : ℝ)) ^ 2 / (4 * t)) = -((z + ℓ * (n : ℝ)) ^ 2) := by
    field_simp
  have hmul : (4 * t) * (z ^ 2 / (2 * t) + -(ℓ ^ 2 / (8 * t) * (n : ℝ) ^ 2))
      = 2 * z ^ 2 - ℓ ^ 2 * (n : ℝ) ^ 2 / 2 := by
    field_simp
    ring
  refine le_of_mul_le_mul_left ?_ h4t
  rw [hL, hmul]
  nlinarith [hkey]

/-! ## 2. The theorem -/

/-- **The heat kernel on a translated lattice is summable.**  For `ℓ, s > 0` and every
`z : ℝ³`, the family `m ↦ Kt s (z + ℓ·vecZ m)` over `m ∈ ℤ³` is summable. -/
theorem ssb_summable_Kt_image {ℓ s : ℝ} (hℓ : 0 < ℓ) (hs : 0 < s)
    (z : EuclideanSpace ℝ (Fin 3)) :
    Summable (fun m : Fin 3 → ℤ => Kt s (z + ℓ • vecZ m)) := by
  -- the Gaussian part, factored over the three coordinates
  have h1 : Summable (fun m : Fin 3 → ℤ =>
      Real.exp (-(‖z + ℓ • vecZ m‖ ^ 2 / (4 * s)))) := by
    have hprod : Summable (fun m : Fin 3 → ℤ =>
        ∏ i, Real.exp (-((z.ofLp i + ℓ * (m i : ℝ)) ^ 2 / (4 * s)))) :=
      summable_pi3_prod_of_nonneg
        (F := fun i (n : ℤ) => Real.exp (-((z.ofLp i + ℓ * (n : ℝ)) ^ 2 / (4 * s))))
        (fun _ _ => (Real.exp_pos _).le)
        (fun _ => summable_exp_shift_gauss_int hℓ hs)
    refine hprod.congr (fun m => ?_)
    rw [← Real.exp_sum, norm_sq_add_smul_vecZ]
    congr 1
    rw [Finset.sum_neg_distrib, ← Finset.sum_div]
  -- pull out the constant prefactor of `Kt`
  refine (h1.mul_left ((4 * Real.pi * s) ^ (-(3 / 2 : ℝ)))).congr (fun m => ?_)
  simp only [Kt, neg_div]

end Work.BoseRowsFS
