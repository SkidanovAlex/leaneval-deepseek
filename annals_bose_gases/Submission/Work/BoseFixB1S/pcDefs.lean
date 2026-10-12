import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseFixB1S.CubeWindowSymbol
import Submission.Work.BoseKinLoc.Kinetic.kinFT_sq_of_memLp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.pcDefs` — the vocabulary of `profHatCube_moments`

Definitions and elementary bookkeeping for the proof that the cube bump
`chiSmall M` has `profHatCube`-moments

    `(2π)⁻³ ∫_p (profHatCube M p)² = 1`,
    `(2π)⁻³ ∫_p ‖p‖² (profHatCube M p)² = ∫_z ‖gradient (chiSmall M) z‖²`.

The bump `chiSmall M` is the pure tensor product `z ↦ ∏_j φ_M(z_j)` (up to the normalisation
constant `cSmall M`), where `φ_M = ζ^M`, and `φ_M` is `C^{M-1}` with a corner at `±1/2`
(so for `M = 1` it is only Lipschitz).  The whole proof therefore runs through the *1D* factor
`φ_M`, its a.e. derivative `phiC_deriv M`, the 1D transform `ft1` and the product structure.

Contents:
* `phiC M`, `phiCDeriv M`, `cSmall M`, `ft1`;
* `chiSmallBase_eq_prod`, `chiSmall_eq`, `chiSmallNormSq_eq` (the product structure and the
  normalisation);
* elementary bounds on `phiC` and `phiCDeriv`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The 1D factor `φ_M = ζ^M` and its a.e. derivative -/

/-- The 1D factor of the cube bump: `phiC M x = ζ(x)^M`. -/
noncomputable def phiC (M : ℕ) (x : ℝ) : ℝ := zeta1d x ^ M

/-- The a.e. derivative of `phiC M`: on `|x| < 1/2` it is the derivative of `cos(π·)^M`
(namely `M·cos(πx)^{M-1}·(−π sin(πx))`), and it vanishes for `|x| ≥ 1/2`. -/
noncomputable def phiCDeriv (M : ℕ) (x : ℝ) : ℝ :=
  if |x| < 1 / 2 then
    (M : ℝ) * (Real.cos (Real.pi * x)) ^ (M - 1) * (-(Real.pi * Real.sin (Real.pi * x)))
  else 0

/-- The normalisation constant of the cube bump: `cSmall M = (√chiSmallNormSq M)⁻¹`. -/
noncomputable def cSmall (M : ℕ) : ℝ := (Real.sqrt (chiSmallNormSq M))⁻¹

/-- The 1D Fourier transform in the corpus's `p`-convention:
`ft1 g y = ∫_x e^{−i y x} g x dx`.  (This is `Submission.BoseGases.kinFT` on `ℝ`.) -/
noncomputable def ft1 (g : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-(Complex.I * (y * x : ℂ))) * g x

/-! ## 2. Elementary bounds -/

lemma phiC_nonneg (M : ℕ) (x : ℝ) : 0 ≤ phiC M x := pow_nonneg (zeta1d_nonneg x) M

lemma phiC_le_one (M : ℕ) (x : ℝ) : phiC M x ≤ 1 :=
  pow_le_one₀ (zeta1d_nonneg x) (zeta1d_le_one x)

lemma abs_phiC_le_one (M : ℕ) (x : ℝ) : |phiC M x| ≤ 1 := by
  calc |phiC M x| = phiC M x := abs_of_nonneg (phiC_nonneg M x)
    _ ≤ 1 := phiC_le_one M x

lemma abs_phiCDeriv_le (M : ℕ) (x : ℝ) : |phiCDeriv M x| ≤ (M : ℝ) * Real.pi := by
  rw [phiCDeriv]
  split_ifs with hx
  · rw [abs_mul, abs_mul, abs_neg]
    have h1 : |(Real.cos (Real.pi * x)) ^ (M - 1)| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_cos_le_one _)
    have h2 : |(M : ℝ)| = (M : ℝ) := abs_of_nonneg (Nat.cast_nonneg M)
    have h3 : |Real.pi * Real.sin (Real.pi * x)| ≤ Real.pi := by
      rw [abs_mul, abs_of_nonneg (le_of_lt Real.pi_pos)]
      calc Real.pi * |Real.sin (Real.pi * x)| ≤ Real.pi * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (le_of_lt Real.pi_pos)
        _ = Real.pi := mul_one _
    calc |(M : ℝ)| * |(Real.cos (Real.pi * x)) ^ (M - 1)| * |Real.pi * Real.sin (Real.pi * x)|
        ≤ (M : ℝ) * 1 * Real.pi := by
          refine mul_le_mul ?_ h3 (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg M) zero_le_one)
          exact mul_le_mul (le_of_eq h2) h1 (abs_nonneg _) (Nat.cast_nonneg M)
      _ = (M : ℝ) * Real.pi := by ring
  · simp only [abs_zero]
    positivity

/-! ## 3. The product structure of the cube bump -/

lemma chiSmallBase_eq_prod (M : ℕ) (z : E3) :
    chiSmallBase M z = ∏ j : Fin 3, phiC M (z.ofLp j) := by
  rw [Fin.prod_univ_three]
  rw [chiSmallBase, phiC, phiC, phiC, mul_pow, mul_pow]

lemma chiSmallBase_apply (M : ℕ) (z : E3) : chiSmallBase M z = ∏ j : Fin 3, phiC M (z.ofLp j) :=
  chiSmallBase_eq_prod M z

/-- `chiSmall M = cSmall M * chiSmallBase M` (pointwise). -/
lemma chiSmall_eq_cSmall_mul (M : ℕ) (z : E3) :
    chiSmall M z = cSmall M * chiSmallBase M z := by
  rw [chiSmall, cSmall, div_eq_mul_inv, mul_comm]

/-- The normalisation integral as a cube of the 1D integral. -/
lemma chiSmallNormSq_eq (M : ℕ) :
    chiSmallNormSq M = (∫ x : ℝ, (phiC M x) ^ 2) ^ 3 := by
  rw [chiSmallNormSq]
  have hfun : (fun z : E3 => (chiSmallBase M z) ^ 2)
      = fun z : E3 => ∏ j : Fin 3, (phiC M (z.ofLp j)) ^ 2 := by
    funext z
    rw [chiSmallBase_eq_prod, Finset.prod_pow]
  rw [hfun]
  -- transfer the integral from `EuclideanSpace` to `Fin 3 → ℝ` (volume preserving)
  have h2 : (∫ z : E3, ∏ j : Fin 3, (phiC M (z.ofLp j)) ^ 2)
      = ∫ x : Fin 3 → ℝ, ∏ j : Fin 3, (phiC M (x j)) ^ 2 := by
    rw [← MeasureTheory.MeasurePreserving.integral_comp'
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))
      (g := fun x : Fin 3 → ℝ => ∏ j : Fin 3, (phiC M (x j)) ^ 2)]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => by rfl)
  rw [h2, integral_fintype_prod_volume_eq_prod (fun _ : Fin 3 => fun x : ℝ => (phiC M x) ^ 2)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Work.BoseFixB1S
