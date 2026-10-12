import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.CorrAux.crossTermBound`

The cross term of the second-order correction to the Bogolubov energy.  With
`ℓ = A (μa³)^{-163/323}` (the box side up to constants), `d = (μa³)^{6/323}` and
`L = 1 + (ℓd)⁻¹ + |log d|` the localisation quantity, under the diluteness
hypothesis `A⁻¹ (μa³)^{157/323} ≤ 1` (which says exactly `(ℓd)⁻¹ ≤ 1`), the two
square roots carrying the `C₀`/`C₁`/`Cχ` constants are dominated by
`2 √(8 C₀C₁Cχ(2π)³) A^{-5/2} (μa³)^{797/646} (1 + |log t|)^{3/2}`.

The mathematics is an exact cancellation of powers together with one crude
bound on `L`:

* `ℓ⁻¹ ((ℓd)⁻¹)^{3/2} = A^{-5/2} (μa³)^{797/646}` exactly
  (`ctb_kernel_eq`), and
* `L ≤ 2 (1 + |log t|)` (`ctb_L_le_two`: `(ℓd)⁻¹ ≤ 1` by the hypothesis and
  `|log d| = (6/323)|log t| ≤ |log t|`), hence `√(L³) ≤ √8 (1+|log t|)^{3/2}`
  (`ctb_sqrt_cube_le`).

The remaining work is bookkeeping: factorise the square roots of the two
products (`cross_sqrt_split1/2/3`) and multiply the resulting inequalities by
the nonnegative factor `2 √C₀ √C₁ √Cχ √((2π)³) A^{-5/2} (μa³)^{797/646}`.
-/

namespace Work.BoseFixB1S.CorrAux

open Work.BoseBox

/-! ## The three analytic inputs -/

/-- **Power cancellation.**  With `ℓ = A(μa³)^{-163/323}` and `d = (μa³)^{6/323}`
the product `ℓ⁻¹ ((ℓd)⁻¹)^{3/2}` equals `A^{-5/2} (μa³)^{797/646}` exactly. -/
theorem ctb_kernel_eq {A t : ℝ} (hA : 0 < A) (ht : 0 < t) :
    (A * fsXp t (-163))⁻¹ * ((A * fsXp t (-163) * fsXp t 6)⁻¹) ^ (3 / 2 : ℝ)
      = A ^ (-(5 / 2 : ℝ)) * fsXp t (797 / 2) := by
  set u : ℝ := fsXp t (-163) with hu
  set w : ℝ := fsXp t 6 with hw
  have h1 : (A * u)⁻¹ = A⁻¹ * fsXp t 163 := by
    rw [mul_inv, hu, fsXp_inv ht, neg_neg]
  have h2 : ((A * u * w)⁻¹) ^ (3 / 2 : ℝ) = A ^ (-(3 / 2 : ℝ)) * fsXp t (471 / 2) := by
    have hmul : A * u * w = A * fsXp t (-157) := by
      rw [hu, hw, mul_assoc, fsXp_mul ht, show (-163:ℝ) + 6 = -157 by norm_num]
    rw [hmul, mul_inv, fsXp_inv ht, neg_neg,
      Real.mul_rpow (le_of_lt (inv_pos.mpr hA)) (fsXp_nonneg (t := t) (c := 157) ht.le),
      fsXp_rpow ht.le 157 (3/2),
      show (157:ℝ) * (3/2) = 471/2 by norm_num,
      Real.inv_rpow hA.le (3/2), ← Real.rpow_neg hA.le (3/2)]
  have hAs : A⁻¹ * A ^ (-(3 / 2 : ℝ)) = A ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one A, ← Real.rpow_add hA,
      show (-(1:ℝ)) + (-(3/2)) = -(5/2) by norm_num]
  have hts : fsXp t 163 * fsXp t (471 / 2) = fsXp t (797 / 2) := by
    rw [fsXp_mul ht, show (163:ℝ) + 471/2 = 797/2 by norm_num]
  calc (A * u)⁻¹ * ((A * u * w)⁻¹) ^ (3 / 2 : ℝ)
      = (A⁻¹ * fsXp t 163) * (A ^ (-(3 / 2 : ℝ)) * fsXp t (471 / 2)) := by rw [h1, h2]
    _ = (A⁻¹ * A ^ (-(3 / 2 : ℝ))) * (fsXp t 163 * fsXp t (471 / 2)) := by ring
    _ = A ^ (-(5 / 2 : ℝ)) * fsXp t (797 / 2) := by rw [hAs, hts]

/-- **The `L`-bound.**  Since `(ℓd)⁻¹ = A⁻¹ (μa³)^{157/323} ≤ 1` and
`|log d| = (6/323)|log t| ≤ |log t|`, the localisation quantity satisfies
`L ≤ 2 (1 + |log t|)`. -/
theorem ctb_L_le_two {A t : ℝ} (_hA : 0 < A) (ht : 0 < t)
    (hu : A⁻¹ * fsXp t 157 ≤ 1) :
    1 + ((A * fsXp t (-163)) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|
      ≤ 2 * (1 + |Real.log t|) := by
  have hd : ((A * fsXp t (-163)) * fsXp t 6)⁻¹ = A⁻¹ * fsXp t 157 := by
    have hmul : (A * fsXp t (-163)) * fsXp t 6 = A * fsXp t (-157) := by
      rw [mul_assoc, fsXp_mul ht, show (-163:ℝ) + 6 = -157 by norm_num]
    rw [hmul, mul_inv, fsXp_inv ht, neg_neg]
  have hlog : |Real.log (fsXp t 6)| ≤ |Real.log t| := by
    rw [fsXp, Real.log_rpow ht, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6/323)]
    nlinarith [abs_nonneg (Real.log t)]
  rw [hd]
  have := abs_nonneg (Real.log t)
  linarith

/-- **The cube-root bound.**  `L ≤ 2x` with `L ≥ 0` gives
`√(L³) ≤ √8 x^{3/2}`. -/
theorem ctb_sqrt_cube_le {L x : ℝ} (hL : 0 ≤ L) (h : L ≤ 2 * x) :
    Real.sqrt (L ^ 3) ≤ Real.sqrt 8 * x ^ (3 / 2 : ℝ) := by
  have hx : 0 ≤ x := by linarith
  have h3 : L ^ 3 ≤ 8 * x ^ 3 := by
    calc L ^ 3 ≤ (2 * x) ^ 3 := pow_le_pow_left₀ hL h 3
      _ = 8 * x ^ 3 := by ring
  calc Real.sqrt (L ^ 3) ≤ Real.sqrt (8 * x ^ 3) := Real.sqrt_le_sqrt h3
    _ = Real.sqrt 8 * Real.sqrt (x ^ 3) := by rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8)]
    _ = Real.sqrt 8 * x ^ (3 / 2 : ℝ) := by
        congr 1
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 3, ← Real.rpow_mul hx]
        congr 1
        norm_num

/-! ## Square-root factorisation helpers -/

/-- `√(c x⁻²) = √c · x⁻¹` for `x > 0` (used for the `C₀ (ℓ⁻¹)²` factor). -/
theorem cross_sqrt_split1 {C₀ ℓ : ℝ} (hC : 0 ≤ C₀) (hℓ : 0 < ℓ) :
    Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) = Real.sqrt C₀ * ℓ⁻¹ := by
  rw [Real.sqrt_mul hC, Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]

/-- `√((x³)⁻¹) = (x⁻¹)^{3/2}` for `x > 0`. -/
theorem cross_sqrt_inv_pow {x : ℝ} (hx : 0 < x) :
    Real.sqrt ((x ^ 3)⁻¹) = (x⁻¹) ^ (3 / 2 : ℝ) := by
  rw [← inv_pow, ← Real.rpow_natCast (x⁻¹) 3, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (inv_nonneg.mpr hx.le)]
  congr 1
  norm_num

/-- The full factorisation of the second square root: with all entries
nonnegative (and `ℓd > 0`),
`√(C₁ L³ ((ℓd)³)⁻¹ (2π)³ Cχ) = √C₁ √(L³) (ℓd)^{-3/2} √((2π)³) √Cχ`. -/
theorem cross_sqrt_split2 {C₁ Cχ L ℓ d : ℝ} (h₁ : 0 ≤ C₁) (hL : 0 ≤ L) (hd : 0 < ℓ * d) :
    Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)
      = Real.sqrt C₁ * Real.sqrt (L ^ 3) * ((ℓ * d)⁻¹) ^ (3 / 2 : ℝ)
          * Real.sqrt ((2 * Real.pi) ^ 3) * Real.sqrt Cχ := by
  have hinv : (0:ℝ) ≤ ((ℓ * d) ^ 3)⁻¹ := inv_nonneg.mpr (pow_nonneg hd.le 3)
  have hpi : (0:ℝ) ≤ (2 * Real.pi) ^ 3 := by positivity
  have hA : (0:ℝ) ≤ C₁ * L ^ 3 := mul_nonneg h₁ (pow_nonneg hL 3)
  have hB : (0:ℝ) ≤ C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ := mul_nonneg hA hinv
  have hC : (0:ℝ) ≤ C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 := mul_nonneg hB hpi
  rw [Real.sqrt_mul hC, Real.sqrt_mul hB, Real.sqrt_mul hA, Real.sqrt_mul h₁,
    cross_sqrt_inv_pow hd]

/-- The factorisation of the right-hand square root. -/
theorem cross_sqrt_split3 {C₀ C₁ Cχ : ℝ} (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (hχ : 0 ≤ Cχ) :
    Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3)
      = Real.sqrt 8 * Real.sqrt C₀ * Real.sqrt C₁ * Real.sqrt Cχ
          * Real.sqrt ((2 * Real.pi) ^ 3) := by
  have h8 : (0:ℝ) ≤ 8 * C₀ := mul_nonneg (by norm_num) h₀
  have h8C₁ : (0:ℝ) ≤ 8 * C₀ * C₁ := mul_nonneg h8 h₁
  have h8C₁Cχ : (0:ℝ) ≤ 8 * C₀ * C₁ * Cχ := mul_nonneg h8C₁ hχ
  rw [Real.sqrt_mul h8C₁Cχ, Real.sqrt_mul h8C₁, Real.sqrt_mul h8,
    Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8)]

/-! ## The cross term bound -/

theorem crossTermBound {C₀ C₁ Cχ A t : ℝ} (h₀ : 0 ≤ C₀) (h₁ : 0 ≤ C₁) (hχ : 0 ≤ Cχ) (hA : 0 < A) (ht : 0 < t)
    (hu : A⁻¹ * Work.BoseBox.fsXp t 157 ≤ 1) :
    (let ℓ : ℝ := A * Work.BoseBox.fsXp t (-163)
     let d : ℝ := Work.BoseBox.fsXp t 6
     let L : ℝ := 1 + (ℓ * d)⁻¹ + |Real.log d|
     2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
       Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)
       ≤ 2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) * A ^ (-(5 / 2 : ℝ)) *
           Work.BoseBox.fsXp t (797 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) := by
  dsimp only
  have hℓ : 0 < A * fsXp t (-163) := mul_pos hA (fsXp_pos ht)
  have hd : 0 < fsXp t 6 := fsXp_pos ht
  have hprod : 0 < (A * fsXp t (-163)) * fsXp t 6 := mul_pos hℓ hd
  have hinv : (0:ℝ) ≤ ((A * fsXp t (-163)) * fsXp t 6)⁻¹ := inv_nonneg.mpr hprod.le
  have hLnn : (0:ℝ) ≤ 1 + ((A * fsXp t (-163)) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)| := by
    have := abs_nonneg (Real.log (fsXp t 6)); linarith
  have hkey := ctb_kernel_eq hA ht
  have hLb := ctb_L_le_two hA ht hu
  have hcube : Real.sqrt ((1 + ((A * fsXp t (-163)) * fsXp t 6)⁻¹
        + |Real.log (fsXp t 6)|) ^ 3) ≤ Real.sqrt 8 * (1 + |Real.log t|) ^ (3 / 2 : ℝ) :=
    ctb_sqrt_cube_le hLnn hLb
  have hQ : (0:ℝ) ≤ Real.sqrt C₀ * Real.sqrt C₁ * Real.sqrt Cχ * Real.sqrt ((2 * Real.pi) ^ 3) := by
    positivity
  have hK : (0:ℝ) ≤ A ^ (-(5 / 2 : ℝ)) * fsXp t (797 / 2) :=
    mul_nonneg (Real.rpow_nonneg hA.le _) (fsXp_pos ht).le
  have hQK : (0:ℝ) ≤ (2 * (Real.sqrt C₀ * Real.sqrt C₁ * Real.sqrt Cχ * Real.sqrt ((2 * Real.pi) ^ 3))) *
      (A ^ (-(5 / 2 : ℝ)) * fsXp t (797 / 2)) :=
    mul_nonneg (mul_nonneg (by norm_num) hQ) hK
  calc
    2 * Real.sqrt (C₀ * ((A * fsXp t (-163))⁻¹) ^ 2) *
        Real.sqrt (C₁ * (1 + ((A * fsXp t (-163)) * fsXp t 6)⁻¹
            + |Real.log (fsXp t 6)|) ^ 3
          * (((A * fsXp t (-163)) * fsXp t 6) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)
      = 2 * (Real.sqrt C₀ * Real.sqrt C₁ * Real.sqrt Cχ * Real.sqrt ((2 * Real.pi) ^ 3)) *
          ((A * fsXp t (-163))⁻¹ * ((A * fsXp t (-163) * fsXp t 6)⁻¹) ^ (3 / 2 : ℝ)) *
          Real.sqrt ((1 + ((A * fsXp t (-163)) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3) := by
        rw [cross_sqrt_split1 h₀ hℓ, cross_sqrt_split2 h₁ hLnn hprod]
        ring
    _ = 2 * (Real.sqrt C₀ * Real.sqrt C₁ * Real.sqrt Cχ * Real.sqrt ((2 * Real.pi) ^ 3)) *
          (A ^ (-(5 / 2 : ℝ)) * fsXp t (797 / 2)) *
          Real.sqrt ((1 + ((A * fsXp t (-163)) * fsXp t 6)⁻¹ + |Real.log (fsXp t 6)|) ^ 3) := by
        rw [hkey]
    _ ≤ 2 * (Real.sqrt C₀ * Real.sqrt C₁ * Real.sqrt Cχ * Real.sqrt ((2 * Real.pi) ^ 3)) *
          (A ^ (-(5 / 2 : ℝ)) * fsXp t (797 / 2)) *
          (Real.sqrt 8 * (1 + |Real.log t|) ^ (3 / 2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hcube hQK
    _ = 2 * Real.sqrt (8 * C₀ * C₁ * Cχ * (2 * Real.pi) ^ 3) * A ^ (-(5 / 2 : ℝ)) *
          fsXp t (797 / 2) * (1 + |Real.log t|) ^ (3 / 2 : ℝ) := by
        rw [cross_sqrt_split3 h₀ h₁ hχ]
        ring

end Work.BoseFixB1S.CorrAux
