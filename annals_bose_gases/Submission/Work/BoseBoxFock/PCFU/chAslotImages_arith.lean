import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

/-- Pure real arithmetic for the `(A)`-channel lattice-image slot bound.
(`Work.BoseBoxFock.PCFU.chAslotImages_arith`.) -/
theorem chAslotImages_arith {Cg ℓ R D N a chiSup : ℝ} (M : ℕ)
    (hℓ : 0 < ℓ) (hR : 0 < R) (h2R : 2 * R ≤ ℓ) (hchi : 0 < chiSup) (hCg : 0 ≤ Cg) :
    ℓ ^ 3 * (Cg * (R / ℓ) ^ (2 * M)) * (343 * 8 * Real.sqrt Real.pi * Real.sqrt a)
        * (Real.sqrt (4 * N / ℓ ^ 3) * Real.sqrt D)
      ≤ (343 * Cg * 16 * Real.sqrt Real.pi / (Real.sqrt chiSup * (4 * R ^ 2)) + 1)
        * (R / ℓ) ^ (2 * M) * Real.sqrt chiSup * Real.sqrt a * ℓ ^ 3 * Real.sqrt ℓ
        * Real.sqrt D * Real.sqrt N := by
  -- Rescale the image slot: `√(4N/ℓ³) = 2√N/(ℓ√ℓ)` (both sides vanish for `N < 0`).
  have hsq : Real.sqrt (4 * N / ℓ ^ 3) = 2 * Real.sqrt N / (ℓ * Real.sqrt ℓ) := by
    have hℓ3 : (0:ℝ) < ℓ^3 := by positivity
    rw [Real.sqrt_div' (4*N) hℓ3.le]
    have h4 : Real.sqrt (4:ℝ) = 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Real.sqrt_mul (show (0:ℝ) ≤ 4 by norm_num) N, h4]
    have hℓ3' : Real.sqrt (ℓ^3) = ℓ * Real.sqrt ℓ := by
      rw [show ℓ^3 = ℓ^2 * ℓ by ring, Real.sqrt_mul (sq_nonneg ℓ) ℓ, Real.sqrt_sq hℓ.le]
    rw [hℓ3']
  -- Left-hand side, in the rescaled normal form.
  have hLHS_eq : ℓ ^ 3 * (Cg * (R / ℓ) ^ (2 * M)) * (343 * 8 * Real.sqrt Real.pi * Real.sqrt a)
        * (Real.sqrt (4 * N / ℓ ^ 3) * Real.sqrt D)
      = (343 * 16 * Cg * Real.sqrt Real.pi * (R/ℓ)^(2*M) * Real.sqrt a * Real.sqrt D * Real.sqrt N)
        * (ℓ^2 / Real.sqrt ℓ) := by
    rw [hsq]
    field_simp
    ring
  have hsℓ : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  have h4R2 : 0 < 4 * R^2 := by positivity
  -- `2R ≤ ℓ` gives `4R² ≤ ℓ²`.
  have h4R2le : 4 * R^2 ≤ ℓ^2 := by
    have h1 : 0 ≤ ℓ - 2*R := by linarith
    have h2 : 0 ≤ ℓ + 2*R := by linarith
    have h3 := mul_nonneg h1 h2
    nlinarith [h3]
  -- The two normal forms compare because `ℓ²/√ℓ ≤ ℓ³√ℓ/(4R²)`.
  have hratio : ℓ^2 / Real.sqrt ℓ ≤ ℓ^3 * Real.sqrt ℓ / (4*R^2) := by
    rw [div_le_div_iff₀ hsℓ h4R2]
    have h1 : ℓ^3 * Real.sqrt ℓ * Real.sqrt ℓ = ℓ^3 * ℓ := by
      rw [mul_assoc, Real.mul_self_sqrt hℓ.le]
    rw [h1]
    nlinarith [mul_le_mul_of_nonneg_left h4R2le (sq_nonneg ℓ), sq_nonneg ℓ]
  have hA : 0 ≤ (343 * 16 * Cg * Real.sqrt Real.pi * (R/ℓ)^(2*M) * Real.sqrt a * Real.sqrt D * Real.sqrt N) := by
    positivity
  -- Right-hand side dominates the rescaled normal form (the `√chiSup` cancels).
  have hstep2 : (343 * 16 * Cg * Real.sqrt Real.pi * (R/ℓ)^(2*M) * Real.sqrt a * Real.sqrt D * Real.sqrt N)
        * (ℓ^3 * Real.sqrt ℓ / (4*R^2))
      ≤ (343 * Cg * 16 * Real.sqrt Real.pi / (Real.sqrt chiSup * (4 * R ^ 2)) + 1)
        * (R / ℓ) ^ (2 * M) * Real.sqrt chiSup * Real.sqrt a * ℓ ^ 3 * Real.sqrt ℓ
        * Real.sqrt D * Real.sqrt N := by
    have hX : 0 ≤ (R / ℓ) ^ (2 * M) * Real.sqrt chiSup * Real.sqrt a * ℓ^3 * Real.sqrt ℓ
        * Real.sqrt D * Real.sqrt N := by positivity
    have hid : (343 * Cg * 16 * Real.sqrt Real.pi / (Real.sqrt chiSup * (4 * R ^ 2)))
          * ((R / ℓ) ^ (2 * M) * Real.sqrt chiSup * Real.sqrt a * ℓ^3 * Real.sqrt ℓ * Real.sqrt D * Real.sqrt N)
        = (343 * 16 * Cg * Real.sqrt Real.pi * (R/ℓ)^(2*M) * Real.sqrt a * Real.sqrt D * Real.sqrt N)
          * (ℓ^3 * Real.sqrt ℓ / (4*R^2)) := by
      field_simp
    calc (343 * 16 * Cg * Real.sqrt Real.pi * (R/ℓ)^(2*M) * Real.sqrt a * Real.sqrt D * Real.sqrt N)
          * (ℓ^3 * Real.sqrt ℓ / (4*R^2))
        = (343 * Cg * 16 * Real.sqrt Real.pi / (Real.sqrt chiSup * (4 * R ^ 2)))
          * ((R / ℓ) ^ (2 * M) * Real.sqrt chiSup * Real.sqrt a * ℓ^3 * Real.sqrt ℓ
              * Real.sqrt D * Real.sqrt N) := hid.symm
      _ ≤ (343 * Cg * 16 * Real.sqrt Real.pi / (Real.sqrt chiSup * (4 * R ^ 2)) + 1)
          * ((R / ℓ) ^ (2 * M) * Real.sqrt chiSup * Real.sqrt a * ℓ^3 * Real.sqrt ℓ
              * Real.sqrt D * Real.sqrt N) := by
            nlinarith [hX]
      _ = (343 * Cg * 16 * Real.sqrt Real.pi / (Real.sqrt chiSup * (4 * R ^ 2)) + 1)
        * (R / ℓ) ^ (2 * M) * Real.sqrt chiSup * Real.sqrt a * ℓ ^ 3 * Real.sqrt ℓ
        * Real.sqrt D * Real.sqrt N := by ring
  calc ℓ ^ 3 * (Cg * (R / ℓ) ^ (2 * M)) * (343 * 8 * Real.sqrt Real.pi * Real.sqrt a)
        * (Real.sqrt (4 * N / ℓ ^ 3) * Real.sqrt D)
      = (343 * 16 * Cg * Real.sqrt Real.pi * (R/ℓ)^(2*M) * Real.sqrt a * Real.sqrt D * Real.sqrt N)
        * (ℓ^2 / Real.sqrt ℓ) := hLHS_eq
    _ ≤ (343 * 16 * Cg * Real.sqrt Real.pi * (R/ℓ)^(2*M) * Real.sqrt a * Real.sqrt D * Real.sqrt N)
        * (ℓ^3 * Real.sqrt ℓ / (4*R^2)) := mul_le_mul_of_nonneg_left hratio hA
    _ ≤ (343 * Cg * 16 * Real.sqrt Real.pi / (Real.sqrt chiSup * (4 * R ^ 2)) + 1)
        * (R / ℓ) ^ (2 * M) * Real.sqrt chiSup * Real.sqrt a * ℓ ^ 3 * Real.sqrt ℓ
        * Real.sqrt D * Real.sqrt N := hstep2

end Work.BoseBoxFock.PCFU
