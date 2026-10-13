import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.RegExportIface.Defs
import Submission.Work.FTS_RegExport.RXR5.Fstar_C1Jet

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXVP

open scoped Real

/-- The angular coefficient `c2m θ = cos 2θ − sin²θ` is bounded by `2` in absolute value
(its range is `[-2, 1]`). -/
theorem abs_c2m_le_two (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq]
  have h1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
  have h2 : |Real.sin θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg (Real.sin θ))]
    exact Real.sin_sq_le_one θ
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      ≤ |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

/-- **The `vz0` clause of RX-VP from abstract bounds.** If the clock satisfies `|μ| ≤ 1/2`, the
closed-form coefficients obey `|L₁₂(F(τ))(z)| ≤ 2 αG/(1+z) + M` and `|V(Φ̃(τ))(z,θ)| ≤ M` on the
open quadrant, and the smallness condition `4 αG + 2 M + 2 αG M ≤ 1/2` holds, then
`Vz7 = (1−μ) + L₁₂(F)·c2m + 2 αG·V(Φ̃) ≥ 0` there.

Indeed `1 − μ ≥ 1/2`, `|c2m| ≤ 2` and `1/(1+z) ≤ 1` give
`Vz7 ≥ 1/2 − 2·(2αG/(1+z) + M) − 2αG M ≥ 1/2 − (4αG + 2M + 2αG M) ≥ 0`. -/
theorem vz7_nonneg_of_bounds {αG M : ℝ} (hαG : 0 < αG) (hM : 0 ≤ M)
    {μ : ℝ → ℝ} {G Φ : Work.FTS.Galerkin.Fam}
    (hmu : ∀ τ : ℝ, |μ τ| ≤ 1 / 2)
    (hLF : ∀ z τ : ℝ, 0 < z →
      |Work.Construction.L12 (Work.Construction.Ftau αG G τ) z|
        ≤ 2 * αG / (1 + z) + M)
    (hV : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop
        (Work.FTS.RegExportIface.phiTil αG G Φ τ) z θ| ≤ M)
    (hsmall : 4 * αG + 2 * M + 2 * αG * M ≤ 1 / 2) :
    ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      0 ≤ Work.FTS.RegExportIface.Vz7 αG μ G Φ z θ τ := by
  intro z θ τ hz hθ hθ2
  show (0 : ℝ) ≤ (1 - μ τ)
    + Work.Construction.L12 (Work.Construction.Ftau αG G τ) z * Work.Construction.c2m θ
    + 2 * αG * Work.Construction.Vop (Work.FTS.RegExportIface.phiTil αG G Φ τ) z θ
  have hden : (0 : ℝ) < 1 + z := by linarith
  have hc2m : |Work.Construction.c2m θ| ≤ 2 := abs_c2m_le_two θ
  have hA : (0 : ℝ) ≤ 2 * αG / (1 + z) + M :=
    add_nonneg (div_nonneg (by linarith) hden.le) hM
  -- the clock term
  have hmu1 : (1 : ℝ) / 2 ≤ 1 - μ τ := by
    have h := (abs_le.mp (hmu τ)).2
    linarith
  -- the `L₁₂·c2m` term
  have hLb : -((2 * αG / (1 + z) + M) * 2)
      ≤ Work.Construction.L12 (Work.Construction.Ftau αG G τ) z * Work.Construction.c2m θ := by
    have h2 : |Work.Construction.L12 (Work.Construction.Ftau αG G τ) z * Work.Construction.c2m θ|
        ≤ (2 * αG / (1 + z) + M) * 2 := by
      rw [abs_mul]
      exact mul_le_mul (hLF z τ hz) hc2m (abs_nonneg _) hA
    have := neg_abs_le
      (Work.Construction.L12 (Work.Construction.Ftau αG G τ) z * Work.Construction.c2m θ)
    linarith
  -- the `V` term
  have hVb : -(2 * αG * M)
      ≤ 2 * αG * Work.Construction.Vop (Work.FTS.RegExportIface.phiTil αG G Φ τ) z θ := by
    have hV' : -M ≤ Work.Construction.Vop (Work.FTS.RegExportIface.phiTil αG G Φ τ) z θ :=
      (abs_le.mp (hV z θ τ hz hθ hθ2)).1
    have h2a : (0 : ℝ) ≤ 2 * αG := by linarith
    have := mul_le_mul_of_nonneg_left hV' h2a
    nlinarith [this]
  -- `1/(1+z) ≤ 1`
  have hdiv : 2 * αG / (1 + z) ≤ 2 * αG := by
    rw [div_le_iff₀ hden]
    nlinarith [hαG, hz]
  nlinarith [hmu1, hLb, hVb, hdiv, hsmall]

end Work.FTS_RegExport.RXVP
