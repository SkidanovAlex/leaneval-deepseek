/-
# N4 — the modulation constants `μ̄`, `μ` and the smallness of `μ`

This module proves, from the zero-mode estimates collected in `RowInputs`:

* `mubar_bound`: `|μ̄| = |L₁₂(N₀)(0) + L₁₂(N)(0)| ≤ 2(α² + √α X + α^{-3/2}X²)`;
* `mu_bound`: `|μ| ≤ 4(α + α^{-1}X + α^{-5/2}X²)` (design L-N4.8; this is stronger than the
  paper's `α^{-3/2}X`, as the paper's Remark at tex 1510 says);
* `mu_le_half`: under the a-priori assumption `X ≤ α^{7/4}` one gets `|μ| ≤ 1/2` for
  `α ≤ α₄`, whence in particular `μ ≠ -1`;
* `lamfun_add`: `μ + lamfun μ + μ·lamfun μ = -μ` whenever `μ ≠ -1`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.Construction.MufunS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlin

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `μ̄` -/

/-- `μ̄ = L₁₂(N₀)(0) + L₁₂(N)(0)` is bounded by the triangle inequality. -/
theorem mubar_bound {N0v Nv : Fn} {α X : ℝ}
    (h0 : |Work.Construction.L12 N0v 0| ≤ α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
    (h1 : |Work.Construction.L12 Nv 0| ≤ α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) :
    |Work.Construction.mubar N0v Nv|
      ≤ 2 * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
  rw [Work.Construction.mubar]
  linarith [abs_add_le (Work.Construction.L12 N0v 0) (Work.Construction.L12 Nv 0)]

/-! ## `μ` -/

/-- `μ̄` with a scaling constant `K ≥ 0`. -/
theorem mubar_bound_mul {N0v Nv : Fn} {α X K : ℝ} (hK : 0 ≤ K)
    (h0 : |Work.Construction.L12 N0v 0|
      ≤ K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h1 : |Work.Construction.L12 Nv 0|
      ≤ K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)) :
    |Work.Construction.mubar N0v Nv| ≤ 2 * (K * (α ^ 2 + Real.sqrt α * X
      + α ^ (-(3 / 2 : ℝ)) * X ^ 2)) := by
  rw [Work.Construction.mubar]
  have h := abs_add_le (Work.Construction.L12 N0v 0) (Work.Construction.L12 Nv 0)
  linarith

/-- **Design L-N4.8, with a scaling constant `K ≥ 0`.**  From the paper's three zero-mode
estimates (each carrying a constant `K`) one gets
`|μ| ≤ 4K(α + α^{-1}X + α^{-5/2}X²)`, with `X = |g|_{ℋ⁴}`.  The constant `μ` is the
sign-corrected `Construction.mufunS` and the proof is `Work.Construction.mu_bound_mulS`. -/
theorem mu_bound_mul {α X K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) (hK : 0 ≤ K)
    {N0v Nv g : Fn}
    (h0 : |Work.Construction.L12 N0v 0|
      ≤ K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h1 : |Work.Construction.L12 Nv 0|
      ≤ K * (α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2))
    (h2 : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ K * X) :
    |Work.Construction.mufunS α N0v Nv g|
      ≤ 4 * (K * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)) :=
  Work.Construction.mu_bound_mulS hα hα1 hX hK h0 h1 h2

/-- **Design L-N4.8.**  From the paper's three zero-mode estimates one gets
`|μ| ≤ 4(α + α^{-1}X + α^{-5/2}X²)`, with `X = |g|_{ℋ⁴}`; this is the `K = 1` case
(`Work.Construction.mu_boundS`) for the sign-corrected constant `Construction.mufunS`. -/
theorem mu_bound {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) {N0v Nv g : Fn}
    (h0 : |Work.Construction.L12 N0v 0| ≤ α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
    (h1 : |Work.Construction.L12 Nv 0| ≤ α ^ 2 + Real.sqrt α * X + α ^ (-(3 / 2 : ℝ)) * X ^ 2)
    (h2 : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ X) :
    |Work.Construction.mufunS α N0v Nv g|
      ≤ 4 * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) :=
  Work.Construction.mu_boundS hα hα1 hX h0 h1 h2

/-! ## Smallness of `μ` -/

/-- **`|μ| ≤ 1/2`** under the a-priori bound `X ≤ α^{7/4}` (design §2.5). -/
theorem mu_le_half (C : ℝ) (hC : 0 < C) :
    ∃ α₄ : ℝ, 0 < α₄ ∧ ∀ α : ℝ, 0 < α → α ≤ α₄ → ∀ X : ℝ, 0 ≤ X →
      X ≤ α ^ (7 / 4 : ℝ) → ∀ μ : ℝ,
      |μ| ≤ C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) → |μ| ≤ 1 / 2 := by
  have h6C : (0 : ℝ) < 6 * C := by linarith
  refine ⟨min 1 ((1 / (6 * C)) ^ (4 / 3 : ℝ)),
    lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _), ?_⟩
  intro α hα hαle X hX0 hX μ hμ
  have hα1 : α ≤ 1 := le_trans hαle (min_le_left _ _)
  have hαc : α ≤ (1 / (6 * C)) ^ (4 / 3 : ℝ) := le_trans hαle (min_le_right _ _)
  have h1 : α ^ (-(1 : ℝ)) * X ≤ α ^ (3 / 4 : ℝ) := by
    have hrw : α ^ (-(1 : ℝ)) * α ^ (7 / 4 : ℝ) = α ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_add hα]; norm_num
    calc α ^ (-(1 : ℝ)) * X ≤ α ^ (-(1 : ℝ)) * α ^ (7 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hX (Real.rpow_nonneg hα.le _)
      _ = α ^ (3 / 4 : ℝ) := hrw
  have h2 : α ^ (-(5 / 2 : ℝ)) * X ^ 2 ≤ α := by
    have hX2 : X ^ 2 ≤ (α ^ (7 / 4 : ℝ)) ^ 2 := by nlinarith
    have hpow : α ^ (-(5 / 2 : ℝ)) * (α ^ (7 / 4 : ℝ)) ^ 2 = α := by
      have hsq : (α ^ (7 / 4 : ℝ)) ^ 2 = α ^ (7 / 2 : ℝ) := by
        rw [← Real.rpow_natCast (α ^ (7 / 4 : ℝ)) 2, ← Real.rpow_mul hα.le]; norm_num
      rw [hsq, ← Real.rpow_add hα]; norm_num
    calc α ^ (-(5 / 2 : ℝ)) * X ^ 2 ≤ α ^ (-(5 / 2 : ℝ)) * (α ^ (7 / 4 : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hX2 (Real.rpow_nonneg hα.le _)
      _ = α := hpow
  have h3' : α ^ (3 / 4 : ℝ) ≤ 1 / (6 * C) := by
    have h4 : ((1 / (6 * C)) ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) = 1 / (6 * C) := by
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / (6 * C)),
        show (4 / 3 : ℝ) * (3 / 4) = 1 by norm_num, Real.rpow_one]
    calc α ^ (3 / 4 : ℝ) ≤ ((1 / (6 * C)) ^ (4 / 3 : ℝ)) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow hα.le hαc (by norm_num)
      _ = 1 / (6 * C) := h4
  have hαle' : α ≤ α ^ (3 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα hα1 (x := α)
      (y := (1 : ℝ)) (z := (3 / 4 : ℝ)) (by norm_num)
    rwa [Real.rpow_one] at h
  have hsum : α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2 ≤ 3 * (1 / (6 * C)) := by
    linarith [h1, h2, hαle', h3']
  have hfin : C * (α + α ^ (-(1 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hsum hC.le
    have he : C * (3 * (1 / (6 * C))) = 1 / 2 := by field_simp; ring
    linarith [h, he.le, he.ge]
  linarith [hμ, hfin]

/-! ## The paper's choice of `λ` -/

/-- For `μ ≠ -1` the paper's choice `λ = -2μ/(1+μ)` satisfies `μ + λ + μλ = -μ`. -/
theorem lamfun_add {μ : ℝ} (hμ : μ ≠ -1) :
    μ + Work.Construction.lamfun μ + μ * Work.Construction.lamfun μ = -μ := by
  have h1μ : (1 + μ) ≠ 0 := by intro h; exact hμ (by linarith)
  rw [Work.Construction.lamfun]
  have hfac : μ + (-2 * μ / (1 + μ)) + μ * (-2 * μ / (1 + μ))
      = μ + (-2 * μ / (1 + μ)) * (1 + μ) := by ring
  rw [hfac, div_mul_cancel₀ (-2 * μ) h1μ]
  ring

end Work.FTS.Nonlin
