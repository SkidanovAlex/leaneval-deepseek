import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.starPt
import Submission.Work.FTS.Nonlinear.Pieces.Rl1.StarUBound
import Submission.Work.FTS.Nonlinear.FstarPkg.FK_Fstar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# The five `sg`-rows of `N`: the pointwise bound of the `rl¹`-integrand

`Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs` bounds the `rl¹`-norm of the five `gs`-pieces
`K θ · Nᵢ^{gs}`.  This file does the same for the four `sg`-pieces
`N₁^{sg}, N₂^{sg}, N₃^{sg}` (which carry the `Φ̃_*`-coefficient and the `g`-profile) and the
two pieces `N₄^{sg}, N₅^{sg}` of the `F_*`-block, but *pointwise*, in the form needed by the
`rl¹`-envelope: for `0 < α ≤ 1`, a `StarPkg` stream function `Φ_s` and every `r > 0`,
`θ ∈ Iθ`,

`|K θ · N₁^{sg}| ≤ 6 max Cs 0 α |g|`, `|K θ · N₂^{sg}| ≤ 24 max Cs 0 α |∂_θg|`,
`|K θ · N₃^{sg}| ≤ 6 max Cs 0 α² |D_zg|`,
`|K θ · N₄^{sg}| ≤ 3α (r/(1+r)²) |∂_θg|`, `|K θ · N₅^{sg}| ≤ 6α (r/(1+r)²) |g|`.

The three `Φ̃_*`-rows are the same pointwise input as in `Pgs`: `|ℛ(Φ̃_*)| ≤ max Cs 0·α` and
`|𝒱(Φ̃_*)| ≤ max Cs 0·α` (`rl1Tools.starPt`).  `𝒰(Φ̃_*)` is *not* directly bounded by
`StarPkg` (only `∂_θ𝒰` is), but the exact identity
`K θ · 𝒰(Ψ) = 3 cos³θ · (𝒱(Ψ) - ℛ(Ψ))` (`sg_K_mul_Uop_eq`, equivalent to
`𝒱 - ℛ = tan θ · 𝒰` times `K θ/ tan θ = 3cos³θ`) removes the `𝒰`-factor entirely, so the
`N₂^{sg}`-row costs only the factor `2·3·(1+1) = 12 ≤ 24`.  The `F_*`-rows use
`FK(F_*) = α·2z/(1+z)²` (`FstarPkg.FK_Fstar`) together with `|K θ| ≤ 3` and
`|sin| ≤ 1`.
-/

/-- `|K θ| ≤ 3` for every `θ`, where `K θ = 3 sin θ cos²θ`. -/
theorem sg_abs_K_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hc2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg (Real.cos θ))]
    exact Real.cos_sq_le_one θ
  have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  calc 3 * |Real.sin θ| * |Real.cos θ ^ 2| ≤ 3 * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) hc2 (abs_nonneg _) (by norm_num)
    _ = 3 := by norm_num

/-- The product bound `|a · b| ≤ A · B` from `|a| ≤ A`, `|b| ≤ B` and `A ≥ 0`. -/
theorem sg_abs_mul_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hA : 0 ≤ A) :
    |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) hA

/-- **The `𝒰`-identity**: `K θ · 𝒰(Ψ) = 3 cos³θ · (𝒱(Ψ) - ℛ(Ψ))` whenever `cos θ ≠ 0`.

It is the product of `𝒱(Ψ) - ℛ(Ψ) = tan θ · 𝒰(Ψ)` (both sides are `-(sin θ/cos θ)·(3Ψ + αz∂_zΨ)`)
with `K θ / tan θ = 3 sin θ cos²θ · cos θ/sin θ = 3 cos³θ`; written as a polynomial identity
after multiplying by `cos θ`, so that no division by `sin θ` occurs. -/
theorem sg_K_mul_Uop_eq (α : ℝ) (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ} (hc : Real.cos θ ≠ 0) :
    Work.Spaces.K θ * Work.Construction.Uop α Ψ z θ
      = 3 * Real.cos θ ^ 3 * (Work.Construction.Vop Ψ z θ
          - Work.Construction.Rop α Ψ z θ) := by
  simp only [Work.Spaces.K, Work.Construction.Uop, Work.Construction.Vop,
    Work.Construction.Rop, Real.tan_eq_sin_div_cos]
  field_simp
  ring

/-- **The `𝒰(Φ̃_*)`-row.**  `|K θ · 𝒰(Φ̃_*)| ≤ 6 max Cs 0 α` on `z > 0`, `θ ∈ Iθ`.

At `θ = π/2` both sides degenerate (`K (π/2) = 0`); otherwise `sg_K_mul_Uop_eq` turns the
left side into `3 cos³θ·|𝒱 - ℛ| ≤ 3·1·(max Cs 0 α + max Cs 0 α)`. -/
theorem sg_K_mul_Uop_bound {α Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.K θ * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
      ≤ 6 * max Cs 0 * α := by
  obtain ⟨hR, hV, -⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs
  have hM : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right Cs 0) hα.le
  rcases eq_or_lt_of_le hθ.2 with hpi | hlt
  · rw [hpi, show Work.Spaces.K (Real.pi / 2) = 0 by
        simp [Work.Spaces.K, Real.cos_pi_div_two], zero_mul, abs_zero]
    linarith
  · have hcpos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hlt⟩
    rw [sg_K_mul_Uop_eq α _ (ne_of_gt hcpos), abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    have hc3 : |Real.cos θ ^ 3| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hcpos.le 3)]
      exact pow_le_one₀ hcpos.le (Real.cos_le_one θ)
    have h1 : |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ max Cs 0 * α :=
      hV z (le_of_lt hz) θ hθ
    have h2 : |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ| ≤ max Cs 0 * α :=
      hR z hz θ hθ
    have h3 : |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        - Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
        ≤ max Cs 0 * α + max Cs 0 * α := by
      have h := abs_sub_le (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ) 0
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ)
      simp only [sub_zero, zero_sub, abs_neg] at h
      linarith
    calc 3 * |Real.cos θ ^ 3| * |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
          - Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) z θ|
        ≤ 3 * 1 * (max Cs 0 * α + max Cs 0 * α) := by gcongr
      _ = 6 * max Cs 0 * α := by ring

/-- `|FK(F_*) r| = α · 2r/(1+r)²` for `r > 0` (`FstarPkg.FK_Fstar` plus `α·2r/(1+r)² ≥ 0`). -/
theorem sg_abs_FK_Fstar {α r : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hr : 0 < r) :
    |Work.Construction.FK (Work.Construction.Fstar α) r| = α * (2 * r / (1 + r) ^ 2) := by
  rw [Work.FTS.Nonlinear.FstarPkg.FK_Fstar hα hα1]
  exact abs_of_nonneg (by positivity)

theorem sgRowsPtwise {α Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {Φs g : Work.FTS.Galerkin.Fn}
    (hs : Work.FTS.Nonlin.StarPkg α Cs Φs) :
    (∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ| ≤ 6 * max Cs 0 * α * |g r θ|) ∧
    (∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ| ≤ 24 * max Cs 0 * α * |Work.Spaces.pth g r θ|) ∧
    (∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ| ≤ 6 * max Cs 0 * α ^ 2 * |Work.Spaces.Dz g r θ|) ∧
    (∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ| ≤ 3 * α * (r / (1 + r) ^ 2) * |Work.Spaces.pth g r θ|) ∧
    (∀ r : ℝ, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ| ≤ 6 * α * (r / (1 + r) ^ 2) * |g r θ|) := by
  obtain ⟨hR, hV, -⟩ := Work.FTS.Nonlinear.Pieces.rl1Tools.starPt hα hs
  have hM : 0 ≤ max Cs 0 * α := mul_nonneg (le_max_right Cs 0) hα.le
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `N₁^{sg} = 2ℛ(Φ̃_*) g`
    intro r hr θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 := sg_abs_K_le_three θ
    have h1 : |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ| ≤ max Cs 0 * α :=
      hR r hr θ hθ
    have hsplit : Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ
        = 2 * (Work.Spaces.K θ * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ)
            * g r θ := by
      simp only [Work.FTS.Nonlin.N1sg]
      ring
    have h2 : |Work.Spaces.K θ * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
        ≤ 3 * (max Cs 0 * α) := sg_abs_mul_le hK h1 (by norm_num)
    calc |Work.Spaces.K θ * Work.FTS.Nonlin.N1sg α Φs g r θ|
        = 2 * |Work.Spaces.K θ * Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
            * |g r θ| := by
          rw [hsplit, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (3 * (max Cs 0 * α)) * |g r θ| := by gcongr
      _ = 6 * max Cs 0 * α * |g r θ| := by ring
  · -- `N₂^{sg} = -2𝒰(Φ̃_*) ∂_θg`
    intro r hr θ hθ
    have hU := sg_K_mul_Uop_bound hα hs hr hθ
    have hsplit : Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ
        = -(2 * (Work.Spaces.K θ * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ)
            * Work.Spaces.pth g r θ) := by
      simp only [Work.FTS.Nonlin.N2sg]
      ring
    calc |Work.Spaces.K θ * Work.FTS.Nonlin.N2sg α Φs g r θ|
        = 2 * |Work.Spaces.K θ * Work.Construction.Uop α (Work.FTS.Nonlin.PhiTs α Φs) r θ|
            * |Work.Spaces.pth g r θ| := by
          rw [hsplit, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * (6 * max Cs 0 * α) * |Work.Spaces.pth g r θ| := by gcongr
      _ ≤ 24 * max Cs 0 * α * |Work.Spaces.pth g r θ| := by
          nlinarith [hM, abs_nonneg (Work.Spaces.pth g r θ)]
  · -- `N₃^{sg} = -2α𝒱(Φ̃_*) D_zg`
    intro r hr θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 := sg_abs_K_le_three θ
    have h1 : |Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ| ≤ max Cs 0 * α :=
      hV r (le_of_lt hr) θ hθ
    have hsplit : Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ
        = -(2 * α * (Work.Spaces.K θ * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ)
            * Work.Spaces.Dz g r θ) := by
      simp only [Work.FTS.Nonlin.N3sg]
      ring
    have h2 : |Work.Spaces.K θ * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|
        ≤ 3 * (max Cs 0 * α) := sg_abs_mul_le hK h1 (by norm_num)
    calc |Work.Spaces.K θ * Work.FTS.Nonlin.N3sg α Φs g r θ|
        = 2 * α * |Work.Spaces.K θ * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) r θ|
            * |Work.Spaces.Dz g r θ| := by
          rw [hsplit, abs_neg, abs_mul, abs_mul,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * α)]
      _ ≤ 2 * α * (3 * (max Cs 0 * α)) * |Work.Spaces.Dz g r θ| := by gcongr
      _ = 6 * max Cs 0 * α ^ 2 * |Work.Spaces.Dz g r θ| := by ring
  · -- `N₄^{sg} = -(1/2) FK(F_*) D_θg`
    intro r hr θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 := sg_abs_K_le_three θ
    have hFK : |Work.Construction.FK (Work.Construction.Fstar α) r|
        ≤ α * (2 * r / (1 + r) ^ 2) := le_of_eq (sg_abs_FK_Fstar hα hα1 hr)
    have hs2 : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one (2 * θ)
    calc |Work.Spaces.K θ * Work.FTS.Nonlin.N4sg α g r θ|
        = (1 / 2) * |Work.Spaces.K θ|
            * |Work.Construction.FK (Work.Construction.Fstar α) r|
            * (|Real.sin (2 * θ)| * |Work.Spaces.pth g r θ|) := by
          simp only [Work.FTS.Nonlin.N4sg, Work.Spaces.Dth, abs_mul, abs_neg,
            abs_of_nonneg (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num)]
          ring
      _ ≤ (1 / 2) * 3 * (α * (2 * r / (1 + r) ^ 2)) * (1 * |Work.Spaces.pth g r θ|) := by
          gcongr
      _ = 3 * α * (r / (1 + r) ^ 2) * |Work.Spaces.pth g r θ| := by ring
  · -- `N₅^{sg} = -sin²θ FK(F_*) g`
    intro r hr θ hθ
    have hK : |Work.Spaces.K θ| ≤ 3 := sg_abs_K_le_three θ
    have hFK : |Work.Construction.FK (Work.Construction.Fstar α) r|
        ≤ α * (2 * r / (1 + r) ^ 2) := le_of_eq (sg_abs_FK_Fstar hα hα1 hr)
    have hs2 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
    calc |Work.Spaces.K θ * Work.FTS.Nonlin.N5sg α g r θ|
        = |Work.Spaces.K θ| * Real.sin θ ^ 2
            * |Work.Construction.FK (Work.Construction.Fstar α) r| * |g r θ| := by
          simp only [Work.FTS.Nonlin.N5sg, abs_mul, abs_neg,
            abs_of_nonneg (sq_nonneg (Real.sin θ))]
          ring
      _ ≤ 3 * 1 * (α * (2 * r / (1 + r) ^ 2)) * |g r θ| := by gcongr
      _ = 6 * α * (r / (1 + r) ^ 2) * |g r θ| := by ring

end

end Work.FTS.Nonlinear.Pieces.rl1Pieces
