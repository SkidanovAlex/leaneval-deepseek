/-
# `Work.FTS.Regularity.fstarModuli` — the moduli of the fundamental-model profile

This file proves the "profile moduli" input of node N7 of the audit:
for `0 < α ≤ 1/3` there are constants `Cθ, Cz, Cz'` such that

* `Γ(θ) = (sin θ cos²θ)^α` is `α`-Hölder on `Iθ = [0,π/2]` with constant `Cθ`,
* `z ↦ F_*(z,θ) = α(Γ(θ)/c(α))·2z/(1+z)²` is Lipschitz in `z` on `[0,∞)`, uniformly in `θ ∈ Iθ`,
  with constant `Cz`,
* `z ↦ ∂_z F_*(z,θ)` is Lipschitz in `z` on `(0,∞)`, uniformly in `θ ∈ Iθ`, with constant `Cz'`.

The quantitative ingredients are the four lemmas of `Work.FTS.Regularity.Moduli`
(`rpow_abs_sub_le`, `sinCosSqLip`, `fstarLip`, `fstarDerivLip`); the assembly below combines them
with the normalisation bound `1/10 ≤ c(3α) ≤ 10` (`Work.Spaces.c_bounds`) and the angular bound
`0 ≤ Γ ≤ 1` (`Work.ConstructionInstance.Gamma_nonneg`, `Gamma_le_one`), and evaluates the
`z`-derivative with `Work.FM.hasDerivAt_Fstar`.

The explicit constants obtained are `Cθ = 3^α`, `Cz = 20`, `Cz' = 80`: the coefficient
`(3α)·(Γ(3α)/c(3α))` of `2z/(1+z)²` in the profile is bounded by `10`, the profile itself is
`2`-Lipschitz and its derivative is `8`-Lipschitz on `[0,∞)`.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.Spaces.c_bounds
import Submission.Work.FM.Core
import Submission.Work.FTS.Regularity.Moduli.rpow_abs_sub_le
import Submission.Work.FTS.Regularity.Moduli.sinCosSqLip
import Submission.Work.FTS.Regularity.Moduli.fstarLip
import Submission.Work.FTS.Regularity.Moduli.fstarDerivLip

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Work.FTS.Regularity

open FiniteTimeSingularity Set Filter Topology MeasureTheory

/-! ## The reduction of `Fstar (3α)` to a constant times the fundamental-model profile -/

/-- `Γ` at the profile exponent: `Spaces.Gam (3α) = Gamma α`, since `(sinθcos²θ)^((3α)/3)` and
`(sinθcos²θ)^α` agree. -/
theorem gam_three (α θ : ℝ) : Work.Spaces.Gam (3 * α) θ = Gamma α θ := by
  rw [← Work.ConstructionInstance.Gamma_div_three (3 * α) θ]
  norm_num

/-- The coefficient `(3α)·(Γ(3α)/c(3α))` of `F_*` in the profile `Fstar (3α)` is bounded by
`10` on the angular domain: `0 < 3α ≤ 1`, `0 ≤ Γ ≤ 1` and `c(3α) ≥ 1/10`. -/
theorem fstarCoeff_abs_le {α θ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |(3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))| ≤ 10 := by
  have h3a : 0 < 3 * α := by linarith
  have h3a1 : 3 * α ≤ 1 := by linarith
  have hc := Work.Spaces.c_bounds (3 * α) h3a h3a1
  have hcpos : 0 < Work.Spaces.c (3 * α) := by linarith [hc.1]
  have hG : |Work.Spaces.Gam (3 * α) θ| ≤ 1 := by
    rw [gam_three α θ, abs_of_nonneg (Work.ConstructionInstance.Gamma_nonneg (β := α) hθ)]
    exact Work.ConstructionInstance.Gamma_le_one hα.le hθ
  rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 3 * α), abs_div, abs_of_pos hcpos]
  have hdiv : |Work.Spaces.Gam (3 * α) θ| / Work.Spaces.c (3 * α) ≤ 10 := by
    rw [div_le_iff₀ hcpos]
    nlinarith [hc.2, hG]
  calc (3 * α) * (|Work.Spaces.Gam (3 * α) θ| / Work.Spaces.c (3 * α))
      ≤ 1 * 10 := mul_le_mul h3a1 hdiv (by positivity) (by norm_num)
    _ = 10 := by ring

/-- The profile is a constant (in `z`) times `F_* z`. -/
theorem fstar_three_eq (α z θ : ℝ) :
    Work.Construction.Fstar (3 * α) z θ
      = ((3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))) * Work.FM.Fstar z := by
  rw [Work.Construction.Fstar]

/-- The `z`-derivative of the profile is the same constant times `∂_z F_*`, for `z ≥ 0`. -/
theorem pz_fstar_three_eq {α θ w : ℝ} (hw : 0 ≤ w) :
    Work.Spaces.pz (fun z θ => Work.Construction.Fstar (3 * α) z θ) w θ
      = ((3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)))
        * deriv Work.FM.Fstar w := by
  have hd : DifferentiableAt ℝ Work.FM.Fstar w :=
    (Work.FM.hasDerivAt_Fstar w (by linarith)).differentiableAt
  have hfun : (fun z' : ℝ => Work.Construction.Fstar (3 * α) z' θ)
      = fun z' : ℝ => ((3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)))
          * Work.FM.Fstar z' := by
    funext z'
    rw [Work.Construction.Fstar]
  rw [Work.Spaces.pz, hfun, deriv_const_mul _ hd]

/-! ## The three moduli -/

variable {α : ℝ}

/-- **The angular modulus**: `Γ = (sin θ cos²θ)^α` is `α`-Hölder on `Iθ` with constant `3^α`,
from the `3`-Lipschitz modulus of the base `sinθcos²θ` and the `α`-Hölder modulus of
`x ↦ x^α` on `[0,∞)`. -/
theorem gammaModulus (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∀ θ θ' : ℝ, θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |Gamma α θ - Gamma α θ'| ≤ 3 ^ α * |θ - θ'| ^ α := by
  intro θ θ' hθ hθ'
  have hb0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := by
    have h1 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    positivity
  have hb0' : 0 ≤ Real.sin θ' * Real.cos θ' ^ 2 := by
    have h1 : 0 ≤ Real.sin θ' :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ'.1 (by linarith [hθ'.2, Real.pi_pos])
    positivity
  have hlip := Work.FTS.Regularity.Moduli.sinCosSqLip θ θ'
  calc |Gamma α θ - Gamma α θ'|
      = |(Real.sin θ * Real.cos θ ^ 2) ^ α - (Real.sin θ' * Real.cos θ' ^ 2) ^ α| := rfl
    _ ≤ |Real.sin θ * Real.cos θ ^ 2 - Real.sin θ' * Real.cos θ' ^ 2| ^ α :=
        Work.FTS.Regularity.Moduli.rpow_abs_sub_le hb0 hb0' hα (by linarith)
    _ ≤ (3 * |θ - θ'|) ^ α := Real.rpow_le_rpow (abs_nonneg _) hlip hα.le
    _ = 3 ^ α * |θ - θ'| ^ α := by
        rw [Real.mul_rpow (by norm_num) (abs_nonneg _)]

/-- **The radial modulus of the profile**: `Fstar (3α)` is Lipschitz in `z` with constant `20`,
uniformly on `Iθ`. -/
theorem fstarModulus (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ|
        ≤ 20 * |z - z'| := by
  intro z z' θ hz hz' hθ
  have hC := fstarCoeff_abs_le hα hα13 hθ
  have hkey : Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ
      = ((3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α)))
        * (Work.FM.Fstar z - Work.FM.Fstar z') := by
    simp only [fstar_three_eq]
    ring
  rw [hkey, abs_mul]
  calc |(3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))|
        * |Work.FM.Fstar z - Work.FM.Fstar z'|
      ≤ 10 * (2 * |z - z'|) :=
        mul_le_mul hC (Work.FTS.Regularity.Moduli.fstarLip hz hz') (abs_nonneg _) (by norm_num)
    _ = 20 * |z - z'| := by ring

/-- **The radial modulus of `∂_z` of the profile**: `∂_z (Fstar (3α))` is Lipschitz in `z` with
constant `80`, uniformly on `Iθ`. -/
theorem pzFstarModulus (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∀ z z' θ : ℝ, 0 < z → 0 < z' → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (fun z θ => Work.Construction.Fstar (3 * α) z θ) z θ
        - Work.Spaces.pz (fun z θ => Work.Construction.Fstar (3 * α) z θ) z' θ|
        ≤ 80 * |z - z'| := by
  intro z z' θ hz hz' hθ
  have hC := fstarCoeff_abs_le hα hα13 hθ
  rw [pz_fstar_three_eq (α := α) (θ := θ) (w := z) hz.le,
    pz_fstar_three_eq (α := α) (θ := θ) (w := z') hz'.le, ← mul_sub, abs_mul]
  calc |(3 * α) * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))|
        * |deriv Work.FM.Fstar z - deriv Work.FM.Fstar z'|
      ≤ 10 * (8 * |z - z'|) :=
        mul_le_mul hC (Work.FTS.Regularity.Moduli.fstarDerivLip hz.le hz'.le)
          (abs_nonneg _) (by norm_num)
    _ = 80 * |z - z'| := by ring

/-! ## The target -/

theorem fstarModuli {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∃ Cθ Cz Cz' : ℝ, 0 ≤ Cθ ∧ 0 ≤ Cz ∧ 0 ≤ Cz' ∧
      (∀ θ θ' : ℝ, θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
        |Work.FTS.Regularity.Gamma α θ - Work.FTS.Regularity.Gamma α θ'|
          ≤ Cθ * |θ - θ'| ^ α) ∧
      (∀ z z' θ : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ →
        |Work.Construction.Fstar (3 * α) z θ - Work.Construction.Fstar (3 * α) z' θ|
          ≤ Cz * |z - z'|) ∧
      (∀ z z' θ : ℝ, 0 < z → 0 < z' → θ ∈ Work.Spaces.Iθ →
        |Work.Spaces.pz (fun z θ => Work.Construction.Fstar (3 * α) z θ) z θ
          - Work.Spaces.pz (fun z θ => Work.Construction.Fstar (3 * α) z θ) z' θ|
          ≤ Cz' * |z - z'|) :=
  ⟨3 ^ α, 20, 80, Real.rpow_nonneg (by norm_num) α, by norm_num, by norm_num,
   gammaModulus hα hα13, fstarModulus hα hα13, pzFstarModulus hα hα13⟩

end Work.FTS.Regularity
