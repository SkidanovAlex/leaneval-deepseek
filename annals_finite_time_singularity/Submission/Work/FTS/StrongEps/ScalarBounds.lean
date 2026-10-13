/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/ScalarBounds.lean` — the universal scalar bounds of the `G7` chain

The `G7` sup-bound chain of `E5` (`epsWP_abs_le_on_compact`, `epsWP_blocks_bnd`) is fed by scalar
bounds on the *explicit* coefficients of the scheme's right-hand side.  This module proves the
three that are universal (no hypothesis beyond `α ∈ (0,1]` and the normalisation
`c α ≥ 1/10`):

* `L12_Fstar_abs_le` — `|L₁₂(F_*)(z)| ≤ 2` for every `z ≥ 0` (the identity
  `L₁₂(F_*)(z) = 2α/(1+z)` of `Construction.L12_Fstar_eq`);
* `AK_abs_le` — `|AK α z θ| ≤ 10`;
* `coef_abs_le` — the two coefficients of `𝓛_Γ^T` are `≤ 10` in absolute value,

the last two using `Γ ≤ 1` (`Spaces.Gam_bounds`) and `z²/(1+z)³ ≤ 1` resp. `z/(1+z)² ≤ 1`.  They
are exactly the `hcoef`, `hcoef2`, `hAK`, `hL12F` hypotheses of the `G7` chain, with the unified
constant `B = 10` (so that the chain can use one `B`).
-/
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.Construction.Basic
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.Spaces.Gam_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

set_option autoImplicit false

/-- **`L₁₂(F_*)` is bounded by `2` on `[0,∞)`**: the identity `L₁₂(F_*)(z) = 2α/(1+z)`. -/
theorem L12_Fstar_abs_le :
    ∃ B : ℝ, 0 < B ∧ ∀ α ∈ Set.Ioc 0 1, ∀ z ∈ Work.Spaces.Iz,
      |Work.Construction.L12 (Work.Construction.Fstar α) z| ≤ B := by
  refine ⟨2, by norm_num, ?_⟩
  intro α hα z hz
  have hz0 : 0 ≤ z := hz
  rw [Work.Construction.L12_Fstar_eq hα.1 hα.2 hz0]
  have h1 : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos h1, abs_of_pos (by linarith [hα.1] : (0 : ℝ) < 2 * α)]
  rw [div_le_iff₀ h1]
  nlinarith [hα.1, hα.2, hz0]

/-- **The coefficient `AK = (Γ/c)·2z²/(1+z)³` is bounded by `10`.** -/
theorem AK_abs_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {c : ℝ} (hc : 1 / 10 ≤ c)
    (hceq : c = Work.Spaces.c α) :
    ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.AK α z θ| ≤ 10 := by
  subst hceq
  intro z θ hz hθ
  have hc0 : (0 : ℝ) < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc
  obtain ⟨_, hGam1⟩ := Work.Spaces.Gam_bounds α θ hα.1 hθ
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα.1 hθ).1
  -- `2z²/(1+z)³ ≤ 1` on `z ≥ 0`
  have hfrac : 2 * z ^ 2 / (1 + z) ^ 3 ≤ 1 := by
    have h1 : (0 : ℝ) < 1 + z := by linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [show (0 : ℝ) ≤ z ^ 2 * (1 + z) by positivity, hz]
  have hAK : Work.Construction.AK α z θ
      = (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3) := rfl
  rw [hAK, abs_mul, abs_of_nonneg (div_nonneg hGam0 hc0.le)]
  have hquot : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hc0]
    nlinarith [hGam1, hc]
  have hnn : 0 ≤ 2 * z ^ 2 / (1 + z) ^ 3 := by positivity
  calc Work.Spaces.Gam α θ / Work.Spaces.c α * |2 * z ^ 2 / (1 + z) ^ 3|
      = Work.Spaces.Gam α θ / Work.Spaces.c α * (2 * z ^ 2 / (1 + z) ^ 3) := by
        rw [abs_of_nonneg hnn]
    _ ≤ 10 * 1 := by
        refine mul_le_mul hquot hfrac hnn (by norm_num)
    _ = 10 := by norm_num

/-- **The two coefficients of `𝓛_Γ^T` are bounded by `10`** (the `hcoef`/`hcoef2` hypotheses of
the `G7` chain), for `α ∈ (0,1]` and `1/10 ≤ c α`. -/
theorem coef_abs_le {α : ℝ} (hα : α ∈ Set.Ioc 0 1) (hc : 1 / 10 ≤ Work.Spaces.c α) :
    ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2)| ≤ 10 ∧
      |Work.Spaces.Gam α θ / Work.Spaces.c α * (2 * z ^ 2 / (1 + z) ^ 3)| ≤ 10 := by
  intro z θ hz hθ
  have hc0 : (0 : ℝ) < Work.Spaces.c α := lt_of_lt_of_le (by norm_num) hc
  obtain ⟨hGam0, hGam1⟩ := Work.Spaces.Gam_bounds α θ hα.1 hθ
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have hquot : Work.Spaces.Gam α θ / Work.Spaces.c α ≤ 10 := by
    rw [div_le_iff₀ hc0]
    nlinarith [hGam1, hc]
  have hquot0 : 0 ≤ Work.Spaces.Gam α θ / Work.Spaces.c α := div_nonneg hGam0 hc0.le
  constructor
  · -- first coefficient: `2z/(1+z)² · (Γ/c)`
    have hfac : 2 * z / (1 + z) ^ 2 ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
      nlinarith [sq_nonneg (z - 1), hz]
    have hrw : 2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2)
        = (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z / (1 + z) ^ 2) := by
      field_simp
    rw [hrw, abs_mul, abs_of_nonneg hquot0, abs_of_nonneg (by positivity : 0 ≤ 2 * z / (1 + z) ^ 2)]
    nlinarith [hquot, hfac]
  · rw [abs_mul, abs_of_nonneg hquot0,
      abs_of_nonneg (by positivity : 0 ≤ 2 * z ^ 2 / (1 + z) ^ 3)]
    have hfrac : 2 * z ^ 2 / (1 + z) ^ 3 ≤ 1 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 3)]
      nlinarith [show (0 : ℝ) ≤ z ^ 2 * (1 + z) by positivity, hz]
    nlinarith [hquot, hfrac]

end Work.FTS.StrongEps
