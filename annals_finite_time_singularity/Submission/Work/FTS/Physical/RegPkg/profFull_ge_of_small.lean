import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.Spaces.c_bounds
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `profFull_ge_of_small` — the full profile is large somewhere

For `0 < α`, `3α ≤ 1` and a perturbation `g` that is uniformly small,
`|g z θ τ| ≤ 3α/200` on `[0,∞) × [0,π/2]`, there is a point `(z,θ)` with `z > 0`,
`θ ∈ [0,π/2]`, `θ < π/2` at which `|F_*(3α) + g| ≥ 3α/100`.

The witness is again `(z,θ) = (1, π/4)`:

* `F_{*,rad}(1) = 2·1/(1+1)² = 1/2` is the maximum of `F_{*,rad}`;
* `Γ(π/4) = (sin(π/4)·cos²(π/4))^α = (√2/4)^α ≥ √2/4 ≥ 3/10` (the base `√2/4` lies in
  `(0,1]` and `α ≤ 1/3 ≤ 1`, so the exponent `α` is *smaller* than `1`);
  note the exponent here is `(3α)/3 = α`, since the profile `F_*(3α)` carries `Γ(3α)`;
* `c(3α) ≤ 10` (`Work.Spaces.c_bounds`), hence `Γ(π/4)/c(3α) ≥ (3/10)/10 = 3/100`.

Therefore `F_*(3α)(1,π/4) ≥ 3α · (3/100) · (1/2) = 9α/200`, so at this point
`F_*(3α)(1,π/4) + g(1,π/4,τ) ≥ 9α/200 - 3α/200 = 3α/100 > 0`, giving the claim.
-/

namespace Work.FTS.Physical.RegPkg

open scoped Real Topology

/-- `Γ(3α)(π/4) = (sin(π/4)·cos²(π/4))^α = (√2/4)^α ≥ √2/4 ≥ 3/10` (the exponent is
`(3α)/3 = α ≤ 1/3 ≤ 1`, and `√2/4 ∈ (0,1]`). -/
private lemma Gam_three_pi_div_four_ge {α : ℝ} (hα1 : 3 * α ≤ 1) :
    (3 : ℝ) / 10 ≤ Work.Spaces.Gam (3 * α) (Real.pi / 4) := by
  have hbase0 : (0 : ℝ) < √2 / 4 := by positivity
  have hbase1 : √2 / 4 ≤ 1 := by
    have h : √2 < 4 := by
      rw [Real.sqrt_lt' (show (0 : ℝ) < 4 by norm_num)]; norm_num
    linarith
  have hsqrt_ge : (3 : ℝ) / 10 ≤ √2 / 4 := by
    have h65 : (6 : ℝ) / 5 ≤ √2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    linarith
  have hsq : (√2 / 2) ^ 2 = (1 : ℝ) / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have hbase : Real.sin (Real.pi / 4) * Real.cos (Real.pi / 4) ^ 2 = √2 / 4 := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four, hsq]; ring
  have hGamEq : Work.Spaces.Gam (3 * α) (Real.pi / 4) = (√2 / 4) ^ α := by
    rw [Work.Spaces.Gam, hbase, show (3 * α) / 3 = α by ring]
  have hmono : (√2 / 4) ^ (1 : ℝ) ≤ (√2 / 4) ^ α :=
    Real.rpow_le_rpow_of_exponent_ge hbase0 hbase1 (by linarith)
  rw [Real.rpow_one] at hmono
  rw [hGamEq]
  linarith

theorem profFull_ge_of_small {α : ℝ} (hα : 0 < α) (hα1 : 3 * α ≤ 1) {g : ℝ → ℝ → ℝ → ℝ}
    (hsmall : ∀ τ : ℝ, 0 ≤ τ → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |g z θ τ| ≤ 3 * α / 200) :
    ∀ τ : ℝ, 0 ≤ τ → ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, θ ∈ Work.Spaces.Iθ ∧ θ < Real.pi / 2 ∧
      3 * α / 100 ≤ |Work.Construction.Fstar (3 * α) z θ + g z θ τ| := by
  intro τ hτ
  have hα3pos : 0 < 3 * α := by linarith
  obtain ⟨_hc1, hc2⟩ := Work.Spaces.c_bounds (3 * α) hα3pos hα1
  have hcpos : 0 < Work.Spaces.c (3 * α) := by
    linarith [(Work.Spaces.c_bounds (3 * α) hα3pos hα1).1]
  have hΓ : (3 : ℝ) / 10 ≤ Work.Spaces.Gam (3 * α) (Real.pi / 4) :=
    Gam_three_pi_div_four_ge hα1
  -- `Γ(π/4)/c(3α) ≥ (3/10)/10 = 3/100`.
  have hratio : (3 : ℝ) / 100 ≤ Work.Spaces.Gam (3 * α) (Real.pi / 4) / Work.Spaces.c (3 * α) := by
    rw [le_div_iff₀ hcpos]
    nlinarith
  have hFhalf : Work.FM.Fstar (1 : ℝ) = 1 / 2 := by
    rw [Work.FM.Fstar]; norm_num
  -- `F_*(3α)(1, π/4) ≥ 3α · (3/100) · (1/2) = 9α/200`.
  have hF : 3 * α * ((3 : ℝ) / 200) ≤ Work.Construction.Fstar (3 * α) 1 (Real.pi / 4) := by
    rw [Work.Construction.Fstar, hFhalf]
    have h1 : (3 * α * ((3 : ℝ) / 100)) * (1 / 2)
        ≤ (3 * α * (Work.Spaces.Gam (3 * α) (Real.pi / 4) / Work.Spaces.c (3 * α))) * (1 / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hα3pos.le) (by norm_num)
    nlinarith [h1]
  have hgpt : -(3 * α / 200) ≤ g 1 (Real.pi / 4) τ := by
    have h := hsmall τ hτ 1 (by simp [Work.Spaces.Iz]) (Real.pi / 4)
      (by constructor <;> linarith [Real.pi_pos])
    rw [abs_le] at h
    linarith [h.1]
  refine ⟨1, one_pos, Real.pi / 4, ?_, ?_, ?_⟩
  · constructor <;> linarith [Real.pi_pos]
  · linarith [Real.pi_pos]
  · have hkey : 3 * α / 100
        ≤ Work.Construction.Fstar (3 * α) 1 (Real.pi / 4) + g 1 (Real.pi / 4) τ := by linarith
    exact le_trans hkey (le_abs_self _)

end Work.FTS.Physical.RegPkg
