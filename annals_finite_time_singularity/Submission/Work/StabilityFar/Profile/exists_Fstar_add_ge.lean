import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# A lower bound for `|F_* + g|` on the domain

The paper's far-field/dichotomy argument needs a point `(z,θ) ∈ I_z × I_θ` at which the
reference profile `F_* = α (Γ(θ)/c) F_{*,rad}(z)` is not cancelled by a perturbation `g`
that is uniformly small, `|g| ≤ α/200`.

The witness is `(z,θ) = (1, π/4)`:

* `F_{*,rad}(1) = 2·1/(1+1)² = 1/2` is the maximum of `F_{*,rad}`;
* `Γ(π/4) = (sin(π/4)·cos²(π/4))^{α/3} = (√2/4)^{α/3} ≥ √2/4 ≥ 3/10`
  (the base `√2/4` lies in `(0,1]` and `α/3 ≤ 1`);
* `c(α) ≤ 10` (`Work.Spaces.c_bounds`), hence `Γ(π/4)/c ≥ (3/10)/10 = 3/100`.

Therefore `F_*(1, π/4) ≥ α · (3/100) · (1/2) = 3α/200`, so that at this point
`F_*(1,π/4) + g(1,π/4) ≥ 3α/200 - α/200 = α/100 > 0`, giving the claim.
-/

namespace Work.StabilityFar.Profile

open scoped Real Topology

/-- `Γ(π/4) = (sin(π/4) cos²(π/4))^{α/3} = (√2/4)^{α/3}` and `√2/4 ∈ (0,1]` while `α/3 ≤ 1`
(for `α ≤ 1`), so `Γ(π/4) ≥ √2/4 ≥ 3/10`. -/
private lemma Gam_pi_div_four_ge {α : ℝ} (_hα : 0 < α) (hα1 : α ≤ 1) :
    (3 : ℝ) / 10 ≤ Work.Spaces.Gam α (π / 4) := by
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
  have hbase : Real.sin (π / 4) * Real.cos (π / 4) ^ 2 = √2 / 4 := by
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four, hsq]; ring
  have hGamEq : Work.Spaces.Gam α (π / 4) = (√2 / 4) ^ (α / 3) := by
    rw [Work.Spaces.Gam, hbase]
  have hmono : (√2 / 4) ^ (1 : ℝ) ≤ (√2 / 4) ^ (α / 3) :=
    Real.rpow_le_rpow_of_exponent_ge hbase0 hbase1 (by linarith)
  rw [Real.rpow_one] at hmono
  linarith

theorem exists_Fstar_add_ge {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, |g z θ| ≤ α / 200) :
    ∃ z ∈ Work.Spaces.Iz, ∃ θ ∈ Work.Spaces.Iθ,
      α / 100 ≤ |Work.Construction.Fstar α z θ + g z θ| := by
  obtain ⟨hc1, hc2⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hΓ : (3 : ℝ) / 10 ≤ Work.Spaces.Gam α (π / 4) := Gam_pi_div_four_ge hα hα1
  -- `Γ(π/4)/c ≥ (3/10)/10 = 3/100`.
  have hratio : (3 : ℝ) / 100 ≤ Work.Spaces.Gam α (π / 4) / Work.Spaces.c α := by
    rw [le_div_iff₀ hcpos]
    nlinarith
  have hFhalf : Work.FM.Fstar (1 : ℝ) = 1 / 2 := by
    rw [Work.FM.Fstar]; norm_num
  -- `F_*(1, π/4) ≥ α · (3/100) · (1/2) = 3α/200`.
  have hF : α * ((3 : ℝ) / 200) ≤ Work.Construction.Fstar α 1 (π / 4) := by
    rw [Work.Construction.Fstar, hFhalf]
    have h1 : (α * ((3 : ℝ) / 100)) * (1 / 2)
        ≤ (α * (Work.Spaces.Gam α (π / 4) / Work.Spaces.c α)) * (1 / 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hα.le) (by norm_num)
    nlinarith [h1]
  have hgpt : -α / 200 ≤ g 1 (π / 4) := by
    have h := hg 1 (by simp [Work.Spaces.Iz]) (π / 4)
      (by constructor <;> linarith [Real.pi_pos])
    rw [abs_le] at h
    linarith [h.1]
  refine ⟨1, by simp [Work.Spaces.Iz], π / 4, ?_, ?_⟩
  · constructor <;> linarith [Real.pi_pos]
  · have hkey : α / 100 ≤ Work.Construction.Fstar α 1 (π / 4) + g 1 (π / 4) := by linarith
    exact le_trans hkey (le_abs_self _)

end Work.StabilityFar.Profile
