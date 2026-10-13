import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.Gam_bounds
import Submission.Work.Spaces.c_bounds
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Pointwise and derivative bounds for the profile `AK`

`AK α z θ = (Γ(θ)/c(α)) · 2z²/(1+z)³` (tex 1357 of Elgindi's paper): the profile
whose `L₁₂`-evaluations supply the modulation constants.  Everything here rests on
the two coarse numerical facts about the angular data, both already available in the
workspace:

* `Γ(θ) = (sin θ cos²θ)^{α/3} ∈ [0,1]` on `Iθ = [0,π/2]` (`Work.Spaces.Gam_bounds`),
* `1/10 ≤ c(α) ≤ 10` (`Work.Spaces.c_bounds`).

Hence `|Γ(θ)/c(α)| ≤ 10` on `Iθ`; the radial factor `2z²/(1+z)³` is `≤ 2z²`, and its
`z`-derivative is `2(2z-z²)/(1+z)⁴`, which is bounded by `1` on `z ≥ 0`
(`(1+z)⁴ - (4z+2z²) = 1 + z²(2+z)² ≥ 0`).  Both statements then follow with room to
spare.
-/

namespace Work.FTS_RegExport.RXR1.HJ

/-- The angular factor of `AK` is bounded by `10`: `Γ ∈ [0,1]` and `c(α) ≥ 1/10`. -/
theorem gam_div_c_abs_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 := by
  obtain ⟨hG0, hG1⟩ := Work.Spaces.Gam_bounds α θ hα hθ
  obtain ⟨hc1, _⟩ := Work.Spaces.c_bounds α hα hα1
  have hcpos : 0 < Work.Spaces.c α := by linarith
  have hnonneg : 0 ≤ Work.Spaces.Gam α θ / Work.Spaces.c α :=
    div_nonneg hG0 (le_of_lt hcpos)
  rw [abs_of_nonneg hnonneg, div_le_iff₀ hcpos]
  nlinarith

/-- The `z`-derivative of the radial factor `2z²/(1+z)³` of `AK`. -/
theorem hasDerivAt_akFactor {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3)
      (2 * (2 * z - z ^ 2) / (1 + z) ^ 4) z := by
  have hnum : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2) (4 * z) z := by
    have hp : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
      simpa using (hasDerivAt_pow 2 z)
    have h2 := hp.const_mul (2 : ℝ)
    convert h2 using 1
    ring
  have hden : HasDerivAt (fun z' : ℝ => (1 + z') ^ 3) (3 * (1 + z) ^ 2) z := by
    have h1 : HasDerivAt (fun z' : ℝ => 1 + z') (1 : ℝ) z := by
      simpa using (hasDerivAt_id z).const_add (1 : ℝ)
    have h2 := (hasDerivAt_pow 3 (1 + z)).comp z h1
    have h3 : ((fun x : ℝ => x ^ 3) ∘ (fun z' : ℝ => 1 + z'))
        = fun z' : ℝ => (1 + z') ^ 3 := rfl
    rw [h3] at h2
    convert h2 using 1
    ring
  have hne : (1 + z) ^ 3 ≠ 0 := by positivity
  have hdiv := hnum.div hden hne
  convert hdiv using 1
  field_simp
  ring

/-- Numerical bound `|2(2z-z²)| ≤ (1+z)⁴` for `z ≥ 0`, i.e. `4z+2z² ≤ (1+z)⁴`. -/
theorem abs_two_mul_two_z_le {z : ℝ} (hz : 0 ≤ z) :
    |2 * (2 * z - z ^ 2)| ≤ (1 + z) ^ 4 := by
  have h1 : |2 * z - z ^ 2| ≤ 2 * z + z ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg z]
  have h2 : 4 * z + 2 * z ^ 2 ≤ (1 + z) ^ 4 := by
    have e : (1 + z) ^ 4 - (4 * z + 2 * z ^ 2) = 1 + z ^ 2 * (2 + z) ^ 2 := by ring
    nlinarith [sq_nonneg (z * (2 + z)), sq_nonneg z, e]
  have h3 : |2 * (2 * z - z ^ 2)| = 2 * |2 * z - z ^ 2| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h3]
  linarith

theorem AKBounds {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    (∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → |Work.Construction.AK α z θ| ≤ 20 * z ^ 2) ∧
    (∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
      ∃ d : ℝ, HasDerivAt (fun z' : ℝ => Work.Construction.AK α z' θ) d z ∧ |d| ≤ 10) := by
  constructor
  · intro θ hθ z hz
    have hGc := gam_div_c_abs_le hα hα1 hθ
    have hden : (0 : ℝ) < (1 + z) ^ 3 := by positivity
    have hden1 : (1 : ℝ) ≤ (1 + z) ^ 3 := by nlinarith [sq_nonneg z, sq_nonneg (1 + z)]
    have hkey : |2 * z ^ 2 / (1 + z) ^ 3| = 2 * z ^ 2 / (1 + z) ^ 3 := by
      rw [abs_of_nonneg (by positivity)]
    rw [Work.Construction.AK, abs_mul, hkey]
    have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| * (2 * z ^ 2 / (1 + z) ^ 3)
        ≤ 10 * (2 * z ^ 2 / (1 + z) ^ 3) :=
      mul_le_mul_of_nonneg_right hGc (by positivity)
    have h2 : 10 * (2 * z ^ 2 / (1 + z) ^ 3) ≤ 10 * (2 * z ^ 2) := by
      have : 2 * z ^ 2 / (1 + z) ^ 3 ≤ 2 * z ^ 2 := by
        rw [div_le_iff₀ hden]
        nlinarith
      linarith
    linarith
  · intro θ hθ z hz
    have hGc := gam_div_c_abs_le hα hα1 hθ
    have hg := hasDerivAt_akFactor hz
    refine ⟨(Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * (2 * z - z ^ 2) / (1 + z) ^ 4),
      ?_, ?_⟩
    · have h := hg.const_mul (Work.Spaces.Gam α θ / Work.Spaces.c α)
      simpa only [Work.Construction.AK] using h
    · have hden : (0 : ℝ) < (1 + z) ^ 4 := by positivity
      have hkey := abs_two_mul_two_z_le (le_of_lt hz)
      rw [abs_mul]
      have h4 : |2 * (2 * z - z ^ 2) / (1 + z) ^ 4|
          = |2 * (2 * z - z ^ 2)| / (1 + z) ^ 4 := by
        rw [abs_div, abs_of_pos hden]
      rw [h4]
      have h5 : |Work.Spaces.Gam α θ / Work.Spaces.c α|
            * (|2 * (2 * z - z ^ 2)| / (1 + z) ^ 4) ≤ 10 * 1 := by
        have h6 : |2 * (2 * z - z ^ 2)| / (1 + z) ^ 4 ≤ 1 := by
          rw [div_le_one hden]
          exact hkey
        have h7 : 0 ≤ |2 * (2 * z - z ^ 2)| / (1 + z) ^ 4 := by positivity
        nlinarith
      linarith

end Work.FTS_RegExport.RXR1.HJ
