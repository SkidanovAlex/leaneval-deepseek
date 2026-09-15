import ChallengeDeps
import Submission.FUP.Metric
import Submission.FUP.Porosity
import Submission.FUP.Cubes

open FractalUncertainty
open MeasureTheory FourierTransform Metric
open scoped ENNReal

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

lemma addSet_subset_of_subset_right {A C D : Set ℝᵈ} (hCD : C ⊆ D) :
    addSet A C ⊆ addSet A D := by
  intro z hz
  rcases hz with ⟨a, ha, c, hc, rfl⟩
  exact ⟨a, ha, c, hCD hc, rfl⟩

/-- §6.2 of Cohen's paper: for `h < s < 1`, if `Y` is `ν`-porous on lines from `1` to `h⁻¹`,
then `s·Y + [-4,4]^d + η` is `ν/2`-porous on lines from scale `10√d/ν` up to `h⁻¹·s`. -/
lemma sY_cube_eta_porous {ν h s : ℝ} {Y : Set ℝᵈ} (η : ℝᵈ)
    (hd : 0 < d) (hν : 0 < ν) (hs0 : 0 < s) (hslo : s ≤ 8 * Real.sqrt (d : ℝ) / ν)
    (hY : PorousOnLines ν 1 h⁻¹ Y) :
    PorousOnLines (ν / 2) (10 * Real.sqrt (d : ℝ) / ν) (s * h⁻¹)
      ((fun z : ℝᵈ => η + z) '' (addSet ((fun y : ℝᵈ => s • y) '' Y) (cube (-4) 4))) := by
  have hν2 : 0 < ν / 2 := by positivity
  have hν2lt : ν / 2 < ν := by nlinarith [hν]
  have hYscaled : PorousOnLines ν s (s * h⁻¹) ((fun y : ℝᵈ => s • y) '' Y) := by
    simpa using PorousOnLines_smul hs0 hY
  -- add the ball of radius 4√d around the dilated set: porous from 8√d/ν
  have hden : ν - ν / 2 = ν / 2 := by ring
  have hfour : (4 * Real.sqrt (d : ℝ)) / (ν / 2) = 8 * Real.sqrt (d : ℝ) / ν := by
    field_simp [ne_of_gt hν]
    ring
  have hlo : s ≤ (4 * Real.sqrt (d : ℝ)) / (ν - ν / 2) := by
    rw [hden, hfour]
    exact hslo
  have hZ2 : PorousOnLines (ν / 2) ((4 * Real.sqrt (d : ℝ)) / (ν - ν / 2)) (s * h⁻¹)
      (addSet ((fun y : ℝᵈ => s • y) '' Y) (closedBall 0 (4 * Real.sqrt (d : ℝ)))) := by
    exact PorousOnLines_add_ball hν2 hν2lt hlo hYscaled
  -- replace the ball by the cube [-4,4]^d (contained in the ball)
  have hcube : (cube (-4) 4 : Set ℝᵈ) ⊆ closedBall 0 (4 * Real.sqrt (d : ℝ)) :=
    cube_four_subset_closedBall
  have hZ3 : PorousOnLines (ν / 2) ((4 * Real.sqrt (d : ℝ)) / (ν - ν / 2)) (s * h⁻¹)
      (addSet ((fun y : ℝᵈ => s • y) '' Y) (cube (-4) 4)) := by
    exact PorousOnLines.mono_set hZ2 (addSet_subset_of_subset_right hcube)
  -- enlarge the lower scale to 10√d/ν
  have hmono₀ : (4 * Real.sqrt (d : ℝ)) / (ν - ν / 2) ≤ 10 * Real.sqrt (d : ℝ) / ν := by
    rw [hden, hfour]
    exact div_le_div_of_nonneg_right (by nlinarith [Real.sqrt_nonneg (d : ℝ)]) (le_of_lt hν)
  have hsqrpos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have hmono₀pos : 0 < 10 * Real.sqrt (d : ℝ) / ν :=
    div_pos (mul_pos (by norm_num) hsqrpos) hν
  have hZ4 : PorousOnLines (ν / 2) (10 * Real.sqrt (d : ℝ) / ν) (s * h⁻¹)
      (addSet ((fun y : ℝᵈ => s • y) '' Y) (cube (-4) 4)) := by
    exact PorousOnLines.mono hZ3 (le_of_eq (by ring : ν / 2 = ν / 2)) hmono₀ le_rfl hmono₀pos
  -- translate by η
  exact PorousOnLines_add_const η hZ4

end Submission.FUP
