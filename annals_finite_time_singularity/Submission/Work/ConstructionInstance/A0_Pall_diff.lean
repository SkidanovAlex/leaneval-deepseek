/-
# `Pall` is `3·ρ²`-Lipschitz

`Pall x = |x₂| · r(x)²` is the homogeneous-degree-3 profile of `AuxOmegaStar` (`A0 β` is built from
`(Pall x)^β`).  Since the eigenvalue bound for `A0` needs a *local* Lipschitz constant in terms of
`ρ = ‖·‖`, we record here the elementary estimate

  `|Pall x - Pall y| ≤ 3 · (max (ρ x) (ρ y))² · ‖x - y‖`,

which is sharp in the constant `3 = 2 + 1` from the splitting
`Pall x - Pall y = |x₂|·(r(x)² - r(y)²) + r(y)²·(|x₂| - |y₂|)`:
the factor `r²` is `2M`-Lipschitz on the ball of radius `M = max (ρ x) (ρ y)`
(`|r(x)²-r(y)²| = |r(x)-r(y)|·(r(x)+r(y))`, and `r` is `1`-Lipschitz while `r ≤ ρ`), the factor
`|x₂|` is `1`-Lipschitz, and both are bounded by `M`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.AuxOmegaStar

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- The axial coordinate is `1`-Lipschitz: `|x₂ - y₂| ≤ ‖x - y‖`. -/
private lemma abs_axial_sub_le_norm (x y : R3) : |x 2 - y 2| ≤ ‖x - y‖ := by
  have h := PiLp.norm_apply_le (x - y) (2 : Fin 3)
  simpa using h

/-- The absolute value of the axial coordinate is `1`-Lipschitz. -/
private lemma abs_abs_axial_sub_le_norm (x y : R3) : |(|x 2| - |y 2|)| ≤ ‖x - y‖ :=
  le_trans (abs_abs_sub_abs_le_abs_sub _ _) (abs_axial_sub_le_norm x y)

/-- The squared radial coordinate is `2M`-Lipschitz with `M = max (ρ x) (ρ y)`. -/
private lemma abs_radial_sq_sub_le (x y : R3) :
    |Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2|
      ≤ 2 * max (Work.Cyl.rho x) (Work.Cyl.rho y) * ‖x - y‖ := by
  have hsub : |Work.Cyl.radial x - Work.Cyl.radial y| ≤ ‖x - y‖ := radial_dist_le x y
  have hsum : Work.Cyl.radial x + Work.Cyl.radial y
      ≤ 2 * max (Work.Cyl.rho x) (Work.Cyl.rho y) := by
    have h1 : Work.Cyl.radial x + Work.Cyl.radial y ≤ Work.Cyl.rho x + Work.Cyl.rho y :=
      add_le_add (Work.Cyl.radial_le_rho x) (Work.Cyl.radial_le_rho y)
    have h2 : Work.Cyl.rho x ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_left _ _
    have h3 : Work.Cyl.rho y ≤ max (Work.Cyl.rho x) (Work.Cyl.rho y) := le_max_right _ _
    linarith
  have hsum0 : 0 ≤ Work.Cyl.radial x + Work.Cyl.radial y := by
    have := Work.Cyl.radial_nonneg x; have := Work.Cyl.radial_nonneg y; linarith
  calc |Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2|
      = |(Work.Cyl.radial x - Work.Cyl.radial y) * (Work.Cyl.radial x + Work.Cyl.radial y)| := by
        congr 1; ring
    _ = |Work.Cyl.radial x - Work.Cyl.radial y| * (Work.Cyl.radial x + Work.Cyl.radial y) := by
        rw [abs_mul, abs_of_nonneg hsum0]
    _ ≤ ‖x - y‖ * (2 * max (Work.Cyl.rho x) (Work.Cyl.rho y)) :=
        mul_le_mul hsub hsum hsum0 (norm_nonneg _)
    _ = 2 * max (Work.Cyl.rho x) (Work.Cyl.rho y) * ‖x - y‖ := by ring

/-- **`Pall` is locally `3ρ²`-Lipschitz**: with `M = max (ρ x) (ρ y)`,
`|Pall x - Pall y| ≤ 3 M² ‖x - y‖`. -/
lemma A0_Pall_diff (x y : Work.ConstructionInstance.R3) :
    |Work.ConstructionInstance.Pall x - Work.ConstructionInstance.Pall y|
      ≤ 3 * (max (Work.Cyl.rho x) (Work.Cyl.rho y)) ^ 2 * ‖x - y‖ := by
  set M := max (Work.Cyl.rho x) (Work.Cyl.rho y) with hMdef
  have hMx : Work.Cyl.rho x ≤ M := le_max_left _ _
  have hMy : Work.Cyl.rho y ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := le_trans (Work.Cyl.rho_nonneg x) hMx
  have hax : |x 2| ≤ M := le_trans (Work.Cyl.abs_axial_le_rho x) hMx
  have hry : Work.Cyl.radial y ≤ M := le_trans (Work.Cyl.radial_le_rho y) hMy
  have hA : |Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2| ≤ 2 * M * ‖x - y‖ := by
    have h := abs_radial_sq_sub_le x y
    rw [← hMdef] at h
    linarith [h]
  have hB : |(|x 2| - |y 2|)| ≤ ‖x - y‖ := abs_abs_axial_sub_le_norm x y
  have hsplit : Pall x - Pall y
      = |x 2| * (Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2)
        + Work.Cyl.radial y ^ 2 * (|x 2| - |y 2|) := by
    simp only [Pall]; ring
  calc |Pall x - Pall y|
      = |(|x 2| * (Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2)
          + Work.Cyl.radial y ^ 2 * (|x 2| - |y 2|))| := by rw [hsplit]
    _ ≤ |(|x 2| * (Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2))|
          + |(Work.Cyl.radial y ^ 2 * (|x 2| - |y 2|))| := abs_add_le _ _
    _ = |x 2| * |Work.Cyl.radial x ^ 2 - Work.Cyl.radial y ^ 2|
          + Work.Cyl.radial y ^ 2 * |(|x 2| - |y 2|)| := by
        rw [abs_mul, abs_mul, abs_abs, abs_of_nonneg (sq_nonneg (Work.Cyl.radial y))]
    _ ≤ M * (2 * M * ‖x - y‖) + M ^ 2 * ‖x - y‖ := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul hax hA (abs_nonneg _) hM0
        · exact mul_le_mul (by nlinarith [hry, Work.Cyl.radial_nonneg y]) hB (abs_nonneg _)
            (by positivity)
    _ = 3 * M ^ 2 * ‖x - y‖ := by ring

end Work.ConstructionInstance
