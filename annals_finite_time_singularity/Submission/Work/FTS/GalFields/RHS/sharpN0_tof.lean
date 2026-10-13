/-
Order/association helpers for the final scaling step of the `N₀`-difference estimate
(`Work.FTS.GalFields.RHS.sharp_N0_diff`).

The step which they encapsulate is: from a bound `Xn α U ≤ C * (A * (Ci * B))` (with the
constant package `C * (A * Ci)` and the *order-one* data `B`) conclude the bound
`Xn α U ≤ (C * (A * Ci)) * ((1 + Xn5 α g + Xn5 α g') * B)`, using that `B` is at most
`(1 + …) * B` and only the nonnegativity of the other factors.  The statements are written
so that the *association and the order of the factors are literally those of the goal*, so
that each is discharged by a single application, with no `ring`/`nlinarith` guessing.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.GalFields.RHS

set_option autoImplicit false

/-- `A * X ≤ A * (B * X)` for `A, X ≥ 0` and `1 ≤ B`. -/
theorem tof_mul_left_le_plain {A B X : ℝ} (hA : 0 ≤ A) (hX : 0 ≤ X) (hB : 1 ≤ B) :
    A * X ≤ A * (B * X) := by
  have h1 : X ≤ B * X := by
    have h := mul_le_mul_of_nonneg_right hB hX
    simpa using h
  exact mul_le_mul_of_nonneg_left h1 hA

/-- `C * (A * (Ci * X)) ≤ (C * (A * Ci)) * (B * X)` for nonnegative factors and `1 ≤ B`. -/
theorem tof_mul_left_le' {C A Ci B X : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hCi : 0 ≤ Ci)
    (hX : 0 ≤ X) (hB : 1 ≤ B) :
    C * (A * (Ci * X)) ≤ (C * (A * Ci)) * (B * X) := by
  have h1 : X ≤ B * X := by
    have h := mul_le_mul_of_nonneg_right hB hX
    simpa using h
  calc C * (A * (Ci * X)) ≤ C * (A * (Ci * (B * X))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hCi) hA) hC
    _ = (C * (A * Ci)) * (B * X) := by ring

/-- `C * ((A * (Ci * X)) * Y) ≤ (C * (A * Ci)) * (B * Y)` for `X ≤ B` and `Y ≥ 0`. -/
theorem tof_mul_mix_le {C A Ci B X Y : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hCi : 0 ≤ Ci)
    (hY : 0 ≤ Y) (hB : X ≤ B) :
    C * ((A * (Ci * X)) * Y) ≤ (C * (A * Ci)) * (B * Y) := by
  have h3 : (A * (Ci * X)) * Y ≤ (A * Ci) * (B * Y) := by
    calc (A * (Ci * X)) * Y = (A * Ci) * (X * Y) := by ring
      _ ≤ (A * Ci) * (B * Y) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB hY) (mul_nonneg hA hCi)
  calc C * ((A * (Ci * X)) * Y) ≤ C * ((A * Ci) * (B * Y)) := mul_le_mul_of_nonneg_left h3 hC
    _ = (C * (A * Ci)) * (B * Y) := by ring

/-- `C * ((A * (Ci * X)) * Y) ≤ (C * (A * Ci)) * (B * X)` for `Y ≤ B` and `X ≥ 0`. -/
theorem tof_mul_mix_le' {C A Ci B X Y : ℝ} (hC : 0 ≤ C) (hA : 0 ≤ A) (hCi : 0 ≤ Ci)
    (hX : 0 ≤ X) (hB : Y ≤ B) :
    C * ((A * (Ci * X)) * Y) ≤ (C * (A * Ci)) * (B * X) := by
  have h4 : X * Y ≤ B * X := by
    calc X * Y ≤ X * B := mul_le_mul_of_nonneg_left hB hX
      _ = B * X := by ring
  have h3 : (A * (Ci * X)) * Y ≤ (A * Ci) * (B * X) := by
    calc (A * (Ci * X)) * Y = (A * Ci) * (X * Y) := by ring
      _ ≤ (A * Ci) * (B * X) := mul_le_mul_of_nonneg_left h4 (mul_nonneg hA hCi)
  calc C * ((A * (Ci * X)) * Y) ≤ C * ((A * Ci) * (B * X)) := mul_le_mul_of_nonneg_left h3 hC
    _ = (C * (A * Ci)) * (B * X) := by ring

end Work.FTS.GalFields.RHS
