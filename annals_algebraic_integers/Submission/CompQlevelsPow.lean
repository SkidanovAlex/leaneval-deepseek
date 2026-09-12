import Submission.CompQNums
import Submission.Bclps

/-!
# The level-power identity for `C2val`

Helper for `Submission/CompQRoots.lean`: `(u_r/2)^D = 8·C2val⁻¹·κ^{D·r}`,
where `u_r = levelStep r = κ^r/(64·D)` and `C2val = 8·(128·D)^D`.
-/

noncomputable section

open scoped Real BigOperators
open Polynomial

namespace Submission.CompQlevelsPow

open Submission.SerreExample
open Submission.ChebSerre
open Submission.AdjustedCheb
open Submission.Bclps
open Submission.DivLinear
open Submission.CompQNums

/-- `(u_r/2)^D = 8·C2val⁻¹·κ^{D·r}`: the level-power lower bound in terms of
`C2val`. -/
theorem level_pow_C2 (r : ℕ) :
    (levelStep r / 2) ^ D = 8 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
  unfold levelStep C2val D
  -- LHS base: `κ^r/(64·D) / 2 = κ^r/(128·D)`.
  have hDne : (Bclps.Dconst : ℝ) ≠ 0 := by
    have hDpos : 0 < Bclps.Dconst := by
      have h := Bclps.Dconst_pos
      omega
    exact_mod_cast (ne_of_gt hDpos)
  have hstep : kappaC ^ r / (64 * (Bclps.Dconst : ℝ)) / 2 =
      kappaC ^ r / (128 * (Bclps.Dconst : ℝ)) := by
    field_simp [hDne]
    ring
  rw [hstep]
  -- `C2val = 8·(128·D)^D`, so `8·C2val⁻¹ = ((128·D)^D)⁻¹`.
  have hy : (128 * (Bclps.Dconst : ℝ)) ^ Bclps.Dconst ≠ 0 := by
    exact pow_ne_zero Bclps.Dconst (by positivity)
  have hfac : 8 * (8 * (128 * (Bclps.Dconst : ℝ)) ^ Bclps.Dconst)⁻¹ =
      ((128 * (Bclps.Dconst : ℝ)) ^ Bclps.Dconst)⁻¹ := by
    field_simp [hy]
  rw [hfac]
  -- `(κ^r/(128·D))^D = κ^(r·D)/(128·D)^D = ((128·D)^D)⁻¹·κ^(D·r)`.
  rw [div_pow]
  rw [← pow_mul]
  field_simp [hy]
  rw [Nat.mul_comm r Bclps.Dconst]

end Submission.CompQlevelsPow
