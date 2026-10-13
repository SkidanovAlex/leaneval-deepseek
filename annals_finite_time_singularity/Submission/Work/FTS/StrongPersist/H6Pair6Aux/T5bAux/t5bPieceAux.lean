import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Weights: continuity, vanishing at `z = 0`, and the two arithmetic reductions -/

theorem contOn_leafW {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) :
    ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  rcases hleaf with h | h | ⟨-, h⟩
  · subst h
    exact (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 Work.Spaces.eta)).congr
      (fun p _ => rfl)
  · subst h
    exact Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.congr (fun p _ => rfl)
  · subst h
    exact (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
      (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0
        (Work.Spaces.gam α))).congr (fun p _ => rfl)

/-- Every leaf weight vanishes at `z = 0` (its `w²`-factor does). -/
theorem leaf_zero_left {α : ℝ} {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (θ : ℝ) : ρ 0 θ = 0 := by
  rcases hleaf with h | h | ⟨-, h⟩
  · rw [h]; simp [Work.FTS.TransportS.leafEta, Work.Spaces.w]
  · rw [h]; simp [Work.FTS.TransportS.leafOne, Work.Spaces.w]
  · rw [h]; simp [Work.FTS.TransportS.leafGam, Work.Spaces.w]

/-- The piece vanishes at `z = 0`. -/
theorem piece_at_zero {α : ℝ} {f : ℝ → ℝ → ℝ} {a b k i : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hleaf : Work.FTS.TransportS.IsLeafW α a ρ) (θ : ℝ) :
    Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k i (0, θ) = 0 := by
  simp only [Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece, leaf_zero_left hleaf θ, zero_mul]

/-- The weight `w²·sin(2θ)^{-(γ-1)}` is continuous on the open quadrant. -/
theorem contOn_Wgam (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.w p.1) ^ 2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α - 1)))
      Work.FTS.EllipticEst.Q0 :=
  Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_w_sq_Q0.mul
    (Work.FTS.StrongPersist.H6Pair6Aux.continuousOn_sin_rpow_Q0 (Work.Spaces.gam α - 1))

theorem arith_four {X Cc C4 N4 N6 B : ℝ} (hCc : 0 ≤ Cc) (hC4 : 0 ≤ C4)
    (hN4 : 0 ≤ N4) (hN6 : 0 ≤ N6) (hB : 1 ≤ B)
    (hres : X ≤ (Cc * (C4 * N4)) * N6 * N6) :
    X ≤ B * Cc * (C4 * N4 * (N4 * N6 + N6 * N6)) := by
  refine hres.trans ?_
  have hA : 0 ≤ Cc * (C4 * N4) := mul_nonneg hCc (mul_nonneg hC4 hN4)
  have hD : 0 ≤ N4 * N6 + N6 * N6 := by nlinarith
  have h1 : (Cc * (C4 * N4)) * N6 * N6 ≤ (Cc * (C4 * N4)) * (N4 * N6 + N6 * N6) := by
    have h2 : N6 * N6 ≤ N4 * N6 + N6 * N6 := by nlinarith
    calc (Cc * (C4 * N4)) * N6 * N6 = (Cc * (C4 * N4)) * (N6 * N6) := by ring
      _ ≤ (Cc * (C4 * N4)) * (N4 * N6 + N6 * N6) := mul_le_mul_of_nonneg_left h2 hA
  have h3 : (Cc * (C4 * N4)) * (N4 * N6 + N6 * N6)
      ≤ B * Cc * (C4 * N4 * (N4 * N6 + N6 * N6)) := by
    have h4 := mul_le_mul_of_nonneg_right hB (mul_nonneg hA hD)
    calc (Cc * (C4 * N4)) * (N4 * N6 + N6 * N6)
        = 1 * ((Cc * (C4 * N4)) * (N4 * N6 + N6 * N6)) := by ring
      _ ≤ B * ((Cc * (C4 * N4)) * (N4 * N6 + N6 * N6)) := h4
      _ = B * Cc * (C4 * N4 * (N4 * N6 + N6 * N6)) := by ring
  exact h1.trans h3

/-- The arithmetic of the `k ≥ 5` branch: from the level-four Cauchy–Schwarz bound
`|∫∫| ≤ (Cc·C₆|f|₆)·|f|₄·|f|₆` conclude the statement's bound. -/
theorem arith_six {X Cc C6 N4 N6 B : ℝ} (hCc : 0 ≤ Cc) (hC6 : 0 ≤ C6)
    (hN4 : 0 ≤ N4) (hN6 : 0 ≤ N6) (hB : 1 ≤ B)
    (hres : X ≤ Cc * (C6 * N6) * N4 * N6) :
    X ≤ B * Cc * (C6 * N6 * (N4 * N6)) := by
  refine hres.trans ?_
  have hA : 0 ≤ Cc * (C6 * N6) := mul_nonneg hCc (mul_nonneg hC6 hN6)
  have hD : 0 ≤ N4 * N6 := mul_nonneg hN4 hN6
  have h4 := mul_le_mul_of_nonneg_right hB (mul_nonneg hA hD)
  calc Cc * (C6 * N6) * N4 * N6
      = 1 * ((Cc * (C6 * N6)) * (N4 * N6)) := by ring
    _ ≤ B * ((Cc * (C6 * N6)) * (N4 * N6)) := h4
    _ = B * Cc * (C6 * N6 * (N4 * N6)) := by ring

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
