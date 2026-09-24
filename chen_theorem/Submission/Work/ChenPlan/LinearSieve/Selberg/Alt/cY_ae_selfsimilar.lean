import Mathlib
import Submission.Work.ChenPlan.LinearSieve.Selberg.Alt.refsum_law

/-!
# Self-similarity of the reference sum `Y = Σ_{k ≥ 1} e^{-S_k}`

If `S_k = E_0 + ⋯ + E_{k-1}` are the partial sums of an iid standard exponential
sequence, then the reference variable `Y = Σ_{k ≥ 1} e^{-S_k}` satisfies the
distributional self-similarity `Y =_d U (1 + Y)` with `U = e^{-E_0}` uniform on
`(0,1)`.  Pointwise this is exactly the identity

  `Y x = e^{-x 0} (1 + Y (cshift x))`,

an algebraic (telescoping) statement, valid whenever `Σ_k e^{-S_k (x)}` converges.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

theorem cY_ae_selfsimilar (h : ∀ᵐ x ∂canonM, Summable (fun k : ℕ => Real.exp (-(cSum x k)))) :
    (fun x : ℕ → ℝ => cY x) =ᵐ[canonM] fun x => Real.exp (-(x 0)) * (1 + cY (cshift x)) := by
  filter_upwards [h] with x hx
  -- The partial sums of the tail sequence `.1; .2; …`
  have hcs : ∀ k, cSum x (k+1) = x 0 + cSum (cshift x) k := by
    intro k
    simp only [cSum, cshift, Finset.sum_range_succ']
    ring
  -- Head/tail factorisation of the exponential term
  have hgk : ∀ k, Real.exp (-(cSum x (k+1))) =
      Real.exp (-(x 0)) * Real.exp (-(cSum (cshift x) k)) := by
    intro k
    rw [hcs k,
      show -(x 0 + cSum (cshift x) k) = -(x 0) + -(cSum (cshift x) k) by ring,
      Real.exp_add]
  -- Summability of the tail appears by dividing out the (nonzero) head factor
  have hb : Summable (fun k => Real.exp (-(cSum (cshift x) k))) := by
    have htail : Summable (fun k => Real.exp (-(cSum x (k+1)))) :=
      hx.comp_injective Nat.succ_injective
    have h2 : Summable (fun k => Real.exp (-(x 0)) * Real.exp (-(cSum (cshift x) k))) := by
      simpa only [hgk] using htail
    have hc : Real.exp (-(x 0)) ≠ 0 := Real.exp_ne_zero _
    have h3 := h2.mul_left ((Real.exp (-(x 0)))⁻¹)
    simpa only [inv_mul_cancel_left₀ hc] using h3
  have h1 : cY x = Real.exp (-(x 0)) * ∑' k, Real.exp (-(cSum (cshift x) k)) := by
    simp only [cY]
    rw [tsum_congr (fun k => hgk k), tsum_mul_left]
  have h2 : (∑' k, Real.exp (-(cSum (cshift x) k))) = 1 + cY (cshift x) := by
    rw [Summable.tsum_eq_zero_add hb]
    have h0 : Real.exp (-(cSum (cshift x) 0)) = 1 := by simp [cSum]
    rw [h0]
    rfl
  rw [h1, h2]

end Work.ChenPlan.LinearSieve.Selberg.Alt
