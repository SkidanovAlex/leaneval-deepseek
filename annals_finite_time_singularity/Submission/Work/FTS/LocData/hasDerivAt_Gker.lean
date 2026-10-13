/-
# `deriv (Gker k) = Gker (k+1)` off the pole `z = -1`

`Work.FTS.LocData.Gker k z = 2·(-1)^k·k!·(z-k)/(1+z)^(k+2)` is the closed form of the `k`-th
plain derivative of the fundamental-model profile `F_* (z) = 2z/(1+z)²`.  This module proves
the expected one-step relation: away from the pole `1 + z = 0`, the next closed form is the
derivative of the previous one.

The proof is the quotient/product rule applied to `(2·(-1)^k·k!·(z-k)) / (1+z)^(k+2)`; the
resulting expression is identified with `Gker (k+1) z` by clearing the denominators
(`field_simp`, using `1 + z ≠ 0`) and the identities `(-1)^(k+1) = -(-1)^k`,
`(k+1)! = (k+1)·k!`, rewritten with `pow_succ` / `Nat.factorial_succ` before `ring`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocData.FstarAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.LocData

set_option autoImplicit false

theorem hasDerivAt_Gker (k : ℕ) (z : ℝ) (hz : 1 + z ≠ 0) :
    HasDerivAt (Work.FTS.LocData.Gker k) (Work.FTS.LocData.Gker (k + 1) z) z := by
  -- derivative of the numerator `2·(-1)^k·k!·(w - k)`
  have hnum : HasDerivAt (fun w : ℝ => 2 * (-1:ℝ)^k * (k.factorial:ℝ) * (w - k))
      (2 * (-1:ℝ)^k * (k.factorial:ℝ)) z := by
    have h : HasDerivAt (fun w : ℝ => w - (k:ℝ)) 1 z := by
      simpa using (hasDerivAt_id z).sub_const (k:ℝ)
    have h2 := h.const_mul (2 * (-1:ℝ)^k * (k.factorial:ℝ))
    simpa using h2
  -- derivative of the denominator `(1 + w)^(k+2)`
  have hden2 : HasDerivAt (fun w : ℝ => (1 + w) ^ (k + 2))
      (((k+2 : ℕ) : ℝ) * (1+z)^(k+1)) z := by
    have h : HasDerivAt (fun w : ℝ => 1 + w) 1 z := by
      simpa using (hasDerivAt_id z).const_add 1
    have h2 := h.pow (k+2)
    rw [show (fun w : ℝ => (1 + w) ^ (k + 2)) = (fun w : ℝ => 1 + w) ^ (k+2) from by
          funext w; simp [Pi.pow_apply]]
    simpa using h2
  have hden : (1+z)^(k+2) ≠ 0 := pow_ne_zero _ hz
  have hdiv := hnum.div hden2 hden
  -- the value produced by the quotient rule is `Gker (k+1) z`
  have hval : (2 * (-1:ℝ)^k * (k.factorial:ℝ) * (1+z)^(k+2)
        - 2 * (-1:ℝ)^k * (k.factorial:ℝ) * (z - k) * (((k+2:ℕ):ℝ) * (1+z)^(k+1)))
        / ((1+z)^(k+2))^2 = Gker (k+1) z := by
    rw [Gker_apply]
    rw [show (k+1)+2 = k+3 by omega]
    -- rewrite every power of `1 + z` through `(1+z)^(k+1)`
    have h1 : (1 + z) ^ (k + 2) = (1 + z) ^ (k + 1) * (1 + z) := by
      rw [show k + 2 = (k+1) + 1 by omega, pow_succ]
    have h2 : (1 + z) ^ (k + 3) = (1 + z) ^ (k + 1) * (1 + z) ^ 2 := by
      rw [show k + 3 = (k+1) + 2 by omega, pow_add]
    have h3 : ((1 + z) ^ (k + 2)) ^ 2 = ((1 + z) ^ (k + 1)) ^ 2 * (1 + z) ^ 2 := by
      rw [h1, mul_pow]
    rw [h3, h1, h2]
    have hu : (1+z)^(k+1) ≠ 0 := pow_ne_zero _ hz
    have ht : (1+z) ≠ 0 := hz
    field_simp
    rw [show (-1:ℝ)^(k+1) = -(-1)^k by rw [pow_succ]; ring]
    rw [show ((k+1).factorial : ℝ) = ((k:ℝ)+1) * (k.factorial:ℝ) by
          rw [Nat.factorial_succ]; push_cast; ring]
    push_cast
    ring
  exact hdiv.congr_deriv hval

end Work.FTS.LocData
