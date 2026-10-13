/-
# The `ℋ⁴` coercivity, assembled from the base case
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.Coercivity.HkShape
import Submission.Work.Coercivity.H1IP_isHkIP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- **`ℋ⁴` coercivity** (paper Proposition `prop:HkCoercivity` with `k = 4`). -/
theorem exists_H4IP (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14)
    (hIBP : ∀ f : ℝ → ℝ → ℝ, HkAdm α 1 f → IBP f)
    (hHH : ∀ f : ℝ → ℝ → ℝ, HkAdm α 1 f → HardyHyp f)
    (hCD : ∀ f : ℝ → ℝ → ℝ, HkAdm α 1 f → CoerciveData α f)
    (hG : GammaL2Bnd α) (hG2 : GammaPointwiseBnd α)
    (hstep : ∀ (n : ℕ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ), 1 ≤ n →
      IsHkIP α n IP →
      ∃ c₁ c₂ : ℝ, 1 ≤ c₁ ∧ 1 ≤ c₂ ∧ IsHkIP α (n + 1) (HkIPStep c₁ c₂ IP)) :
    ∃ IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ, IsHkIP α 4 IP :=
  H4Coercivity_of_step α (H1IP_isHkIP α hα hα1 hIBP hHH hCD hG hG2) hstep

/-- **`ℋ^k` coercivity** (paper Proposition `prop:HkCoercivity`), every level `k ≥ 1`. -/
theorem exists_HkIP (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) (k : ℕ) (hk : 1 ≤ k)
    (hIBP : ∀ f : ℝ → ℝ → ℝ, HkAdm α 1 f → IBP f)
    (hHH : ∀ f : ℝ → ℝ → ℝ, HkAdm α 1 f → HardyHyp f)
    (hCD : ∀ f : ℝ → ℝ → ℝ, HkAdm α 1 f → CoerciveData α f)
    (hG : GammaL2Bnd α) (hG2 : GammaPointwiseBnd α)
    (hstep : ∀ (n : ℕ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ), 1 ≤ n →
      IsHkIP α n IP →
      ∃ c₁ c₂ : ℝ, 1 ≤ c₁ ∧ 1 ≤ c₂ ∧ IsHkIP α (n + 1) (HkIPStep c₁ c₂ IP)) :
    ∃ IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ, IsHkIP α k IP :=
  HkCoercivity_of_step α (H1IP_isHkIP α hα hα1 hIBP hHH hCD hG hG2) hstep k hk

end Work.Coercivity
