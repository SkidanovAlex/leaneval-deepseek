/-
# The `ℋ^k` coercivity shape (paper Proposition `prop:HkCoercivity`)

The paper's §"Higher order derivatives and the inner product on `ℋ^k`" proves, by
induction on `k`, that there is an inner product on `ℋ^k` which is comparable to the
`ℋ^k` norm and on which `𝓛_Γ^T` is coercive (`IsHkIP`).  This file states the induction
in the form in which the construction/bootstrap consumes it and proves the *purely
combinatorial* part (the iteration), leaving the two analytic inputs precisely named:

* `hbase : IsHkIP α 1 (H1IP α)` — the base case, which is Corollary
  `FirstDerivativeCoercivity` of the paper assembled from the three coercivity
  propositions of this area (`L2Coercivity`, the `D_θ` and `D_z` propositions);
* `hstep` — the paper's induction step, which is `HkIPStep_isHkIP`: from an admissible
  inner product on `ℋ^n` (`n ≥ 1`) and the commutator estimates `CommutTheta α n`,
  `CommutZ α n` (the paper's `E₁`, `E₂` bounds `|E₁|_{ℋ^n} ≤ C̄|f|_{ℋ^n}`,
  `|E₂|_{ℋ^n} ≤ C̄(|f|_{ℋ^n} + |D_θf|_{ℋ^n})`) one produces an admissible inner product on
  `ℋ^{n+1}`.

`H4Coercivity_of_step` is the `k = 4` instance, which is what the a-priori estimate of
§Modulation needs (`Work.Construction.IsH4IP`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.Coercivity.Basic

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

/-- **The `ℋ^k` coercivity (paper Proposition `prop:HkCoercivity`), as an induction.**
Given the base case on `ℋ¹` and the paper's induction step, there is an admissible inner
product on `ℋ^k` for every `k ≥ 1`. -/
theorem HkCoercivity_of_step (α : ℝ)
    (hbase : IsHkIP α 1 (H1IP α))
    (hstep : ∀ (n : ℕ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ), 1 ≤ n → IsHkIP α n IP →
      ∃ c₁ c₂ : ℝ, 1 ≤ c₁ ∧ 1 ≤ c₂ ∧ IsHkIP α (n + 1) (HkIPStep c₁ c₂ IP)) :
    ∀ k : ℕ, 1 ≤ k → ∃ IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ, IsHkIP α k IP := by
  intro k
  induction k with
  | zero => intro hk; exact absurd hk (by norm_num)
  | succ m ih =>
    intro _
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; exact ⟨H1IP α, hbase⟩
    · obtain ⟨IP, hIP⟩ := ih hm
      obtain ⟨c₁, c₂, hc₁, hc₂, hIP'⟩ := hstep m IP hm hIP
      exact ⟨HkIPStep c₁ c₂ IP, hIP'⟩

/-- **The `ℋ⁴` coercivity** (`prop:HkCoercivity` with `k = 4`), the shape consumed by the
a-priori estimate of §Modulation. -/
theorem H4Coercivity_of_step (α : ℝ)
    (hbase : IsHkIP α 1 (H1IP α))
    (hstep : ∀ (n : ℕ) (IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ), 1 ≤ n → IsHkIP α n IP →
      ∃ c₁ c₂ : ℝ, 1 ≤ c₁ ∧ 1 ≤ c₂ ∧ IsHkIP α (n + 1) (HkIPStep c₁ c₂ IP)) :
    ∃ IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ, IsHkIP α 4 IP :=
  HkCoercivity_of_step α hbase hstep 4 (by norm_num)

/-- The coercivity clause of `IsHkIP`, unpacked for a caller. -/
theorem IsHkIP.coercive {α : ℝ} {k : ℕ} {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsHkIP α k IP) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℝ → ℝ, HkAdm α k f →
      c * Spaces.HkSq α k f ≤ IP (LGammaT α f) f :=
  h.2.2.2.2.2

/-- The comparison clause of `IsHkIP`, unpacked for a caller. -/
theorem IsHkIP.le_self {α : ℝ} {k : ℕ} {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsHkIP α k IP) {f : ℝ → ℝ → ℝ} (ha : HkAdm α k f) : Spaces.HkSq α k f ≤ IP f f :=
  h.2.2.2.1 f ha

/-- The nonnegativity clause of `IsHkIP`, unpacked for a caller. -/
theorem IsHkIP.nonneg {α : ℝ} {k : ℕ} {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsHkIP α k IP) (u : ℝ → ℝ → ℝ) : 0 ≤ IP u u :=
  h.2.2.1 u

/-- The additivity clause of `IsHkIP`, unpacked for a caller. -/
theorem IsHkIP.add {α : ℝ} {k : ℕ} {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ}
    (h : IsHkIP α k IP) (f₁ f₂ g : ℝ → ℝ → ℝ)
    (hs₁ : Spaces.SmoothNbhd f₁) (hs₂ : Spaces.SmoothNbhd f₂) (hsg : Spaces.SmoothNbhd g)
    (h₁ : Spaces.HkMem α k f₁) (h₂ : Spaces.HkMem α k f₂) (hg : Spaces.HkMem α k g) :
    IP (f₁ + f₂) g = IP f₁ g + IP f₂ g :=
  h.1 f₁ f₂ g hs₁ hs₂ hsg h₁ h₂ hg

end Work.Coercivity
