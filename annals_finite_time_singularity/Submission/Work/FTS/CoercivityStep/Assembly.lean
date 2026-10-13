/-
# The `ℋ⁴` (and `ℋ³`) coercivity, assembled from the induction step

This is the deliverable of Node N2: `∃ IP, IsH4IP_fts α IP`, with the coercivity
`c|g|²_{ℋ²} ≤ IP(𝓛_Γ^T g, g)` of the paper's corollary (tex 1545) and the `ℋ³` instance
used for `∂_τ g` in the fake-time estimate (tex 1575–1577).

The induction is the paper's (tex 686–707), run at levels `1, 2, 3, 4`:

    IP₁ = H1IP,  IP₂ = HkIPStep 1 1 IP₁,  IP₃ = HkIPStep 1 1 IP₂,  IP₄ = HkIPStep 1 1 IP₃

with coercivity constants `cc₁, cc₁/4, cc₁/16, cc₁/64` and Cauchy–Schwarz constants
`CC₁, 9CC₁, 81CC₁, 729CC₁`.  The hypotheses are exactly the `StepInputs` packages of the
four levels, namely: the base case at level 1 (from the delivered
`Work.Coercivity.H1IP_isHkIP` upgraded to `IsHkIP_fts`, see `Base/`), the regularity
packages `StepReg α n` and the commutator bounds `CommutBounds α n κₙ` at levels
`2, 3, 4`, and the three balances `CC'√κ' ≤ cc'/2` of the constant bookkeeping.

Nothing here is vacuous: every `StepReg` is a statement about `𝓛_Γ^T` alone (the paper's
smoothing property), every `CommutBounds` is proved in the delivered repository
(`Work.Coercivity.CommutTheta_holds`, `Work.Coercivity.CommutZ_holds`), and the balances
are numeric inequalities between the constants of the concrete inner products.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.HkSq_mono
import Submission.Work.FTS.CoercivityStep.Defs
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.FTS.CoercivityStep.Step
import Submission.Work.FTS.CoercivityStep.Bridge

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep

set_option autoImplicit false

/-- The paper's recursion iterated four times from `H1IP`:
`IP₄ = HkIPStep 1 1 (HkIPStep 1 1 (HkIPStep 1 1 (H1IP α)))`. -/
def IP4 (α : ℝ) : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ :=
  Work.Coercivity.HkIPStep 1 1
    (Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.H1IP α)))

/-- The paper's recursion iterated three times from `H1IP`:
`IP₃ = HkIPStep 1 1 (HkIPStep 1 1 (H1IP α))`. -/
def IP3 (α : ℝ) : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ :=
  Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.HkIPStep 1 1 (Work.Coercivity.H1IP α))

/-- **The `ℋ⁴` coercivity, assembled** (paper Proposition `prop:HkCoercivity` with `k = 4`,
tex 1551).

The four `StepInputs`-style hypotheses are the residual of the chapter, named at each
level: the base case `h1` at level 1 (whose CS constant is `CC₁`), the regularity packages
`hreg₂, hreg₃, hreg₄`, the commutator bounds `hcom₂, hcom₃, hcom₄` and the three
balances. -/
theorem exists_IsH4IP_fts (α : ℝ) (hα : 0 < α)
    {cc₁ CC₁ κ₁ κ₂ κ₃ κ₄ : ℝ}
    (h1 : StepInputs α 1 (Work.Coercivity.H1IP α) cc₁ CC₁ κ₁)
    (hreg₂ : StepReg α 2) (hcom₂ : CommutBounds α 2 κ₂)
    (hbal₂ : 9 * CC₁ * Real.sqrt κ₂ ≤ cc₁ / 8)
    (hreg₃ : StepReg α 3) (hcom₃ : CommutBounds α 3 κ₃)
    (hbal₃ : 9 * (9 * CC₁) * Real.sqrt κ₃ ≤ (cc₁ / 4) / 8)
    (hreg₄ : StepReg α 4) (hcom₄ : CommutBounds α 4 κ₄)
    (hbal₄ : 9 * (9 * (9 * CC₁)) * Real.sqrt κ₄ ≤ (cc₁ / 4 / 4) / 8) :
    ∃ IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ, IsH4IP_fts α IP := by
  have h2 := HkIPStep_isHkIP_fts α hα 1 (by norm_num) h1 hcom₂ hreg₂ hbal₂
  have h3 := HkIPStep_isHkIP_fts α hα 2 (by norm_num) h2 hcom₃ hreg₃ hbal₃
  have h4 := HkIPStep_isHkIP_fts α hα 3 (by norm_num) h3 hcom₄ hreg₄ hbal₄
  exact ⟨_, ⟨h4.2.2.1.prop⟩⟩

/-- **The `ℋ⁴` coercivity with the named coercivity constant `cc₁/64`.**  This is the form
in which the a-priori estimate of §Modulation consumes it. -/
theorem exists_IsH4IPc_fts (α : ℝ) (hα : 0 < α)
    {cc₁ CC₁ κ₁ κ₂ κ₃ κ₄ : ℝ}
    (h1 : StepInputs α 1 (Work.Coercivity.H1IP α) cc₁ CC₁ κ₁)
    (hreg₂ : StepReg α 2) (hcom₂ : CommutBounds α 2 κ₂)
    (hbal₂ : 9 * CC₁ * Real.sqrt κ₂ ≤ cc₁ / 8)
    (hreg₃ : StepReg α 3) (hcom₃ : CommutBounds α 3 κ₃)
    (hbal₃ : 9 * (9 * CC₁) * Real.sqrt κ₃ ≤ (cc₁ / 4) / 8)
    (hreg₄ : StepReg α 4) (hcom₄ : CommutBounds α 4 κ₄)
    (hbal₄ : 9 * (9 * (9 * CC₁)) * Real.sqrt κ₄ ≤ (cc₁ / 4 / 4) / 8) :
    IsHkIPc_fts α 4 (IP4 α) (cc₁ / 64) ∧ IsHkIPc_fts α 3 (IP3 α) (cc₁ / 16) := by
  have h2 := HkIPStep_isHkIP_fts α hα 1 (by norm_num) h1 hcom₂ hreg₂ hbal₂
  have h3 := HkIPStep_isHkIP_fts α hα 2 (by norm_num) h2 hcom₃ hreg₃ hbal₃
  have h4 := HkIPStep_isHkIP_fts α hα 3 (by norm_num) h3 hcom₄ hreg₄ hbal₄
  have h4c : cc₁ / 4 / 4 / 4 = cc₁ / 64 := by ring
  have h3c : cc₁ / 4 / 4 = cc₁ / 16 := by ring
  exact ⟨h4c ▸ h4.2.2.1, h3c ▸ h3.2.2.1⟩

/-- **The coercivity in the paper's corollary form** (tex 1545):
`c|g|²_{ℋ²} ≤ (𝓛_Γ^T g, g)_{ℋ⁴}`.  The `ℋ²` (rather than `ℋ⁴`) norm on the left is the
paper's display; the `ℋ⁴` version follows from the same clause. -/
theorem level4_coercive_fts (α : ℝ) (hα : 0 < α)
    {cc₁ CC₁ κ₁ κ₂ κ₃ κ₄ : ℝ}
    (h1 : StepInputs α 1 (Work.Coercivity.H1IP α) cc₁ CC₁ κ₁)
    (hreg₂ : StepReg α 2) (hcom₂ : CommutBounds α 2 κ₂)
    (hbal₂ : 9 * CC₁ * Real.sqrt κ₂ ≤ cc₁ / 8)
    (hreg₃ : StepReg α 3) (hcom₃ : CommutBounds α 3 κ₃)
    (hbal₃ : 9 * (9 * CC₁) * Real.sqrt κ₃ ≤ (cc₁ / 4) / 8)
    (hreg₄ : StepReg α 4) (hcom₄ : CommutBounds α 4 κ₄)
    (hbal₄ : 9 * (9 * (9 * CC₁)) * Real.sqrt κ₄ ≤ (cc₁ / 4 / 4) / 8) :
    ∃ IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ,
      (∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α 4 f →
        (cc₁ / 64) * Work.Spaces.HkSq α 4 f ≤ IP (Work.Coercivity.LGammaT α f) f) ∧
      (∀ f : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α 4 f →
        (cc₁ / 64) * Work.Spaces.HkSq α 2 f ≤ IP (Work.Coercivity.LGammaT α f) f) := by
  obtain ⟨h4, _⟩ := exists_IsH4IPc_fts α hα h1 hreg₂ hcom₂ hbal₂ hreg₃ hcom₃ hbal₃
    hreg₄ hcom₄ hbal₄
  refine ⟨IP4 α, h4.coercive, ?_⟩
  intro f hf
  have hmem : Work.Spaces.HkMem α 4 f := by simpa using hf.2.1 0 0 (by omega)
  have hmono : Work.Spaces.HkSq α 2 f ≤ Work.Spaces.HkSq α 4 f :=
    Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hmem
  exact le_trans (mul_le_mul_of_nonneg_left hmono (by linarith [h4.hc])) (h4.coercive f hf)

/-- **The `ℋ³` instance, for the fake-time equation** (tex 1575–1577).  The paper
differentiates the fake-time equation in `τ` and pairs the result with `∂_τ g` in the
`ℋ³` inner product; this is the coercivity of `𝓛_Γ^T` on that inner product, with the
named constant `cc₁/16`.  Applying it to `w = ∂_τ g` gives the differential inequality
`d/dτ |∂_τ g|_{ℋ³} ≤ -c|∂_τ g|_{ℋ³} + (nonlinear)`. -/
theorem level3_dtau_coercive_fts (α : ℝ) (hα : 0 < α)
    {cc₁ CC₁ κ₁ κ₂ κ₃ κ₄ : ℝ}
    (h1 : StepInputs α 1 (Work.Coercivity.H1IP α) cc₁ CC₁ κ₁)
    (hreg₂ : StepReg α 2) (hcom₂ : CommutBounds α 2 κ₂)
    (hbal₂ : 9 * CC₁ * Real.sqrt κ₂ ≤ cc₁ / 8)
    (hreg₃ : StepReg α 3) (hcom₃ : CommutBounds α 3 κ₃)
    (hbal₃ : 9 * (9 * CC₁) * Real.sqrt κ₃ ≤ (cc₁ / 4) / 8) :
    ∃ IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ,
      ∀ w : ℝ → ℝ → ℝ, Work.Coercivity.HkAdm α 3 w →
        (cc₁ / 16) * Work.Spaces.HkSq α 3 w ≤ IP (Work.Coercivity.LGammaT α w) w := by
  have h2 := HkIPStep_isHkIP_fts α hα 1 (by norm_num) h1 hcom₂ hreg₂ hbal₂
  have h3 := HkIPStep_isHkIP_fts α hα 2 (by norm_num) h2 hcom₃ hreg₃ hbal₃
  have h3c : cc₁ / 4 / 4 = cc₁ / 16 := by ring
  exact ⟨IP3 α, h3c ▸ h3.2.2.1.coercive⟩

/-- **The `ℋ⁴` coercivity in the *delivered* vocabulary**: `∃ IP, Work.Coercivity.IsHkIP α 4 IP`.
This is the form required by `Work.Coercivity.H4Assembly.exists_H4IP` and by every
consumer of the delivered Coercivity area. -/
theorem exists_old_HkIP4_fts (α : ℝ) (hα : 0 < α)
    {cc₁ CC₁ κ₁ κ₂ κ₃ κ₄ : ℝ}
    (h1 : StepInputs α 1 (Work.Coercivity.H1IP α) cc₁ CC₁ κ₁)
    (hreg₂ : StepReg α 2) (hcom₂ : CommutBounds α 2 κ₂)
    (hbal₂ : 9 * CC₁ * Real.sqrt κ₂ ≤ cc₁ / 8)
    (hreg₃ : StepReg α 3) (hcom₃ : CommutBounds α 3 κ₃)
    (hbal₃ : 9 * (9 * CC₁) * Real.sqrt κ₃ ≤ (cc₁ / 4) / 8)
    (hreg₄ : StepReg α 4) (hcom₄ : CommutBounds α 4 κ₄)
    (hbal₄ : 9 * (9 * (9 * CC₁)) * Real.sqrt κ₄ ≤ (cc₁ / 4 / 4) / 8) :
    ∃ IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ, Work.Coercivity.IsHkIP α 4 IP := by
  obtain ⟨IP, hIP⟩ := exists_IsH4IP_fts α hα h1 hreg₂ hcom₂ hbal₂ hreg₃ hcom₃ hbal₃
    hreg₄ hcom₄ hbal₄
  exact ⟨IP, hIP.to_old⟩

end Work.FTS.CoercivityStep
