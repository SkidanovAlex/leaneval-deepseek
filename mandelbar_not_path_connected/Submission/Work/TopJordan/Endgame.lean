/-
# The mandelbar endgame, with the Jordan curve theorem discharged

`Submission/Work/Top/Main.lean` proves

* `Work.Top.not_isPathConnected_of_twoSidedPinch` and
* `Work.Top.mandelbar_not_isPathConnected_of_twoSidedPinch`

under the explicit hypothesis `hJ : Work.Top.JordanForm` (the Jordan curve theorem), and
`Work.Top.scale_separation` is the per-scale separation lemma they rest on.

Here `hJ` is removed: `Work.TopJordan.jordanForm` (`Submission/Work/TopJordan/Jordan.lean`)
supplies it, so the three statements become unconditional plane-topology + abstract-interface
theorems.  The statements are verbatim those of `Submission/Work/Top`, minus `hJ`.
-/
import Mathlib
import Submission.Work.Top.Main
import Submission.Work.Top.scale_separation
import Submission.Work.TopJordan.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open Classical Filter Set
open scoped Topology

namespace Work.TopJordan

noncomputable section

/-- **Per-scale separation, without the Jordan curve hypothesis.**  This is
`Work.Top.scale_separation` with `Work.Top.JordanForm` discharged. -/
theorem scale_separation {Mb : Set ℂ} {Φ : ℂ → ℂ} (hN : Work.Top.NakaneData Mb Φ)
    {c₀ : ℂ} {Nm : Set ℂ} {a₁ a₂ θ ε : ℝ}
    (hwin : 0 < a₁ - ε ∧ a₁ + ε < θ ∧ θ < a₂ - ε ∧ a₂ + ε < 1)
    (hθ : c₀ ∉ closure (Work.Top.NakaneData.paramRay hN θ))
    (hreal : (1/4 : ℂ) ∈ Mb ∧ (1/4 : ℂ) ∈ closure (Work.Top.NakaneData.paramRay hN 0) ∧
      c₀ ∉ closure (Work.Top.NakaneData.paramRay hN 0))
    (hX : ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
        ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mb ∧ e₂ ∉ Mb ∧
        Work.Top.NakaneData.extAngle Φ e₁ ∈ Set.Ioo (a₁ - ε) (a₁ + ε) ∧
        Work.Top.NakaneData.extAngle Φ e₂ ∈ Set.Ioo (a₂ - ε) (a₂ + ε))
    {p : ℂ} (hp : p ∈ Mb) (hpcl : p ∈ closure (Work.Top.NakaneData.paramRay hN θ))
    (hpq : p ≠ (1/4 : ℂ))
    {γ : C(unitInterval, ℂ)} (hγ0 : γ 0 = p) (hγ1 : γ 1 = (1/4 : ℂ))
    (hγmem : ∀ t, γ t ∈ Mb) {r : ℝ} (hr : 0 < r) (hrp : r < dist p c₀)
    (hrq : r < dist (1/4 : ℂ) c₀) :
    ∃ t, γ t ∈ Nm ∧ dist c₀ (γ t) < r :=
  Work.Top.scale_separation hN jordanForm hwin hθ hreal hX hp hpcl hpq hγ0 hγ1 hγmem hr hrp hrq

/-- **The endgame, without the Jordan curve hypothesis.**  This is
`Work.Top.not_isPathConnected_of_twoSidedPinch` with `Work.Top.JordanForm` discharged. -/
theorem not_isPathConnected_of_twoSidedPinch
    (Mb : Set ℂ) (Φ : ℂ → ℂ) (hN : Work.Top.NakaneData Mb Φ)
    (c₀ : ℂ) (Nm : Set ℂ) (a₁ a₂ θ ε : ℝ)
    (hwin : 0 < a₁ - ε ∧ a₁ + ε < θ ∧ θ < a₂ - ε ∧ a₂ + ε < 1)
    (hθ : c₀ ∉ closure (Work.Top.NakaneData.paramRay hN θ))
    (hq : c₀ ≠ (1 / 4 : ℂ))
    (hreal : (1 / 4 : ℂ) ∈ Mb ∧ (1 / 4 : ℂ) ∈ closure (Work.Top.NakaneData.paramRay hN 0) ∧
      c₀ ∉ closure (Work.Top.NakaneData.paramRay hN 0))
    (hp : ∃ p : ℂ, p ∈ Mb ∧ p ∈ closure (Work.Top.NakaneData.paramRay hN θ) ∧ p ≠ (1 / 4 : ℂ))
    (hLB : ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ Mb) →
      c₀ ∉ closure (Set.range γ ∩ Nm))
    (hX : ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
        ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ Mb ∧ e₂ ∉ Mb ∧
        Work.Top.NakaneData.extAngle Φ e₁ ∈ Set.Ioo (a₁ - ε) (a₁ + ε) ∧
        Work.Top.NakaneData.extAngle Φ e₂ ∈ Set.Ioo (a₂ - ε) (a₂ + ε)) :
    ¬ IsPathConnected Mb :=
  Work.Top.not_isPathConnected_of_twoSidedPinch Mb Φ hN jordanForm c₀ Nm a₁ a₂ θ ε
    hwin hθ hq hreal hp hLB hX

/-- **The endgame at the Mandelbar, without the Jordan curve hypothesis.**  This is
`Work.Top.mandelbar_not_isPathConnected_of_twoSidedPinch` with `Work.Top.JordanForm`
discharged. -/
theorem mandelbar_not_isPathConnected_of_twoSidedPinch
    (Φ : ℂ → ℂ) (hN : Work.Top.NakaneData LeanEval.ComplexAnalysis.Mandelbar Φ)
    (c₀ : ℂ) (Nm : Set ℂ) (a₁ a₂ θ ε : ℝ)
    (hwin : 0 < a₁ - ε ∧ a₁ + ε < θ ∧ θ < a₂ - ε ∧ a₂ + ε < 1)
    (hθ : c₀ ∉ closure (Work.Top.NakaneData.paramRay hN θ))
    (hq : c₀ ≠ (1 / 4 : ℂ))
    (hreal : (1 / 4 : ℂ) ∈ LeanEval.ComplexAnalysis.Mandelbar ∧
      (1 / 4 : ℂ) ∈ closure (Work.Top.NakaneData.paramRay hN 0) ∧
      c₀ ∉ closure (Work.Top.NakaneData.paramRay hN 0))
    (hp : ∃ p : ℂ, p ∈ LeanEval.ComplexAnalysis.Mandelbar ∧
      p ∈ closure (Work.Top.NakaneData.paramRay hN θ) ∧ p ≠ (1 / 4 : ℂ))
    (hLB : ∀ γ : C(unitInterval, ℂ), (∀ t, γ t ∈ LeanEval.ComplexAnalysis.Mandelbar) →
      c₀ ∉ closure (Set.range γ ∩ Nm))
    (hX : ∀ r > 0, ∃ x y : ℂ, segment ℝ x y ⊆ Nm ∩ Metric.ball c₀ r ∧
        ∃ e₁ ∈ segment ℝ x y, ∃ e₂ ∈ segment ℝ x y, e₁ ∉ LeanEval.ComplexAnalysis.Mandelbar ∧
        e₂ ∉ LeanEval.ComplexAnalysis.Mandelbar ∧
        Work.Top.NakaneData.extAngle Φ e₁ ∈ Set.Ioo (a₁ - ε) (a₁ + ε) ∧
        Work.Top.NakaneData.extAngle Φ e₂ ∈ Set.Ioo (a₂ - ε) (a₂ + ε)) :
    ¬ IsPathConnected LeanEval.ComplexAnalysis.Mandelbar :=
  Work.Top.mandelbar_not_isPathConnected_of_twoSidedPinch Φ hN jordanForm c₀ Nm a₁ a₂ θ ε
    hwin hθ hq hreal hp hLB hX

end

end Work.TopJordan
