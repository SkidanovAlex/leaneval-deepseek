/-
# Four arcs glued into a Jordan curve

Four continuous arcs `γ₁ γ₂ γ₃ γ₄` in the plane which close up into a loop — consecutive ones
meeting exactly in their common endpoint and all other pairs being disjoint — have as their
union a Jordan curve, i.e. the image of a continuous injective map of the circle.

The proof exhibits the parametrisation explicitly.  The map

`fourArcs γ₁ γ₂ γ₃ γ₄ : ℝ → ℂ`

(see `Submission/Work/Top/FourArcsDefs.lean`) runs through `γ₁` on `[0,1/4]`, `γ₂` on
`[1/4,1/2]`, `γ₃` on `[1/2,3/4]` and `γ₄` on `[3/4,1]`; the gluing hypotheses make it continuous
on `ℝ`, and `γ₄ 1 = γ₁ 0` gives `fourArcs … 0 = fourArcs … 1`, so it descends to the quotient
`AddCircle 1` of `ℝ`, which is the circle.  The two remaining inputs are

* `Work.Top.fourArcs_injOn` — the descended map is injective (`fourArcs` is injective on `[0,1)`,
  which is where the intersection hypotheses are used);
* `Work.Top.fourArcs_image_Ico` — its range is the union of the four arcs.
-/
import Mathlib
import Submission.Work.Top.Defs
import Submission.Work.Top.Jordan
import Submission.Work.Top.FourArcsDefs
import Submission.Work.Top.fourArcs_injOn
import Submission.Work.Top.fourArcs_image_Ico

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set
open scoped Topology

noncomputable section

namespace Work.Top

/-! ## Lifting a map of the interval to the circle -/

/-- `AddCircle.liftIco` evaluated at `y` is just the defining map evaluated at the representative
of `y` in `[0,1)`. -/
theorem liftIco_eq (q : ℝ → ℂ) (y : AddCircle (1:ℝ)) :
    AddCircle.liftIco (1:ℝ) 0 q y = q ((AddCircle.equivIco (1:ℝ) 0 y : ℝ)) := rfl

/-- The range of the circle map induced by `q` is the image of `[0,1)` under `q`. -/
theorem range_liftIco (q : ℝ → ℂ) :
    Set.range (AddCircle.liftIco (1:ℝ) 0 q) = q '' Set.Ico (0:ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(AddCircle.equivIco (1:ℝ) 0 y : ℝ),
      by simpa using (AddCircle.equivIco (1:ℝ) 0 y).2, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨(s : AddCircle (1:ℝ)), AddCircle.liftIco_coe_apply (by simpa using hs)⟩

/-- If `q` is injective on `[0,1)` then the map on the circle that it induces is injective. -/
theorem injective_liftIco {q : ℝ → ℂ} (h : Set.InjOn q (Set.Ico (0:ℝ) 1)) :
    Function.Injective (AddCircle.liftIco (1:ℝ) 0 q) := by
  intro x y hxy
  rw [liftIco_eq, liftIco_eq] at hxy
  have hst := h (by simpa using (AddCircle.equivIco (1:ℝ) 0 x).2)
    (by simpa using (AddCircle.equivIco (1:ℝ) 0 y).2) hxy
  rw [← AddCircle.coe_equivIco (y := x), ← AddCircle.coe_equivIco (y := y), hst]

/-- The concatenation of the four arcs is a closed loop as soon as its last endpoint is its
first one. -/
theorem fourArcs_period (γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ)) (h₄₁ : γ₄ 1 = γ₁ 0) :
    fourArcs γ₁ γ₂ γ₃ γ₄ 0 = fourArcs γ₁ γ₂ γ₃ γ₄ 1 := by
  rw [fourArcs_zero, fourArcs_one, h₄₁]

/-! ## The four-arc loop is a Jordan curve -/

/-- **Four arcs glued cyclically into a loop bound a Jordan curve.**  If `γ₁ γ₂ γ₃ γ₄` are
injective arcs which close up (`γ₁ 1 = γ₂ 0`, `γ₂ 1 = γ₃ 0`, `γ₃ 1 = γ₄ 0`, `γ₄ 1 = γ₁ 0`), meet
only in their endpoints when consecutive (`range γᵢ ∩ range γᵢ₊₁ = {endpoint}`) and are disjoint
when opposite (`range γ₁ ⊥ range γ₃`, `range γ₂ ⊥ range γ₄`), then their union is a Jordan
curve. -/
theorem four_arcs_jordan (γ₁ γ₂ γ₃ γ₄ : C(unitInterval, ℂ))
    (h₁ : Function.Injective γ₁) (h₂ : Function.Injective γ₂)
    (h₃ : Function.Injective γ₃) (h₄ : Function.Injective γ₄)
    (h₁₂ : γ₁ 1 = γ₂ 0) (h₂₃ : γ₂ 1 = γ₃ 0) (h₃₄ : γ₃ 1 = γ₄ 0) (h₄₁ : γ₄ 1 = γ₁ 0)
    (hd₁₂ : Set.range γ₁ ∩ Set.range γ₂ = {γ₁ 1})
    (hd₂₃ : Set.range γ₂ ∩ Set.range γ₃ = {γ₂ 1})
    (hd₃₄ : Set.range γ₃ ∩ Set.range γ₄ = {γ₃ 1})
    (hd₄₁ : Set.range γ₄ ∩ Set.range γ₁ = {γ₄ 1})
    (hd₁₃ : Disjoint (Set.range γ₁) (Set.range γ₃))
    (hd₂₄ : Disjoint (Set.range γ₂) (Set.range γ₄)) :
    Work.Top.IsJordanCurve (Set.range γ₁ ∪ Set.range γ₂ ∪ Set.range γ₃ ∪ Set.range γ₄) := by
  have hq0 := fourArcs_period γ₁ γ₂ γ₃ γ₄ h₄₁
  have hcont : Continuous (AddCircle.liftIco (1:ℝ) 0 (fourArcs γ₁ γ₂ γ₃ γ₄)) :=
    AddCircle.liftIco_zero_continuous hq0 (continuous_fourArcs h₁₂ h₂₃ h₃₄).continuousOn
  refine ⟨⟨_, hcont⟩, ?_, ?_⟩
  · exact injective_liftIco (fourArcs_injOn γ₁ γ₂ γ₃ γ₄ h₁ h₂ h₃ h₄ h₁₂ h₂₃ h₃₄ h₄₁
      hd₁₂ hd₂₃ hd₃₄ hd₄₁ hd₁₃ hd₂₄)
  · show Set.range (AddCircle.liftIco (1:ℝ) 0 (fourArcs γ₁ γ₂ γ₃ γ₄)) = _
    rw [range_liftIco, fourArcs_image_Ico γ₁ γ₂ γ₃ γ₄ h₁₂ h₂₃ h₃₄ h₄₁]

end Work.Top
