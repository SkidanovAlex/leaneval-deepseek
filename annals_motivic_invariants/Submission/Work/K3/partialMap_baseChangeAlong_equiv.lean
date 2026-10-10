import Mathlib
import Submission.Work.K3.BaseChangeBirational

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.K3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

/-! ## The two projections of a base-changed partial map

`Work.K3.PartialMap.baseChangeAlong f g` is defined by pulling back the graph of `g` along
`f : T ⟶ S`; concretely its underlying morphism is a `pullback.lift` into
`baseChangeAlong f Y = pullback f (Y ↘ S)`.  These two lemmas compute the two components of that
morphism (equivalently: characterise it by its projections). -/


/-- **Base change respects the equivalence relation on partial maps**: two partial maps which agree
on a dense open base change to partial maps which agree on a dense open (the preimage of a dense
open is dense, `Work.K3.Dense.preimage_baseChangeAlongProj`).  This is what makes the base change
of a *rational* map well defined. -/
theorem partialMap_baseChangeAlong_equiv {S T X Y : Scheme.{0}} (f : T ⟶ S) [X.Over S] [Y.Over S]
    [Surjective f] [UniversallyOpen f] (g₁ g₂ : X.PartialMap Y) [g₁.IsOver S] [g₂.IsOver S]
    (h : g₁.toRationalMap = g₂.toRationalMap) :
    (Work.K3.PartialMap.baseChangeAlong f g₁).toRationalMap =
      (Work.K3.PartialMap.baseChangeAlong f g₂).toRationalMap := by
  -- `g₁` and `g₂` agree on a dense open `W`, cut down to the common domains.
  obtain ⟨W, hW, hWl, hWr, e⟩ := PartialMap.toRationalMap_eq_iff.mp h
  -- Base change to the preimage of `W`, which is dense.
  have hWl' : (baseChangeAlongProj f X) ⁻¹ᵁ W ≤ (PartialMap.baseChangeAlong f g₁).domain :=
    (baseChangeAlongProj f X).preimage_mono hWl
  have hWr' : (baseChangeAlongProj f X) ⁻¹ᵁ W ≤ (PartialMap.baseChangeAlong f g₂).domain :=
    (baseChangeAlongProj f X).preimage_mono hWr
  refine PartialMap.toRationalMap_eq_iff.mpr ⟨(baseChangeAlongProj f X) ⁻¹ᵁ W,
    Dense.preimage_baseChangeAlongProj f X hW, hWl', hWr', ?_⟩
  -- It remains to compare the two base changes on the preimage of `W`.  Unfold the definition of
  -- the base change so that the domains appear as the explicit preimages of `W`, `g₁.domain`,
  -- `g₂.domain`; then compare the two `pullback.lift`s componentwise.
  rw [PartialMap.restrict_hom, PartialMap.restrict_hom]
  dsimp only [PartialMap.baseChangeAlong] at hWl' hWr' ⊢
  apply pullback.hom_ext
  · -- component into `T`
    rw [Category.assoc, Category.assoc]
    rw [pullback.lift_fst, pullback.lift_fst]
    rw [← Category.assoc, ← Category.assoc]
    rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  · -- component into `Y`: use that `g₁` and `g₂` agree on `W`
    rw [Category.assoc, Category.assoc]
    rw [pullback.lift_snd, pullback.lift_snd]
    rw [← Category.assoc, ← Category.assoc]
    rw [← morphismRestrict_homOfLE (baseChangeAlongProj f X) W g₁.domain hWl,
        ← morphismRestrict_homOfLE (baseChangeAlongProj f X) W g₂.domain hWr]
    simp only [Category.assoc]
    rw [← PartialMap.restrict_hom g₁ W hW hWl, ← PartialMap.restrict_hom g₂ W hW hWr, e]

end Work.K3
