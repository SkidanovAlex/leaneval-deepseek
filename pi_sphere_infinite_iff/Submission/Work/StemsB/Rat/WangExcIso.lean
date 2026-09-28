import Mathlib
import Submission.Work.StemsB.Rat.WangDerivDefs
import Submission.Work.Cohomology.cappedPairMapIso
import Submission.Work.StemsB.SerreSphereCollar

/-!
# Excision over `ℚ`: `wangExc` is an isomorphism on cohomology

The pair map of the inclusion `(E|_G, E|_C) ↪ (E, E|_O)` is an isomorphism on relative cohomology
because `E|_G` and `E|_O` are open and cover `E`.  Over ℚ this is the general commutative-ring
statement `Work.Cohomology.relComplexMap_excision_isIso` (proved in
`Submission/Work/Cohomology/cappedPairMapIso.lean`), so no new excision theory is needed.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB.Rat

noncomputable section

variable {E : Type} [TopologicalSpace E]

theorem wangExc_isIso (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, Work.StemsB.SphModel b)) (k : ℕ) :
    CategoryTheory.IsIso (Work.StemsB.Rat.wangExc b p k) := by
  have hsp : Work.StemsB.Rat.wangA1 b p =
      ({y : ↥(p ⁻¹' sphLoopBig b) | (y : E) ∈ p ⁻¹' sphLoopOuter b}) := by
    ext x
    constructor
    · intro hx; exact hx.1
    · intro hx; exact ⟨hx, x.2⟩
  have hcov : p ⁻¹' sphLoopBig b ∪ p ⁻¹' sphLoopOuter b = Set.univ := by
    rw [← Set.preimage_union, Set.union_comm, sphLoopOuter_union_sphLoopBig, Set.preimage_univ]
  have key : ∀ (A₁ : Set ↥(p ⁻¹' sphLoopBig b))
      (hA₁ : A₁ = {y : ↥(p ⁻¹' sphLoopBig b) | (y : E) ∈ p ⁻¹' sphLoopOuter b})
      (h : ∀ x ∈ A₁, (Work.Cohomology.subtypeIncl (TopCat.of E) (p ⁻¹' sphLoopBig b)) x
        ∈ (p ⁻¹' sphLoopOuter b)),
      CategoryTheory.IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap
        (X₁ := TopCat.of ↥(p ⁻¹' sphLoopBig b)) (X₂ := TopCat.of E) ℚ A₁
        (p ⁻¹' sphLoopOuter b)
        (Work.Cohomology.subtypeIncl (TopCat.of E) (p ⁻¹' sphLoopBig b)) h) k) := by
    intro A₁ hA₁ h
    subst hA₁
    exact Work.Cohomology.relComplexMap_excision_isIso ℚ (TopCat.of E)
      (p ⁻¹' sphLoopBig b) (p ⁻¹' sphLoopOuter b)
      ((sphLoopBig_open b).preimage p.continuous) ((sphLoopOuter_open b).preimage p.continuous)
      hcov k h
  exact key (Work.StemsB.Rat.wangA1 b p) hsp (fun x hx => hx.1)

end

end Work.StemsB.Rat
