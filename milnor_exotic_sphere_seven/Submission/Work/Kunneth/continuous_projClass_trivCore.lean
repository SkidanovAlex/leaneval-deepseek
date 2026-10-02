import Mathlib
import Submission.Work.LerayHirsch.Chapter

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The class of the fibre coordinate is continuous for the trivial complex bundle

For the trivial complex bundle `Z = ε^m` over an arbitrary topological space `B` (its gluing data
`trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit` has a single chart, the whole base),
the "class of the fibre coordinate"

`Work.LerayHirsch.projClass Z : P(ε^m) → ℙ ℂ (ℂ^m)`,  `[b, v] ↦ [v]`

is continuous.

The quotient map `Work.LerayHirsch.mkProj Z : (E∖0) → P(ε^m)` is a quotient map, so it suffices to
check continuity of `projClass Z ∘ mkProj Z`, which is `p ↦ mkP m ⟨p.1.2, _⟩`.  For the trivial
bundle the fibre coordinate `p ↦ p.1.2` is continuous: the punctured total space is `B × (ℂ^m∖0)`
by `Work.LerayHirsch.exists_punctTrivHomeo`, whose underlying map is exactly
`p ↦ (p.1.proj, ⟨p.1.2, _⟩)`. -/

namespace Work.Kunneth

open Work.LerayHirsch Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

/-- **The class of the fibre coordinate is continuous** for the trivial complex bundle over an
arbitrary base. -/
theorem continuous_projClass_trivCore (m : ℕ) (B : Type) [TopologicalSpace B] :
    Continuous (Work.LerayHirsch.projClass
      (trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit)) := by
  classical
  let Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit :=
    trivialVectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) PUnit
  obtain ⟨φ, hφ⟩ := Work.LerayHirsch.exists_punctTrivHomeo m B
  -- It suffices to check continuity after composing with the quotient map `mkProj`.
  have key : Continuous (fun p : ↥(Work.Thom.zeroComplement (Work.Thom.realification Z)) =>
      Work.LerayHirsch.projClass Z (Work.LerayHirsch.mkProj Z p)) := by
    -- On representatives, `projClass Z ∘ mkProj Z` is the class of the fibre coordinate.
    have h1 : (fun p : ↥(Work.Thom.zeroComplement (Work.Thom.realification Z)) =>
        Work.LerayHirsch.projClass Z (Work.LerayHirsch.mkProj Z p))
        = fun p => Work.LerayHirsch.mkP m ⟨(show EuclideanSpace ℂ (Fin m) from p.1.2),
            (Work.Thom.mem_zeroComplement p.1).mp p.2⟩ := by
      funext p
      rw [Work.LerayHirsch.projClass_mkProj]
      simp only [Work.LerayHirsch.mkP_apply]
    rw [h1]
    -- The punctured total space of the trivial bundle is `B × (ℂ^m ∖ 0)`, with the fibre
    -- coordinate as second component.
    have h2 : (fun p : ↥(Work.Thom.zeroComplement (Work.Thom.realification Z)) =>
        Work.LerayHirsch.mkP m ⟨(show EuclideanSpace ℂ (Fin m) from p.1.2),
          (Work.Thom.mem_zeroComplement p.1).mp p.2⟩)
        = (fun q : B × {v : EuclideanSpace ℂ (Fin m) // v ≠ 0} =>
            Work.LerayHirsch.mkP m ⟨q.2.1, q.2.2⟩) ∘
          (φ : ↥(Work.Thom.zeroComplement (Work.Thom.realification Z)) → _) := by
      funext p
      rw [Function.comp_apply, hφ p]
    rw [h2]
    exact (Work.LerayHirsch.continuous_mkP m).comp ((Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_snd) (fun q => q.2.2)).comp φ.continuous)
  have : Continuous (Work.LerayHirsch.projClass Z) := by
    rw [Topology.IsQuotientMap.continuous_iff
      (isQuotientMap_quotient_mk' (s := Work.LerayHirsch.projSetoid Z))]
    exact key
  exact this

end

end Work.Kunneth
