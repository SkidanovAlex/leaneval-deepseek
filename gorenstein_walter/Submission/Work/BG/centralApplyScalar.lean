import Mathlib
import Submission.OddOrder.GroupTheory.RepresentationTheory.AbsolutelyIrreducible

namespace Work.BG

/-- **Schur's lemma, central-element form.**  A central element `a` of `X` (here recorded
pointwise as `a * x = x * a` for all `x`) acts on a finite-dimensional irreducible complex
representation `ρ` by a scalar.  This is exactly `OddOrder.RepresentationTheory.center_isScalar`
with the membership hypothesis `a ∈ Subgroup.center X` unpacked. -/
theorem centralApplyScalar {X V : Type} [Group X] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ X V) (hρ : Representation.IsIrreducible ρ)
    (a : X) (hcent : ∀ x : X, a * x = x * a) :
    ∃ μ : ℂ, ρ a = μ • LinearMap.id := by
  have hρ' : ρ.IsIrreducible := hρ
  exact OddOrder.RepresentationTheory.center_isScalar ρ
    (Subgroup.mem_center_iff.mpr fun x => (hcent x).symm)

end Work.BG
