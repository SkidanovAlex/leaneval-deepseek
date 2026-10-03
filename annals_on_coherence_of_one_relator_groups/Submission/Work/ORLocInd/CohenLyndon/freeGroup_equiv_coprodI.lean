/-
# The free group on a product is the free product of free groups

For any types `α` and family `X : ι → Type`, a bijection `e : α ≃ Σ i, X i` induces an isomorphism
from the free group on `α` to the free product over `i` of the free groups on `X i`, sending the
generator `a` to the generator `(e a).2` in the factor `(e a).1`.

(The `ι = Bool` case is proved in `Submission/Work/OROneRel/exists_hnnStepCore.lean` as
`Work.OROneRel.freeGroupEquivCoprodI`, using `Monoid.CoprodI.FreeGroupBasis.coprodI`; the proof
does not use the index type.)
-/
import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.CohenLyndon

/-- **The free group on a sigma-type is the free product of the free groups on the fibres.** -/
theorem freeGroup_equiv_coprodI {ι : Type u} {X : ι → Type u} {α : Type u} (e : α ≃ Sigma X) :
    ∃ κ : FreeGroup α ≃* Monoid.CoprodI (fun i => FreeGroup (X i)),
      ∀ a : α, κ (FreeGroup.of a) = (Monoid.CoprodI.of (i := (e a).1)) (FreeGroup.of (e a).2) := by
  classical
  have hbase : ∀ (a : α),
      (Monoid.CoprodI.FreeGroupBasis.coprodI
        (fun i => FreeGroupBasis.ofFreeGroup (X i))).repr.symm (FreeGroup.of (e a)) =
      (Monoid.CoprodI.of (i := (e a).1)) (FreeGroup.of (e a).2) := by
    intro a
    show FreeGroup.lift
      (fun x : Sigma X => Monoid.CoprodI.of (M := fun i => FreeGroup (X i)) (i := x.1)
        (FreeGroupBasis.ofFreeGroup (X x.1) x.2))
      (FreeGroup.of (e a)) =
      Monoid.CoprodI.of (M := fun i => FreeGroup (X i)) (i := (e a).1) (FreeGroup.of (e a).2)
    rw [FreeGroup.lift_apply_of]
    rfl
  refine ⟨(FreeGroup.freeGroupCongr e).trans
    (Monoid.CoprodI.FreeGroupBasis.coprodI
      (fun i => FreeGroupBasis.ofFreeGroup (X i))).repr.symm, ?_⟩
  intro a
  show (Monoid.CoprodI.FreeGroupBasis.coprodI
      (fun i => FreeGroupBasis.ofFreeGroup (X i))).repr.symm
    (FreeGroup.freeGroupCongr e (FreeGroup.of a)) = _
  rw [show FreeGroup.freeGroupCongr e (FreeGroup.of a) = FreeGroup.of (e a) from
    FreeGroup.map.of]
  exact hbase a

end Work.ORLocInd.CohenLyndon
