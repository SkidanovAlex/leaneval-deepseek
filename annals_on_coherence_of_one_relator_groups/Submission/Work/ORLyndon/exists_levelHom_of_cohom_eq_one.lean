import Mathlib
import Submission.Work.ORLyndon.Lyndon
import Submission.Work.OROneRel.MagnusGenDefs

namespace Work.ORLyndon

theorem exists_levelHom_of_cohom_eq_one {α : Type*} [DecidableEq α] (c : α → ℤ) (w : FreeGroup α)
    (hw : Work.OROneRel.cohom c w = 1) :
    ∃ φ : Work.ORLyndon.OneRelatorGroup w →* Multiplicative ℤ,
      ∀ v : FreeGroup α, φ (Work.ORLyndon.presentRho w v) = Work.OROneRel.cohom c v := by
  classical
  -- `cohom c` is `FreeGroup.lift (fun a => Multiplicative.ofAdd (c a))` by definition, so it kills
  -- the defining relator `w` and therefore descends to the presented group `⟨w⟩`.
  refine ⟨PresentedGroup.toGroup (rels := {w}) (G := Multiplicative ℤ)
    (f := fun a => Multiplicative.ofAdd (c a)) ?_, ?_⟩
  · intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact hw
  · intro v
    rfl

end Work.ORLyndon
