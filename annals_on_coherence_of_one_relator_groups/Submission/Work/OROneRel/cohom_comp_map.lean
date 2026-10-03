import Mathlib
import Submission.Work.OROneRel.Basic
import Submission.Work.OROneRel.MagnusGenDefs

namespace Work.OROneRel

theorem cohom_comp_map {β γ : Type*} (d : γ → ℤ) (f : β → γ) (v : FreeGroup β) :
    Work.OROneRel.cohom d (FreeGroup.map f v) = Work.OROneRel.cohom (d ∘ f) v := by
  have h : (Work.OROneRel.cohom d).comp (FreeGroup.map f) = Work.OROneRel.cohom (d ∘ f) := by
    apply FreeGroup.ext_hom
    intro a
    simp only [MonoidHom.comp_apply, FreeGroup.map.of, Work.OROneRel.cohom_of,
      Function.comp_apply]
  exact DFunLike.congr_fun h v

end Work.OROneRel
