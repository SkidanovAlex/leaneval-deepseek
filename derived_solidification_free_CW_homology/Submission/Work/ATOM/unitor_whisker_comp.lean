import Mathlib
import Submission.Work.ATOM.Defs

namespace Work.ATOM

open CategoryTheory MonoidalCategory in
theorem unitor_whisker_comp {C : Type*} [Category C] [MonoidalCategory C] {P W : C}
    (e : 𝟙_ C ⟶ P) (g : P ⟶ W) :
    ((λ_ P).inv ≫ (e ▷ P)) ≫ (P ◁ g) = g ≫ ((λ_ W).inv ≫ (e ▷ W)) := by
  rw [Category.assoc, ← MonoidalCategory.tensorHom_def]
  exact MonoidalCategory.leftUnitor_inv_comp_tensorHom e g

end Work.ATOM
