import Mathlib
import Submission.Work.OROneRel.FreiheitssatzDefs

universe u

namespace Work.OROneRel

theorem zeta_mk_eq_expand {α : Type u} (t : α) (v : List (({a : α // a ≠ t} × ℤ) × Bool)) :
    Work.OROneRel.zeta t (FreeGroup.mk v) = Work.OROneRel.expand t v := by
  classical
  -- Pointwise, sending a signed letter `((s,i),b)` through `zeta` agrees with `expandLetter`.
  have hkey : ∀ x : ({a : α // a ≠ t} × ℤ) × Bool,
      (bif x.2 then
        ((FreeGroup.of t) ^ (x.1.2) * FreeGroup.of (x.1.1 : α) * (FreeGroup.of t) ^ (-(x.1.2)))
      else
        (((FreeGroup.of t) ^ (x.1.2) * FreeGroup.of (x.1.1 : α) * (FreeGroup.of t) ^ (-(x.1.2)))⁻¹))
      = expandLetter t x := by
    rintro ⟨⟨s, i⟩, b⟩
    cases b
    · simp only [Bool.cond_false, expandLetter, Bool.false_eq_true, ↓reduceIte]
      group
    · simp only [Bool.cond_true, expandLetter, ↓reduceIte]
      group
  simp only [zeta, FreeGroup.lift_mk, expand]
  congr 1
  exact congrArg (List.map · v) (funext hkey)

end Work.OROneRel
