import Mathlib
import Submission.Work.MotK.TwRule
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotK

/-- The polarisation `kleinTwPolarP a b h c` of the quadratic twisted Pfaffian map
`kleinTwP a b h` is linear in its second argument: each component of `kleinTwP` is a
homogeneous quadratic form in the coordinates, so its polarisation is a bilinear form. -/
theorem KleinTwPolarLin {R : Type*} [CommRing R] (a b h : R) (c u v : Fin 5 → R) (s t : R) :
    Work.MotK.kleinTwPolarP a b h c (fun i => s * u i + t * v i)
      = fun i => s * Work.MotK.kleinTwPolarP a b h c u i
          + t * Work.MotK.kleinTwPolarP a b h c v i := by
  funext i
  fin_cases i <;>
    simp only [kleinTwPolarP, kleinTwP, kleinTwP0, kleinTwP1, kleinTwP2, kleinTwP3, kleinTwP4] <;>
    simp only [show (⟨0, by decide⟩ : Fin 5) = 0 from rfl,
               show (⟨1, by decide⟩ : Fin 5) = 1 from rfl,
               show (⟨2, by decide⟩ : Fin 5) = 2 from rfl,
               show (⟨3, by decide⟩ : Fin 5) = 3 from rfl,
               show (⟨4, by decide⟩ : Fin 5) = 4 from rfl] <;>
    simp <;>
    first | refl_ring1 | ring

end Work.MotK
