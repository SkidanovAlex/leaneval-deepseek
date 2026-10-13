import Mathlib
import Submission.Work.WilG0.Defs

namespace Work.WilG0

theorem Omega_cast {S : WilkiesDesign.SOMin} {a b F D : ℕ} (h : a = b) {X : Set (Fin a → ℝ)} (hX : X ∈ S.Ω F D a) :
    (h ▸ X) ∈ S.Ω F D b := by
  subst h
  exact hX

end Work.WilG0
