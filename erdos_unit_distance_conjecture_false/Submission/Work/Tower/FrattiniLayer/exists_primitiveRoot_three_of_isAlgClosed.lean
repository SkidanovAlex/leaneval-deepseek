import Mathlib
import Submission.Work.Tower.FrattiniLayer.Basic

namespace Work.Tower.FrattiniLayer

open Polynomial

theorem exists_primitiveRoot_three_of_isAlgClosed (Ω : Type*) [Field Ω] [CharZero Ω]
    [IsAlgClosed Ω] : ∃ ζ : Ω, IsPrimitiveRoot ζ 3 := by
  have : NeZero (3 : Ω) := ⟨by norm_num⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (cyclotomic 3 Ω) (by
    rw [degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (by norm_num : 0 < 3)).ne')
  exact ⟨ζ, isRoot_cyclotomic_iff.mp hζ⟩

end Work.Tower.FrattiniLayer
