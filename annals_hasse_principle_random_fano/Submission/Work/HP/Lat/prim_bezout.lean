import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.gcd_sum

/-!
# Bézout for a primitive integer vector

`IsPrim c` means `Finset.univ.gcd c = 1`.  `Work.HP.gcd_sum` shows that the gcd of the entries of an
integer vector is a `ℤ`-linear combination of them, so for a primitive `c` there is `u` with
`∑ i, u i * c i = 1`.
-/

namespace Work.HP.Lat

theorem prim_bezout {ι : Type*} [Fintype ι]
    (c : ι → ℤ) (hc : IsPrim c) :
    ∃ u : ι → ℤ, ∑ i, u i * c i = 1 := by
  classical
  obtain ⟨u, hu⟩ := Work.HP.gcd_sum c
  exact ⟨u, by rw [hu]; exact hc⟩

end Work.HP.Lat
