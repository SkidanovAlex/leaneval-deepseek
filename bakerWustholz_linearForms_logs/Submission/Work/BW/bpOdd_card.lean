import Mathlib
import Submission.Work.BW.bpOddDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The odd integers in `[−X, X]` are `X` in number, for even `X`; `oddIdx X` is the index set of
`bprodOdd`. Route: `X = 2m`, bijection `j ↦ 2j+1` from `Icc (−m) (m−1)`, or peel `±(M+1)`. -/
theorem bpOdd_card {X : ℕ} (hXe : Even X) : (oddIdx X).card = X := by
  obtain ⟨m, rfl⟩ := hXe
  have hm : m + m = 2 * m := by ring
  rw [hm]
  have himg : oddIdx (2*m) =
      (Finset.Icc (-(m:ℤ)) ((m:ℤ)-1)).image (fun j : ℤ => 2*j+1) := by
    ext k
    rw [mem_oddIdx_iff, Finset.mem_image]
    simp only [Finset.mem_Icc]
    constructor
    · rintro ⟨⟨j, rfl⟩, h1, h2⟩
      exact ⟨j, ⟨by omega, by omega⟩, rfl⟩
    · rintro ⟨j, ⟨h1, h2⟩, heq⟩
      exact ⟨⟨j, heq.symm⟩, by omega, by omega⟩
  rw [himg]
  have hinj : Function.Injective (fun j : ℤ => 2*j+1) := by intro a b h; linarith
  rw [Finset.card_image_of_injective _ hinj, Int.card_Icc]
  have h2 : ((m:ℤ) - 1 + 1 - (-(m:ℤ))) = ((2*m : ℕ) : ℤ) := by push_cast; ring
  rw [h2, Int.toNat_natCast]

end Work.BW
