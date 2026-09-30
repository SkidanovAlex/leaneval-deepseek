import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The odd integers in `{−X, …, X}` number exactly `X` when `X` is even (they are the `X`
values `±1, ±3, …, ±(X−1)`); this is the count `#Z = X` of the known points in the even step, where
`Z` is the index set of the lacunary Blaschke product `B'(·;X) = ∏_{k ∈ (Icc (−X) X).filter Odd} β(·;k)`. -/
theorem card_filter_odd_Icc {X : ℕ} (hX : Even X) :
    ((Finset.Icc (-(X : ℤ)) X).filter Odd).card = X := by
  obtain ⟨m, hm⟩ := hX
  rw [hm]
  -- With `X = m + m`, the odd elements of `[-X, X]` are exactly `2*j+1` for `j ∈ [-m, m-1]`.
  have himg : (Finset.Icc (-((m+m:ℕ):ℤ)) ((m+m:ℕ):ℤ)).filter Odd
      = (Finset.Icc (-(m:ℤ)) ((m:ℤ)-1)).image (fun j : ℤ => 2*j+1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, j, hj⟩
      exact ⟨j, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨j, ⟨hj1, hj2⟩, hjk⟩
      exact ⟨⟨by omega, by omega⟩, j, by omega⟩
  have hf : Function.Injective (fun j : ℤ => 2*j+1) := by
    intro a b h
    simp only at h
    omega
  rw [himg]
  rw [Finset.card_image_of_injective _ hf]
  -- `#(Icc (-m) (m-1)) = (m-1+1-(-m)).toNat = (2m).toNat = 2m = X`.
  rw [Int.card_Icc]
  omega

end Work.BW
