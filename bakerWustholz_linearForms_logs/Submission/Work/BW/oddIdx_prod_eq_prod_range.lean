import Mathlib
import Submission.Work.BW.bpOddDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For every `m`, the odd integers `k` with `|k| ≤ 2m` are exactly `±(2i+1)` for `i < m`. -/
lemma oddIdx_two_mul_eq_image_union (m : ℕ) :
    oddIdx (2*m) = (Finset.range m).image (fun i : ℕ => 2*(i:ℤ)+1)
      ∪ (Finset.range m).image (fun i : ℕ => -(2*(i:ℤ)+1)) := by
  ext k
  simp only [mem_oddIdx_iff, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  push_cast
  constructor
  · rintro ⟨hodd, hlo, hhi⟩
    obtain ⟨j, rfl⟩ := hodd
    have h1 : -((m:ℤ)) ≤ j := by omega
    have h2 : j ≤ (m:ℤ) - 1 := by omega
    rcases le_or_gt 0 j with hj | hj
    · exact Or.inl ⟨j.toNat, by rw [Int.toNat_lt hj]; omega,
        by rw [Int.toNat_of_nonneg hj]⟩
    · exact Or.inr ⟨(-j-1).toNat, by rw [Int.toNat_lt (by omega)]; omega,
        by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨⟨(i:ℤ), by ring⟩, by omega, by omega⟩
    · exact ⟨⟨-(i:ℤ)-1, by ring⟩, by omega, by omega⟩

/-- The positive and the negative branches of `oddIdx_two_mul_eq_image_union` are disjoint. -/
lemma oddIdx_two_mul_image_disjoint (m : ℕ) :
    Disjoint ((Finset.range m).image (fun i : ℕ => 2*(i:ℤ)+1))
      ((Finset.range m).image (fun i : ℕ => -(2*(i:ℤ)+1))) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  simp only [Finset.mem_image, Finset.mem_range] at ha hb
  obtain ⟨i, -, rfl⟩ := ha
  obtain ⟨j, -, hj⟩ := hb
  omega

/-- For even `X`, the odd integers `k` with `|k| ≤ X` are exactly `±(2i+1)` for `i < X/2`, so a
product over `oddIdx X` splits into pair products over `Finset.range (X/2)`. -/
lemma oddIdx_prod_eq_prod_range {M : Type*} [CommMonoid M] (X : ℕ) (hX : Even X) (f : ℤ → M) :
    ∏ k ∈ oddIdx X, f k
      = ∏ i ∈ Finset.range (X/2), (f (2*(i:ℤ)+1) * f (-(2*(i:ℤ)+1))) := by
  obtain ⟨m, hm⟩ := hX
  subst hm
  rw [← two_mul, Nat.mul_div_right m (by norm_num : 0 < 2)]
  have h1 : ∏ k ∈ (Finset.range m).image (fun i : ℕ => 2*(i:ℤ)+1), f k
      = ∏ i ∈ Finset.range m, f (2*(i:ℤ)+1) := by
    apply Finset.prod_image
    intro a _ b _ hab
    simp only [] at hab
    omega
  have h2 : ∏ k ∈ (Finset.range m).image (fun i : ℕ => -(2*(i:ℤ)+1)), f k
      = ∏ i ∈ Finset.range m, f (-(2*(i:ℤ)+1)) := by
    apply Finset.prod_image
    intro a _ b _ hab
    simp only [] at hab
    omega
  rw [oddIdx_two_mul_eq_image_union m, Finset.prod_union (oddIdx_two_mul_image_disjoint m),
    h1, h2, ← Finset.prod_mul_distrib]

end Work.BW
