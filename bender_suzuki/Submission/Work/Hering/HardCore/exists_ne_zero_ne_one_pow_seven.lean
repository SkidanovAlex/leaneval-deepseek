import Mathlib
import Submission.Work.Hering.AppVIII.FrobField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

/-- The cardinality of `GF(2³)` is `8`. -/
theorem card_galoisField_two_three : Nat.card (GaloisField 2 3) = 8 := by
  rw [GaloisField.card 2 3 (by norm_num : (3 : ℕ) ≠ 0)]
  norm_num

/-- There is an element of `GF(2³)` different from both `0` and `1`. -/
theorem exists_ne_zero_ne_one_galoisField_two_three :
    ∃ x : GaloisField 2 3, x ≠ 0 ∧ x ≠ 1 := by
  classical
  have hinst : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 3) = 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_galoisField_two_three
  have hlt : ({0, 1} : Finset (GaloisField 2 3)).card <
      (Finset.univ : Finset (GaloisField 2 3)).card := by
    rw [Finset.card_pair (zero_ne_one (α := GaloisField 2 3)), Finset.card_univ, hcard]
    norm_num
  obtain ⟨x, -, hxnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
  exact ⟨x, hxnot.1, hxnot.2⟩

theorem exists_ne_zero_ne_one_pow_seven :
    ∃ x : GaloisField 2 3, x ≠ 0 ∧ x ≠ 1 ∧ x ^ 7 = 1 := by
  classical
  have hinst : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 3) = 8 := by
    rw [← Nat.card_eq_fintype_card]
    exact card_galoisField_two_three
  obtain ⟨x, hx0, hx1⟩ := exists_ne_zero_ne_one_galoisField_two_three
  refine ⟨x, hx0, hx1, ?_⟩
  have h := FiniteField.pow_card_sub_one_eq_one x hx0
  rw [hcard] at h
  norm_num at h
  exact h

end Work.Hering.HardCore
