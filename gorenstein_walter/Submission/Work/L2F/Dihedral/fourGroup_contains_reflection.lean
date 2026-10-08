import Mathlib
import Submission.Work.L2F.Dihedral.zmod_half_of_add_self
import Submission.Work.L2F.Dihedral.exists_sr_mem_of_card_four
import Submission.Work.L2F.Dihedral.exists_ne_one_ne_of_card_four

namespace Work.L2F.Dihedral

/-- A subgroup `V ≤ DihedralGroup m` of order `4` all of whose elements are involutions contains a
reflection `sr i`, and then also the unique involution `r (m / 2)` of the rotation subgroup.

Indeed `V` cannot sit inside the rotation subgroup `⟨r⟩` (a cyclic group), since a cyclic group of
order `4` has an element of order `4`, contradicting the exponent-`2` hypothesis; so `V` contains a
reflection `sr i`.  Taking a second element `u ∈ V` distinct from `1` and `sr i`: either `u = r k`
with `k ≠ 0`, and `u ^ 2 = 1` gives `k + k = 0`, so `k = m / 2`; or `u = sr j` with `j ≠ i`, and
then `sr i * sr j = r (j - i) ∈ V` is a non-trivial involution of the rotations, so again
`j - i = m / 2`. -/
lemma fourGroup_contains_reflection {m : ℕ} (V : Subgroup (DihedralGroup m)) (hcard : Nat.card V = 4)
    (hsq : ∀ v ∈ V, v ^ 2 = 1) :
    ∃ i : ZMod m, DihedralGroup.sr i ∈ V ∧ DihedralGroup.r ((m / 2 : ℕ) : ZMod m) ∈ V := by
  obtain ⟨i, hi⟩ := exists_sr_mem_of_card_four V hcard hsq
  obtain ⟨u, hu, hu1, hus⟩ := exists_ne_one_ne_of_card_four V hcard hi
  rcases u with k | j
  · -- the second element is the rotation `r k`
    refine ⟨i, hi, ?_⟩
    have hk : k ≠ 0 := by
      intro h
      refine hu1 ?_
      rw [h]
      exact DihedralGroup.r_zero
    have h2 : k + k = 0 := by
      have h := hsq (DihedralGroup.r k) hu
      rw [pow_two, DihedralGroup.r_mul_r, DihedralGroup.one_def] at h
      exact DihedralGroup.r.inj h
    rw [← zmod_half_of_add_self k h2 hk]
    exact hu
  · -- the second element is the reflection `sr j`, so `r (j - i) = sr i * sr j ∈ V`
    refine ⟨i, hi, ?_⟩
    have hji : j ≠ i := fun h => hus (by rw [h])
    have hw : DihedralGroup.r (j - i) ∈ V := by
      have h := V.mul_mem hi hu
      rwa [DihedralGroup.sr_mul_sr] at h
    have hne : j - i ≠ 0 := fun h => hji (sub_eq_zero.mp h)
    have h2 : (j - i) + (j - i) = 0 := by
      have h := hsq (DihedralGroup.r (j - i)) hw
      rw [pow_two, DihedralGroup.r_mul_r, DihedralGroup.one_def] at h
      exact DihedralGroup.r.inj h
    rw [← zmod_half_of_add_self (j - i) h2 hne]
    exact hw

end Work.L2F.Dihedral
