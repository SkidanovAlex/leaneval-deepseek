import Mathlib
import Submission.Work.L2F.Dihedral.dihedral_oddSubgroup

namespace Work.CORE4

/-- If `y` commutes with a reflection `sr i` of a dihedral group, then `y` is an involution.
(Concretely: for a rotation `r k` the commutation relation gives `k = -k`, and a reflection is an
involution outright.) -/
lemma sq_eq_one_of_comm_reflection {m : ℕ} {i : ZMod m} {y : DihedralGroup m}
    (h : y * DihedralGroup.sr i = DihedralGroup.sr i * y) : y * y = 1 := by
  rcases y with k | k
  · have h1 : i - k = i + k := by simpa using h
    have hk : k = -k := by
      have h1' : i + (-k) = i + k := by simpa [sub_eq_add_neg] using h1
      exact (add_left_cancel h1').symm
    have hkk : k + k = 0 := (eq_neg_iff_add_eq_zero).mp hk
    rw [DihedralGroup.r_mul_r, hkk, DihedralGroup.r_zero]
  · exact DihedralGroup.sr_mul_self k

/-- An element `t` of a dihedral group commuting with a nontrivial odd-order subgroup `X` must be
a rotation: if `t = sr i` were a reflection, then every `y ∈ X` would be an involution
(`sq_eq_one_of_comm_reflection`), contradicting `Odd (Nat.card X)` for `y ≠ 1 ∈ X`.  Hence
`t = r i`, and conjugating a rotation by a rotation fixes it while conjugating it by a reflection
inverts it. -/
theorem DihedralConjCentralizerOdd {m : ℕ} (X : Subgroup (DihedralGroup m))
    (hXne : X ≠ ⊥) (hXodd : Odd (Nat.card X)) (d t : DihedralGroup m)
    (ht : t ∈ Subgroup.centralizer (X : Set (DihedralGroup m))) :
    d * t * d⁻¹ = t ∨ d * t * d⁻¹ = t⁻¹ := by
  rcases t with i | i
  · -- `t = r i` is a rotation: rotations commute with `r i`, reflections invert it.
    rcases d with j | j
    · left
      rw [DihedralGroup.r_mul_r, DihedralGroup.inv_r, DihedralGroup.r_mul_r]
      congr 1
      ring
    · right
      rw [DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
        DihedralGroup.inv_r]
      congr 1
      ring
  · -- `t = sr i` is a reflection: this is impossible, as `X` is a nontrivial odd-order subgroup.
    exfalso
    obtain ⟨y, hyX, hy1⟩ : ∃ y, y ∈ X ∧ y ≠ 1 := by
      by_contra h
      push Not at h
      exact hXne ((Subgroup.eq_bot_iff_forall X).mpr h)
    have hcomm : y * DihedralGroup.sr i = DihedralGroup.sr i * y :=
      (Subgroup.mem_centralizer_iff.mp ht) y hyX
    have hyy : y * y = 1 := sq_eq_one_of_comm_reflection hcomm
    -- `orderOf y` divides both `2` and the odd number `Nat.card X`, hence equals `1`.
    have hdiv2 : orderOf y ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hyy
    have hdivX : orderOf y ∣ Nat.card X := by
      have h2 := orderOf_dvd_natCard (⟨y, hyX⟩ : X)
      rw [← Subgroup.orderOf_coe (⟨y, hyX⟩ : X)] at h2
      exact h2
    have hodd : Odd (orderOf y) := hXodd.of_dvd_nat hdivX
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv2 with h | h
    · exact hy1 (orderOf_eq_one_iff.mp h)
    · rw [h] at hodd
      exact absurd hodd (by decide)

end Work.CORE4
