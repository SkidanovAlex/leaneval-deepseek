import Mathlib
import Submission.Work.RED.Basic

namespace Work.RED

/-- If a finite group `P` that is a 2-group and is not cyclic is isomorphic to
`DihedralGroup n`, then `n` is even and nonzero.

The proof is by cardinality.  `DihedralGroup n` has order `2 * n`, while a finite
2-group has order `2 ^ k`, so `2 * n = 2 ^ k`.  If `n = 1`, then `P ≅ DihedralGroup 1`
is cyclic, which is excluded; hence `n = 2 ^ k` with `k ≥ 1` and `n` is even (and
certainly nonzero). -/
theorem even_dihedral_param_of_isPGroup_two_not_isCyclic
    {P : Type*} [Group P] [Finite P] {n : ℕ} (e : P ≃* DihedralGroup n)
    (hP : IsPGroup 2 P) (hnc : ¬ IsCyclic P) : Even n ∧ NeZero n := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := P)).1 hP
  have h2 : 2 * n = 2 ^ k := by
    rw [← DihedralGroup.nat_card, ← Nat.card_congr e.toEquiv]
    exact hk
  have hn1 : n ≠ 1 := by
    intro hn
    exact hnc ((MulEquiv.isCyclic e).mpr (DihedralGroup.isCyclic_iff.mpr hn))
  refine ⟨?_, ?_⟩
  · rcases k with _ | k
    · rw [pow_zero] at h2
      omega
    · rw [pow_succ] at h2
      have hmul : 2 * n = 2 * 2 ^ k := by rw [h2, Nat.mul_comm]
      have hn : n = 2 ^ k := Nat.mul_left_cancel (by norm_num) hmul
      rcases k with _ | k
      · rw [pow_zero] at hn
        exact absurd hn hn1
      · rw [hn, pow_succ]
        exact ⟨2 ^ k, by ring⟩
  · exact ⟨by
      rintro rfl
      rw [mul_zero] at h2
      exact (pow_ne_zero k (by norm_num : (2:ℕ) ≠ 0)) h2.symm⟩

end Work.RED
