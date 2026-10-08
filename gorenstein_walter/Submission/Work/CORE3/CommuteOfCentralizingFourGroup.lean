import Mathlib

namespace Work.CORE3

-- (put this in `namespace Work.CORE3`, so the full name is `Work.CORE3.CommuteOfCentralizingFourGroup`)
/-- An elementary group-theory fact: if a subgroup `V` of order `4` of a group `S` of order `8`
is central in `S`, then `S` is commutative.  (`V ≤ Z(S)` gives `|S : Z(S)| ≤ 2`, so `S/Z(S)` has
order `≤ 2`, hence is cyclic, hence `S` is commutative by
`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` applied to `S →* S ⧸ Z(S)`, using
`isCyclic_of_card_dvd_prime` and `Subgroup.index_eq_card`.) -/
-- If a natural number divides `8` and is at most `2`, then it divides `2`.
private lemma dvd_two_of_dvd_eight_of_le_two {n : ℕ} (hle : n ≤ 2) (hdvd : n ∣ 8) : n ∣ 2 := by
  obtain ⟨k, hk⟩ := hdvd
  have hn0 : n ≠ 0 := by rintro rfl; simp at hk
  have : n = 1 ∨ n = 2 := by omega
  rcases this with rfl | rfl <;> norm_num

theorem CommuteOfCentralizingFourGroup {S : Type} [Group S] [Finite S] (V : Subgroup S)
    (hcardV : Nat.card V = 4) (hcardS : Nat.card S = 8)
    (hcent : ∀ v ∈ V, ∀ s : S, v * s = s * v) : IsMulCommutative S := by
  -- Every element of `V` is central, i.e. `V ≤ Z(S)`.
  have hVZ : V ≤ Subgroup.center S := by
    intro v hv
    rw [Subgroup.mem_center_iff]
    exact fun s => (hcent v hv s).symm
  -- Hence `|Z(S)| ≥ |V| = 4`.
  have hcardZ : 4 ≤ Nat.card (Subgroup.center S) := by
    have h := Subgroup.card_le_of_le hVZ
    omega
  -- Since `|Z(S)| · [S : Z(S)] = |S| = 8` and `|Z(S)| ≥ 4`, the index is at most `2`.
  have hidx : (Subgroup.center S).index ≤ 2 := by
    have hmul := Subgroup.index_mul_card (H := Subgroup.center S)
    rw [hcardS] at hmul
    have hle : (Subgroup.center S).index * 4 ≤ 2 * 4 := by
      calc (Subgroup.center S).index * 4
          ≤ (Subgroup.center S).index * Nat.card (Subgroup.center S) :=
            Nat.mul_le_mul_left _ hcardZ
        _ = 8 := hmul
        _ = 2 * 4 := by norm_num
    exact Nat.le_of_mul_le_mul_right hle (by norm_num)
  have hcardQ : Nat.card (S ⧸ Subgroup.center S) ≤ 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  -- The order of `S ⧸ Z(S)` divides `|S| = 8`.
  have hdvd8 : Nat.card (S ⧸ Subgroup.center S) ∣ 8 := by
    rw [← Subgroup.index_eq_card, ← hcardS]
    exact Subgroup.index_dvd_card (Subgroup.center S)
  -- So `S ⧸ Z(S)`, of order `≤ 2` and dividing `8`, has order dividing the prime `2`: it is cyclic.
  have hcyc : IsCyclic (S ⧸ Subgroup.center S) :=
    isCyclic_of_card_dvd_prime (α := S ⧸ Subgroup.center S) (p := 2)
      (dvd_two_of_dvd_eight_of_le_two hcardQ hdvd8)
  -- A group whose quotient by its center is cyclic is commutative.
  exact isMulCommutative_of_isCyclic_quotient_center_self S

end Work.CORE3
