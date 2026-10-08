import Mathlib

namespace Work.A7REC.Char

set_option linter.style.haveILetI false

/-- In a finite group of order `15`, all subgroups of order `5` coincide. -/
theorem eq_of_card_five_of_card_fifteen {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 15) {A B : Subgroup H} (hA : Nat.card A = 5) (hB : Nat.card B = 5) :
    A = B := by
  -- In a group of order `15`, the number of Sylow `5`-subgroups is `≡ 1 [MOD 5]` and divides
  -- the index of any Sylow `5`-subgroup, which is `3`. Hence there is exactly one of them.
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hAidx : A.index = 3 := by
    have h := A.card_mul_index
    rw [hA, hH] at h
    omega
  have hA5 : IsPGroup 5 A := IsPGroup.of_card (p := 5) (n := 1) (by rw [hA]; simp)
  have hndA : ¬ 5 ∣ A.index := by rw [hAidx]; norm_num
  have hBidx : B.index = 3 := by
    have h := B.card_mul_index
    rw [hB, hH] at h
    omega
  have hB5 : IsPGroup 5 B := IsPGroup.of_card (p := 5) (n := 1) (by rw [hB]; simp)
  have hndB : ¬ 5 ∣ B.index := by rw [hBidx]; norm_num
  -- the number of Sylow `5`-subgroups is `1`
  have hnd : Nat.card (Sylow 5 H) ∣ 3 := by
    have h := Sylow.card_dvd_index (hA5.toSylow hndA)
    simpa [hAidx] using h
  have hmod : Nat.card (Sylow 5 H) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 H
  have hcard1 : Nat.card (Sylow 5 H) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hnd with h | h
    · exact h
    · rw [h] at hmod
      exact absurd hmod (by decide)
  haveI : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp hcard1).1
  -- both `A` and `B` are (the coercion of) the unique Sylow `5`-subgroup
  have hSylow : (hA5.toSylow hndA) = (hB5.toSylow hndB) := Subsingleton.elim _ _
  have := congrArg (fun S : Sylow 5 H => (S : Subgroup H)) hSylow
  simpa using this

end Work.A7REC.Char
