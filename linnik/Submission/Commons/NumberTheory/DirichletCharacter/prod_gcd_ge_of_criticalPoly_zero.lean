import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_cube_local

namespace Commons.NumberTheory.DirichletCharacter

theorem prod_gcd_ge_of_criticalPoly_zero {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → (![a 0, a 1, a 2, b 0, b 1, b 2] i)
        ≠ (![a 0, a 1, a 2, b 0, b 1, b 2] j))
    (hH : Commons.NumberTheory.DirichletCharacter.cH p a b = 0) :
    p ≤ ∏ j ∈ Finset.univ.erase i,
          Nat.gcd (p ^ e) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
            - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs) := by
  obtain ⟨j, hjne, hjmod⟩ := exists_coincidence_of_H_zero a b i hH
  have hjdvd : p ∣ (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
      - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs) := by
    have h2 : (![a 0, a 1, a 2, b 0, b 1, b 2] j) ≡ (![a 0, a 1, a 2, b 0, b 1, b 2] i) [MOD p] :=
      (ZMod.natCast_eq_natCast_iff _ _ p).mp hjmod
    have h4 : (p : ℤ) ∣ (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℕ) : ℤ)
        - ((![a 0, a 1, a 2, b 0, b 1, b 2] j : ℕ) : ℤ)) := Nat.ModEq.dvd h2
    obtain ⟨k, hk⟩ := h4
    exact ⟨k.natAbs, by rw [hk, Int.natAbs_mul, Int.natAbs_natCast]⟩
  have hgcd : p ≤ Nat.gcd (p ^ e) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
      - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs) := by
    have h1 : p ∣ p ^ e := by simpa using pow_dvd_pow p he
    have h2 : p ∣ Nat.gcd (p ^ e) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
        - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs) := Nat.dvd_gcd h1 hjdvd
    have h3 : 0 < Nat.gcd (p ^ e) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
        - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs) :=
      Nat.gcd_pos_of_pos_left _ (pow_pos (Fact.out : p.Prime).pos e)
    exact Nat.le_of_dvd h3 h2
  refine le_trans hgcd (Finset.single_le_prod'
    (f := fun j => Nat.gcd (p ^ e) (((![a 0, a 1, a 2, b 0, b 1, b 2] i : ℤ)
      - (![a 0, a 1, a 2, b 0, b 1, b 2] j : ℤ)).natAbs))
    (fun j _ => Nat.succ_le_iff.mpr (Nat.gcd_pos_of_pos_left _
      (pow_pos (Fact.out : p.Prime).pos e))) (Finset.mem_erase.mpr ⟨hjne, Finset.mem_univ j⟩))

end Commons.NumberTheory.DirichletCharacter
