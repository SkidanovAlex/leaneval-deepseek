import Mathlib
import Submission.Work.KMTPlan.A6.ConcAux.Defs

namespace Work.KMTPlan.A6.ConcAux

open Polynomial Work.KMTPlan.A6.ConcAux

/-- Integer form of the `p`-content decomposition: every integer `a` is `p ^ c` times an integer
which is not divisible by `p` (unless `a = 0`). -/
lemma intContentDecomp (p : ℕ) [Fact p.Prime] (a : ℤ) :
    ∃ c : ℕ, ∃ v : ℤ, a = (p : ℤ) ^ c * v ∧ (v = 0 ∨ ¬ (p : ℤ) ∣ v) := by
  classical
  have key : ∀ n : ℕ, ∀ a : ℤ, a.natAbs = n →
      ∃ c : ℕ, ∃ v : ℤ, a = (p : ℤ) ^ c * v ∧ (v = 0 ∨ ¬ (p : ℤ) ∣ v) := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih a ha
    by_cases ha0 : a = 0
    · exact ⟨0, 0, by rw [ha0]; simp, Or.inl rfl⟩
    · by_cases hd : (p : ℤ) ∣ a
      · obtain ⟨b, hb⟩ := hd
        have hb0 : b ≠ 0 := by
          intro h
          exact ha0 (by rw [hb, h]; ring)
        have hlt : b.natAbs < n := by
          rw [← ha]
          have hb1 : 0 < b.natAbs := Int.natAbs_pos.mpr hb0
          have h1p : 1 < p := by
            have := (Fact.out (p := p.Prime)).two_le
            omega
          calc b.natAbs < (p : ℤ).natAbs * b.natAbs := by
                rw [Int.natAbs_natCast]
                exact lt_mul_of_one_lt_left hb1 h1p
            _ = ((p : ℤ) * b).natAbs := (Int.natAbs_mul (p : ℤ) b).symm
            _ = a.natAbs := by rw [← hb]
        obtain ⟨c, v, hv, hcond⟩ := ih b.natAbs hlt b rfl
        exact ⟨c + 1, v, by rw [hb, hv, pow_succ]; ring, hcond⟩
      · exact ⟨0, a, by simp, Or.inr hd⟩
  exact key a.natAbs a rfl

theorem exists_content_decomp (p : ℕ) [Fact p.Prime] (H : ℤ[X]) :
    ∃ c : ℕ, ∃ Ĝ : ℤ[X], H = C ((p : ℤ) ^ c) * Ĝ ∧ (Ĝ = 0 ∨ ∃ i, ¬ (p : ℤ) ∣ Ĝ.coeff i) := by
  classical
  by_cases hH : H = 0
  · exact ⟨0, 0, by rw [hH]; simp, Or.inl rfl⟩
  · have hcont : H.content ≠ 0 := fun h => hH (content_eq_zero_iff.mp h)
    obtain ⟨c, v, hv, hcond⟩ := intContentDecomp p H.content
    have hv0 : v ≠ 0 := by
      intro h
      exact hcont (by rw [hv, h, mul_zero])
    have hnv : ¬ (p : ℤ) ∣ v := by
      rcases hcond with h | h
      · exact absurd h hv0
      · exact h
    have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out (p := p.Prime))
    have hprim : ¬ C (p : ℤ) ∣ H.primPart := by
      intro hd
      exact hprime.not_isUnit
        ((isPrimitive_iff_isUnit_of_C_dvd.mp H.isPrimitive_primPart) (p : ℤ) hd)
    have hex : ∃ i, ¬ (p : ℤ) ∣ (H.primPart).coeff i := by
      by_contra hcon
      push Not at hcon
      exact hprim ((C_dvd_iff_dvd_coeff (p : ℤ) H.primPart).mpr hcon)
    obtain ⟨i, hi⟩ := hex
    refine ⟨c, C v * H.primPart, ?_, Or.inr ⟨i, ?_⟩⟩
    · calc H = C H.content * H.primPart := eq_C_content_mul_primPart H
        _ = C ((p : ℤ) ^ c * v) * H.primPart := by rw [hv]
        _ = (C ((p : ℤ) ^ c) * C v) * H.primPart := by rw [C_mul]
        _ = C ((p : ℤ) ^ c) * (C v * H.primPart) := by rw [mul_assoc]
    · rw [coeff_C_mul]
      intro hd
      rcases hprime.dvd_or_dvd hd with h1 | h1
      · exact hnv h1
      · exact hi h1

end Work.KMTPlan.A6.ConcAux
