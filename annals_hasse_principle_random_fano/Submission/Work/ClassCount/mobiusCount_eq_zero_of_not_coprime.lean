import Mathlib
import Submission.Work.HP.PFCountDefs

namespace Work.ClassCount

/-- If `k` is not coprime to `W ≥ 2`, then the `k`-th Möbius summand vanishes: a prime `p | W`
with `p | k` would force `p | b i` for every `i` from `W | k z i - b i`, contradicting the
hypothesis that `b` is primitive at every prime divisor of `W`. -/
theorem mobiusCount_eq_zero_of_not_coprime (d n : ℕ) (a : Work.HP.Mon d n → ℤ)
    (b : Fin (n + 1) → ℤ) (W k : ℕ) (α R : ℝ)
    (hW2 : 2 ≤ W)
    (hbprim : ∀ p : ℕ, p.Prime → p ∣ W → ∃ i, ¬ (p : ℤ) ∣ b i)
    (hkn : ¬ Nat.Coprime k W) :
    Work.HP.mobiusCount d n a b W k α R = 0 := by
  -- `¬ Coprime k W` with `W ≥ 2` gives a prime `p` dividing both `k` and `W`.
  obtain ⟨p, hpprime, hpW, hpk⟩ : ∃ p, p.Prime ∧ p ∣ W ∧ p ∣ k := by
    have hg : Nat.gcd k W ≠ 1 := fun h => hkn (Nat.coprime_iff_gcd_eq_one.mpr h)
    obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd hg
    exact ⟨p, hp.1, dvd_trans hp.2 (Nat.gcd_dvd_right k W),
      dvd_trans hp.2 (Nat.gcd_dvd_left k W)⟩
  -- `b` is primitive at `p`: some coordinate is not divisible by `p`.
  obtain ⟨i, hi⟩ := hbprim p hpprime hpW
  -- Hence the defining set of `mobiusCount` is empty.
  have hempty : {z : Fin (n + 1) → ℤ |
      z ≠ 0 ∧ (∀ j, (W : ℤ) ∣ (k : ℤ) * z j - b j) ∧
        Work.HP.eNorm z ≤ R / (k : ℝ) ∧
        Work.HP.toR a ∈ Work.HP.Cgam (Work.HP.toR (Work.HP.veronese d n z)) α} = ∅ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, hcong, -, -⟩
    have h1 : (p : ℤ) ∣ (k : ℤ) * z i - b i :=
      dvd_trans (by exact_mod_cast hpW) (hcong i)
    have h2 : (p : ℤ) ∣ (k : ℤ) * z i :=
      dvd_mul_of_dvd_left (by exact_mod_cast hpk) (z i)
    have h3 : (p : ℤ) ∣ (k : ℤ) * z i - ((k : ℤ) * z i - b i) := dvd_sub h2 h1
    have h4 : (k : ℤ) * z i - ((k : ℤ) * z i - b i) = b i := by ring
    exact hi (h4 ▸ h3)
  unfold Work.HP.mobiusCount
  rw [hempty, Set.ncard_empty]

end Work.ClassCount
