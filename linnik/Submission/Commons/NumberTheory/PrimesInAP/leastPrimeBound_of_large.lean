import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.PrimesInAP

/-- Auxiliary arithmetic fact: for `m ≥ 0`, `x * m ≤ |x| * m + 1`. -/
private lemma mul_le_abs_mul_add_one (x m : ℝ) (hm : 0 ≤ m) : x * m ≤ |x| * m + 1 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]; linarith
  · have h1 : x * m ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt hx) hm
    have h2 : 0 ≤ |x| * m := mul_nonneg (abs_nonneg x) hm
    linarith

/-- If `p ≡ a [MOD d]` and `a < d` then `a ≤ p`. -/
private lemma le_of_modEq_lt {p a d : ℕ} (h : p ≡ a [MOD d]) (ha : a < d) : a ≤ p := by
  have h' : p % d = a := by
    have : p % d = a % d := h
    rw [this, Nat.mod_eq_of_lt ha]
  calc a = p % d := h'.symm
    _ ≤ p := Nat.mod_le p d

/-- **Linnik's theorem: extension from large to all moduli.**
If every reduced progression `a mod d` with `q₀ ≤ d` contains a prime
`p ≤ cH · d ^ (11/2)`, then there is a single constant `c > 0` that works for
*all* moduli `d` (with `a ≤ p` for free). -/
theorem leastPrimeBound_of_large {q₀ : ℕ} {cH : ℝ}
    (hH : ∀ ⦃a d : ℕ⦄, q₀ ≤ d → 0 < a → a < d → a.Coprime d →
      ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD d] ∧ (p : ℝ) ≤ cH * (d : ℝ) ^ (5.5 : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ⦃a d : ℕ⦄, 0 < a → a < d → a.Coprime d →
      ∃ p : ℕ, a ≤ p ∧ (p : ℝ) ≤ c * (d : ℝ) ^ (5.5 : ℝ) ∧ p.Prime ∧ p ≡ a [MOD d] := by
  -- A fixed prime `M` larger than `q₀`, used to lift small moduli to large ones.
  obtain ⟨M, hMq, hMprime⟩ := Nat.exists_infinite_primes (q₀ + 1)
  have hqM : q₀ < M := Nat.lt_of_succ_le hMq
  have hM2 : 2 ≤ M := hMprime.two_le
  have hMpos : 0 < M := by omega
  have hM1R : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show (1 : ℕ) ≤ M by omega)
  have hMrpow1 : (1 : ℝ) ≤ (M : ℝ) ^ (5.5 : ℝ) := Real.one_le_rpow hM1R (by norm_num)
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  refine ⟨|cH| * (M : ℝ) ^ (5.5 : ℝ) + 1, by positivity, ?_⟩
  intro a d ha hd hcop
  have hd2 : 2 ≤ d := by omega
  by_cases hdq : q₀ ≤ d
  · -- Large moduli: use `hH` directly.
    obtain ⟨p, hpp, hpm, hpb⟩ := hH hdq ha hd hcop
    refine ⟨p, le_of_modEq_lt hpm hd, ?_, hpp, hpm⟩
    have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have hcHc : cH ≤ |cH| * (M : ℝ) ^ (5.5 : ℝ) + 1 := by
      have h1 : cH ≤ |cH| := le_abs_self cH
      have h2 : |cH| ≤ |cH| * (M : ℝ) ^ (5.5 : ℝ) := by
        have := mul_le_mul_of_nonneg_left hMrpow1 (abs_nonneg cH)
        simpa using this
      linarith
    calc (p : ℝ) ≤ cH * (d : ℝ) ^ (5.5 : ℝ) := hpb
      _ ≤ (|cH| * (M : ℝ) ^ (5.5 : ℝ) + 1) * (d : ℝ) ^ (5.5 : ℝ) :=
            mul_le_mul_of_nonneg_right hcHc (Real.rpow_nonneg hdnn _)
  · -- Small moduli: lift `d` to `D = d * M ≥ q₀`.
    have hDq : q₀ ≤ d * M := by
      have h1 : M ≤ d * M := Nat.le_mul_of_pos_left M (by omega : 0 < d)
      exact le_trans (le_of_lt hqM) h1
    have haD : a < d * M := by
      have h1 : d ≤ d * M := Nat.le_mul_of_pos_right d hMpos
      exact lt_of_lt_of_le hd h1
    have haCopD : a.Coprime (d * M) := by
      rw [Nat.coprime_mul_iff_right]
      refine ⟨hcop, ?_⟩
      have hnotdvd : ¬ M ∣ a := by
        intro hdiv
        have := Nat.le_of_dvd ha hdiv
        omega
      exact ((Nat.Prime.coprime_iff_not_dvd hMprime).mpr hnotdvd).symm
    obtain ⟨p, hpp, hpmD, hpb⟩ := hH hDq ha haD haCopD
    have hpm : p ≡ a [MOD d] := Nat.ModEq.of_dvd (dvd_mul_right d M) hpmD
    have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    refine ⟨p, le_of_modEq_lt hpm hd, ?_, hpp, hpm⟩
    have hDcast : (((d * M : ℕ)) : ℝ) ^ (5.5 : ℝ)
        = (d : ℝ) ^ (5.5 : ℝ) * (M : ℝ) ^ (5.5 : ℝ) := by
      rw [Nat.cast_mul, Real.mul_rpow hdnn hMnn]
    calc (p : ℝ) ≤ cH * (((d * M : ℕ)) : ℝ) ^ (5.5 : ℝ) := hpb
      _ = cH * ((d : ℝ) ^ (5.5 : ℝ) * (M : ℝ) ^ (5.5 : ℝ)) := by rw [hDcast]
      _ = (cH * (M : ℝ) ^ (5.5 : ℝ)) * (d : ℝ) ^ (5.5 : ℝ) := by ring
      _ ≤ (|cH| * (M : ℝ) ^ (5.5 : ℝ) + 1) * (d : ℝ) ^ (5.5 : ℝ) :=
            mul_le_mul_of_nonneg_right
              (mul_le_abs_mul_add_one cH ((M : ℝ) ^ (5.5 : ℝ)) (Real.rpow_nonneg hMnn _))
              (Real.rpow_nonneg hdnn _)

end Commons.NumberTheory.PrimesInAP