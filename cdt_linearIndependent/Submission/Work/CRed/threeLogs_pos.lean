import Mathlib
import Submission.Helpers
import Submission.Commons.Data.Int.oneAddInvPowEq
import Submission.Commons.Data.Rat.den_mul_self
import Submission.Transcendence.LindemannC

/-!
# `threeLogs_pos`

`1, log (1 + 1/m), log (1 + 1/n)` are `ℚ`-linearly independent for distinct
positive integers `m ≠ n`.

This is the `d = 0` slice of Calegari–Dimitrov–Tang Theorem C
(arXiv:2408.15403) *without* the large-gap hypothesis `10⁶·|m−n| < |n|`:
for **positive** `m, n` the elementary multiplicative crux
(`Commons.Data.Int.oneAddInvPowEq_core`) never needs the gap — the gap only
excludes the degenerate alternative `(1+1/m)(1+1/n) = 1`, i.e.
`m + n + 1 = 0`, which is already impossible for `m, n ≥ 1`.

The route is the one of `Submission.CDT.twoLogs_three_li`: clear a
`ℚ`-relation to an integer relation `A + B·z₁ + C·z₂ = 0`, exponentiate to
`e^A·u^B·v^C = 1` with `u, v ∈ ℚ`, kill `A ≠ 0` by Lindemann–Weierstrass
(`e^A` would then be transcendental, yet `e^A = (u^B v^C)⁻¹ ∈ ℚ`), and finish
with the multiplicative crux.
-/

namespace Work.CRed

open scoped BigOperators

/-- Denominator clearing over `ℝ`: for a rational `q` and naturals `u, v`,
`(q.den * (u*v)) * q = (u*v) * q.num`, all cast to `ℝ`. -/
lemma clear_coeff_real (q : ℚ) (u v : ℕ) :
    (((q.den * (u * v) : ℕ) : ℝ) * (q : ℝ)) = ((((u * v : ℕ) : ℤ) * q.num : ℤ) : ℝ) := by
  have hq : (((q.den * (u * v) : ℕ) : ℚ) * q) = (((u * v : ℕ) : ℤ) * q.num : ℤ) := by
    calc (((q.den * (u * v) : ℕ) : ℚ) * q)
        = ((q.den : ℚ) * (((u * v) : ℕ) : ℚ)) * q := by rw [Nat.cast_mul]
      _ = ((q.den : ℚ) * q) * ((u * v : ℕ) : ℚ) := by ring
      _ = (q.num : ℚ) * (((u * v : ℕ) : ℚ)) := by rw [Commons.Data.Rat.den_mul_self q]
      _ = (((u * v : ℕ) : ℤ) * q.num : ℤ) := by
            have hcast : (((u * v : ℕ) : ℤ) : ℚ) = ((u * v : ℕ) : ℚ) := by simp
            rw [Int.cast_mul, hcast]; ring
  exact_mod_cast hq

/-- **Multiplicative independence of `1 + 1/m` and `1 + 1/n`** for distinct
positive integers `m ≠ n` (no gap hypothesis): if
`(1 + 1/m)^b · (1 + 1/n)^c = 1` in `ℚ` with `b, c ∈ ℤ`, then `b = c = 0`. -/
lemma one_add_inv_pow_nat (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n)
    (b c : ℤ) (h : ((1 + 1 / (m : ℚ)) ^ b) * ((1 + 1 / (n : ℚ)) ^ c) = 1) :
    b = 0 ∧ c = 0 := by
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hX : (1 + 1 / (m : ℚ)) = ((m + 1 : ℕ) : ℚ) / ((m : ℕ) : ℚ) := by
    push_cast; field_simp
  have hY : (1 + 1 / (n : ℚ)) = ((n + 1 : ℕ) : ℚ) / ((n : ℕ) : ℚ) := by
    push_cast; field_simp
  rw [hX, hY] at h
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · exact ⟨hb, hc⟩
    · exfalso
      have h1 : (((n + 1 : ℕ) : ℚ) / ((n : ℕ) : ℚ)) ^ c = 1 := by simpa [hb] using h
      have h2 := Commons.Data.Int.oneAddInvPowEq_zpow_eq_one (C := n + 1) (D := n)
        (by omega) (Or.inl rfl) c h1
      exact hc h2
  · by_cases hc : c = 0
    · exfalso
      have h1 : (((m + 1 : ℕ) : ℚ) / ((m : ℕ) : ℚ)) ^ b = 1 := by simpa [hc] using h
      have h2 := Commons.Data.Int.oneAddInvPowEq_zpow_eq_one (C := m + 1) (D := m)
        (by omega) (Or.inl rfl) b h1
      exact hb h2
    · exfalso
      have hcore := Commons.Data.Int.oneAddInvPowEq_core (A := m + 1) (B := m) (C := n + 1)
        (D := n) (by omega) (by omega) (by omega) (by omega) (Or.inl rfl) (Or.inl rfl)
        b c hb hc h
      rcases hcore with hXY | hXY1
      · have h1 : (1 + 1 / (m : ℚ)) = (1 + 1 / (n : ℚ)) := by
          rw [hX, hY]; exact hXY
        have h2 : (1 : ℚ) / (m : ℚ) = 1 / (n : ℚ) := by linarith
        have h3 : (n : ℚ) = (m : ℚ) := by
          have h4 := (div_eq_div_iff hmq hnq).mp h2
          simpa using h4
        exact hmn (by exact_mod_cast h3.symm : m = n)
      · have h1 : (1 + 1 / (m : ℚ)) * (1 + 1 / (n : ℚ)) = 1 := by
          rw [hX, hY]; exact hXY1
        have h2 : (m : ℚ) + (n : ℚ) + 1 = 0 := by
          field_simp at h1
          linarith
        have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
        have hn1 : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
        linarith

theorem threeLogs_pos (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≠ n) :
    LinearIndependent ℚ ![1, Real.log (1 + 1 / (m : ℝ)), Real.log (1 + 1 / (n : ℝ))] := by
  rw [Submission.Helpers.linearIndependent_cons3_iff]
  intro a b c habc
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have huR : (0 : ℝ) < 1 + 1 / (m : ℝ) := by positivity
  have hvR : (0 : ℝ) < 1 + 1 / (n : ℝ) := by positivity
  have habc' : (a : ℝ) + (b : ℝ) * Real.log (1 + 1 / (m : ℝ))
      + (c : ℝ) * Real.log (1 + 1 / (n : ℝ)) = 0 := by
    simpa [Algebra.smul_def] using habc
  -- clear denominators
  let D : ℕ := a.den * b.den * c.den
  let A : ℤ := ((b.den * c.den : ℕ) : ℤ) * a.num
  let B : ℤ := ((a.den * c.den : ℕ) : ℤ) * b.num
  let C : ℤ := ((a.den * b.den : ℕ) : ℤ) * c.num
  have hA : (A : ℝ) = (D : ℝ) * (a : ℝ) := by
    rw [show (D : ℝ) = (((a.den * (b.den * c.den) : ℕ) : ℝ)) by
        dsimp [D]; congr 1; ring]
    exact (clear_coeff_real a b.den c.den).symm
  have hB : (B : ℝ) = (D : ℝ) * (b : ℝ) := by
    rw [show (D : ℝ) = (((b.den * (a.den * c.den) : ℕ) : ℝ)) by
        dsimp [D]; congr 1; ring]
    exact (clear_coeff_real b a.den c.den).symm
  have hC : (C : ℝ) = (D : ℝ) * (c : ℝ) := by
    rw [show (D : ℝ) = (((c.den * (a.den * b.den) : ℕ) : ℝ)) by
        dsimp [D]; congr 1; ring]
    exact (clear_coeff_real c a.den b.den).symm
  have hrelZ : (A : ℝ) + (B : ℝ) * Real.log (1 + 1 / (m : ℝ))
      + (C : ℝ) * Real.log (1 + 1 / (n : ℝ)) = 0 := by
    calc
      (A : ℝ) + (B : ℝ) * Real.log (1 + 1 / (m : ℝ))
          + (C : ℝ) * Real.log (1 + 1 / (n : ℝ))
          = (D : ℝ) * (a : ℝ) + (D : ℝ) * (b : ℝ) * Real.log (1 + 1 / (m : ℝ))
              + (D : ℝ) * (c : ℝ) * Real.log (1 + 1 / (n : ℝ)) := by rw [hA, hB, hC]
      _ = (D : ℝ) * ((a : ℝ) + (b : ℝ) * Real.log (1 + 1 / (m : ℝ))
              + (c : ℝ) * Real.log (1 + 1 / (n : ℝ))) := by ring
      _ = 0 := by rw [habc']; ring
  -- exponentiate
  have e1 : Real.exp ((B : ℝ) * Real.log (1 + 1 / (m : ℝ)))
      = (1 + 1 / (m : ℝ)) ^ B := by
    have key : (B : ℝ) * Real.log (1 + 1 / (m : ℝ))
        = Real.log (1 + 1 / (m : ℝ)) * (B : ℝ) := mul_comm _ _
    rw [key, Real.exp_mul, Real.exp_log huR, Real.rpow_intCast]
  have e2 : Real.exp ((C : ℝ) * Real.log (1 + 1 / (n : ℝ)))
      = (1 + 1 / (n : ℝ)) ^ C := by
    have key : (C : ℝ) * Real.log (1 + 1 / (n : ℝ))
        = Real.log (1 + 1 / (n : ℝ)) * (C : ℝ) := mul_comm _ _
    rw [key, Real.exp_mul, Real.exp_log hvR, Real.rpow_intCast]
  have hBig : Real.exp ((A : ℝ)) * ((1 + 1 / (m : ℝ)) ^ B * (1 + 1 / (n : ℝ)) ^ C)
      = 1 := by
    have hsum : (A : ℝ) + ((B : ℝ) * Real.log (1 + 1 / (m : ℝ))
        + (C : ℝ) * Real.log (1 + 1 / (n : ℝ))) = 0 := by linarith [hrelZ]
    calc Real.exp ((A : ℝ)) * ((1 + 1 / (m : ℝ)) ^ B * (1 + 1 / (n : ℝ)) ^ C)
        = Real.exp ((A : ℝ)) * (Real.exp ((B : ℝ) * Real.log (1 + 1 / (m : ℝ)))
            * Real.exp ((C : ℝ) * Real.log (1 + 1 / (n : ℝ)))) := by rw [e1, e2]
      _ = Real.exp ((A : ℝ) + ((B : ℝ) * Real.log (1 + 1 / (m : ℝ))
            + (C : ℝ) * Real.log (1 + 1 / (n : ℝ)))) := by
            rw [← Real.exp_add, ← Real.exp_add]
      _ = 1 := by rw [hsum, Real.exp_zero]
  -- the rational value of `u^B * v^C`
  let Q : ℚ := (1 + 1 / (m : ℚ)) ^ B * (1 + 1 / (n : ℚ)) ^ C
  have hQcast : (Q : ℝ) = (1 + 1 / (m : ℝ)) ^ B * (1 + 1 / (n : ℝ)) ^ C := by
    dsimp only [Q]
    push_cast
    ring
  have hBigQ : Real.exp ((A : ℝ)) * (Q : ℝ) = 1 := by
    rw [hQcast]; exact hBig
  have hQ0 : (Q : ℝ) ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hBigQ
    exact one_ne_zero hBigQ.symm
  have hexp : Real.exp ((A : ℝ)) = ((Q⁻¹ : ℚ) : ℝ) := by
    calc Real.exp ((A : ℝ)) = Real.exp ((A : ℝ)) * (Q : ℝ) * (Q : ℝ)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hQ0, mul_one]
      _ = 1 * (Q : ℝ)⁻¹ := by rw [hBigQ]
      _ = ((Q⁻¹ : ℚ) : ℝ) := by rw [one_mul, Rat.cast_inv]
  -- kill `A ≠ 0` by Lindemann–Weierstrass
  have hA0 : A = 0 := by
    by_contra hAne
    have hAlg : IsAlgebraic ℚ (Complex.exp ((A : ℂ))) := by
      have hcast : Complex.exp ((A : ℂ)) = ((Q⁻¹ : ℚ) : ℂ) := by
        have h1 : Complex.exp ((A : ℂ)) = ((Real.exp ((A : ℝ))) : ℂ) := by
          rw [show ((A : ℂ)) = (((A : ℝ)) : ℂ) by norm_num, Complex.ofReal_exp]
        rw [h1, hexp]
        norm_num
      rw [hcast]
      exact Submission.Transcendence.isAlgebraic_rat_complex (Q⁻¹)
    have htr : Transcendental ℚ (Complex.exp ((A : ℂ))) :=
      Submission.Transcendence.cexp_transcendental_of_algebraic_ne_zero
        (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) ((A : ℤ) : ℚ))
        (by exact_mod_cast hAne)
    exact htr hAlg
  -- multiplicative crux
  have hpow : ((1 + 1 / (m : ℚ)) ^ B) * ((1 + 1 / (n : ℚ)) ^ C) = 1 := by
    have h1 : (Q : ℝ) = 1 := by
      have h2 := hBigQ
      rw [hA0] at h2
      simpa using h2
    exact_mod_cast h1
  obtain ⟨hB0, hC0⟩ := one_add_inv_pow_nat m n hm hn hmn B C hpow
  -- recover the rational coefficients
  have hD0 : (D : ℝ) ≠ 0 := by
    have hDnz : D ≠ 0 := by
      dsimp [D]
      exact Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos a.den_pos b.den_pos) c.den_pos)
    exact_mod_cast hDnz
  have ha0 : a = 0 := by
    have hA' : (A : ℝ) = 0 := by rw [hA0]; simp
    rw [hA] at hA'
    have hz : (a : ℝ) = 0 := (mul_eq_zero.mp hA').resolve_left hD0
    exact_mod_cast hz
  have hb0 : b = 0 := by
    have hB' : (B : ℝ) = 0 := by rw [hB0]; simp
    rw [hB] at hB'
    have hz : (b : ℝ) = 0 := (mul_eq_zero.mp hB').resolve_left hD0
    exact_mod_cast hz
  have hc0 : c = 0 := by
    have hC' : (C : ℝ) = 0 := by rw [hC0]; simp
    rw [hC] at hC'
    have hz : (c : ℝ) = 0 := (mul_eq_zero.mp hC').resolve_left hD0
    exact_mod_cast hz
  exact ⟨ha0, hb0, hc0⟩

end Work.CRed
