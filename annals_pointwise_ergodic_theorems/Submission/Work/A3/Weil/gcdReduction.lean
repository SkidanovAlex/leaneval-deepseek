import Mathlib
import Submission.Work.A3.Weil.Defs

/-!
# Reducing a rational to a denominator in the window `[q/M, q]`

Given integers `a`, `q` with `q ≥ 1` and `gcd a q = 1`, and `M ≥ 1`, the rational number
`M · a/q` can be written as `b/q'` in lowest terms with

* `1 ≤ q'`, `q' ≤ q` and `q ≤ M q'`  (i.e. `q' ∈ [q/M, q]`),
* `gcd b q' = 1` (and hence also `gcd (-b) q' = 1`).

The construction is the natural one: with `d = gcd (M, q)`, `q = d q'`, `M = d m`, the choice
`q' = q/d`, `b = m·a` turns `M·a/q` into `(m·a)/(q/d)` with numerator and denominator coprime:
`gcd (m, q') = 1` because `gcd (d m, d q') = d`, and `gcd (a, q') = 1` because `q' ∣ q` and
`gcd (a,q) = 1`.  Since `gcd(M,q) = gcd(Ma, q)` under `gcd(a,q) = 1`, the denominator `q/gcd(M,q)`
is exactly the reduced denominator of `Ma/q`, so the bound `q' ≤ q` is equality with `q` iff
`gcd(M,q) = 1`, and `q ≤ M q'` is the statement `gcd(M,q) ≤ M`.

This is the arithmetic reduction used in the Dirichlet-approximation step of the circle method:
it replaces a rational `a/q` with `q` large by an *equivalent* fraction whose denominator is
smaller by the factor `gcd(M,q)` but still `≥ q/M`.
-/

namespace Work.A3.Weil

theorem gcdReduction (M : ℕ) (a q : ℤ) (hq : 1 ≤ q) (hcop : IsCoprime a q) (hM : 1 ≤ M) :
    ∃ (b : ℤ) (q' : ℕ), 1 ≤ q' ∧ (q' : ℤ) ≤ q ∧ q ≤ (M : ℤ) * (q' : ℤ) ∧
      IsCoprime b (q' : ℤ) ∧ IsCoprime (-b) (q' : ℤ) ∧
      (b : ℝ) / (q' : ℝ) = (M : ℝ) * ((a : ℝ) / (q : ℝ)) := by
  -- Normalise the denominator to a natural number.
  have hq0 : (0 : ℤ) ≤ q := by omega
  let qn : ℕ := q.toNat
  have hqn : (qn : ℤ) = q := Int.toNat_of_nonneg hq0
  have hqnab : q.natAbs = qn := by
    have h1 : (q.natAbs : ℤ) = q := Int.natAbs_of_nonneg hq0
    have h2 : (q.natAbs : ℤ) = (qn : ℤ) := by rw [h1, ← hqn]
    exact_mod_cast h2
  have hqn_pos : 0 < qn := by omega
  -- Coprimality of `a` and `qn`.
  have hcop_an_qn : Nat.Coprime a.natAbs qn := by
    have h := Int.isCoprime_iff_gcd_eq_one.mp hcop
    rw [Int.gcd_eq_natAbs, hqnab] at h
    exact h
  -- The construction: `d = gcd (M, qn)`, `M = m * d`, `qn = d * q'`, `b = m * a`.
  let d : ℕ := M.gcd qn
  have hd_dvd_M : d ∣ M := Nat.gcd_dvd_left M qn
  have hd_dvd_qn : d ∣ qn := Nat.gcd_dvd_right M qn
  have hMpos : 0 < M := by omega
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd_M hMpos
  let m : ℕ := M / d
  let q' : ℕ := qn / d
  have hmd : m * d = M := Nat.div_mul_cancel hd_dvd_M
  have hq'd : d * q' = qn := Nat.mul_div_cancel' hd_dvd_qn
  have hd_le_qn : d ≤ qn := Nat.le_of_dvd hqn_pos hd_dvd_qn
  have hq'_pos : 0 < q' := Nat.div_pos hd_le_qn hd_pos
  have hq'_ge : 1 ≤ q' := by omega
  have hq'_le_qn : q' ≤ qn := Nat.div_le_self qn d
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hMpos hd_dvd_M) hd_pos
  have hm_ge : 1 ≤ m := by omega
  -- `m` and `q'` are coprime, because `gcd (d * m) (d * q') = d = gcd M qn`.
  have hq'dvd : q' ∣ qn := ⟨d, by rw [← hq'd, mul_comm]⟩
  have hcop_a_q' : Nat.Coprime a.natAbs q' := Nat.Coprime.coprime_dvd_right hq'dvd hcop_an_qn
  have hcop_m_q' : Nat.Coprime m q' := by
    have h2 : (d * m).gcd (d * q') = d * (m.gcd q') := Nat.gcd_mul_left d m q'
    rw [Nat.mul_comm d m, hmd, hq'd] at h2
    have h2' : d * (m.gcd q') = d * 1 := by rw [← h2, mul_one]
    exact Nat.mul_left_cancel hd_pos h2'
  -- The product identity `m * qn = M * q'` behind the value of the fraction.
  have hmq : m * qn = M * q' := by
    calc m * qn = m * (d * q') := by rw [← hq'd]
      _ = (m * d) * q' := by ring
      _ = M * q' := by rw [hmd]
  -- The size constraint `q ≤ M * q'`.
  have hle_nat : qn ≤ M * q' := by
    calc qn ≤ m * qn := Nat.le_mul_of_pos_left qn hm_pos
      _ = m * (d * q') := by rw [← hq'd]
      _ = (m * d) * q' := by ring
      _ = M * q' := by rw [hmd]
  have hq'le : (q' : ℤ) ≤ q := by
    have h : (q' : ℤ) ≤ (qn : ℤ) := by exact_mod_cast hq'_le_qn
    rwa [hqn] at h
  have hMq : q ≤ (M : ℤ) * (q' : ℤ) := by
    have h : (qn : ℤ) ≤ (M : ℤ) * (q' : ℤ) := by exact_mod_cast hle_nat
    rwa [hqn] at h
  -- Coprimality of the numerator.
  have hm_int : IsCoprime (m : ℤ) (q' : ℤ) := hcop_m_q'.isCoprime
  have ha_int : IsCoprime a (q' : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact hcop_a_q'
  have hb_int : IsCoprime ((m : ℤ) * a) (q' : ℤ) := hm_int.mul_left ha_int
  refine ⟨(m : ℤ) * a, q', hq'_ge, hq'le, hMq, hb_int, hb_int.neg_left, ?_⟩
  -- The value of the fraction: `(m * a) / q' = M * (a / q)`.
  have hmqZ : (m : ℤ) * (qn : ℤ) = (M : ℤ) * (q' : ℤ) := by exact_mod_cast hmq
  have hbq : ((m : ℤ) * a) * q = (M : ℤ) * a * (q' : ℤ) := by
    rw [← hqn]
    calc ((m : ℤ) * a) * (qn : ℤ) = ((m : ℤ) * (qn : ℤ)) * a := by ring
      _ = ((M : ℤ) * (q' : ℤ)) * a := by rw [hmqZ]
      _ = (M : ℤ) * a * (q' : ℤ) := by ring
  have hR : (((m : ℤ) * a : ℤ) : ℝ) * (q : ℝ) = (M : ℝ) * (a : ℝ) * (q' : ℝ) := by
    exact_mod_cast hbq
  have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hq'ne : (q' : ℝ) ≠ 0 := by exact_mod_cast (show q' ≠ 0 by omega)
  have hMa : (M : ℝ) * ((a : ℝ) / (q : ℝ)) = ((M : ℝ) * (a : ℝ)) / (q : ℝ) := by ring
  rw [hMa, div_eq_div_iff hq'ne hqne]
  exact hR

end Work.A3.Weil
