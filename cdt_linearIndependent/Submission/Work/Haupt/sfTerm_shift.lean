import Mathlib
import Submission.Work.Haupt.qp_defs
import Submission.Work.Haupt.sf_aux
import Submission.Work.Haupt.sf_helpers

/-!
# The shift identity for the semi-finite summand

`sfTerm q z m n = qhalfInt q n * z ^ n / qpInt (q ^ (m+1)) q n` is the summand of the
semi-finite sum `∑_{n ∈ ℤ} q^{n(n-1)/2} z^n / (q^{m+1};q)_n` appearing in the
semi-finite proof of the Jacobi triple product.

Here we relate the term with index `N - m` (`N : ℕ`) to the `N`-th term of the
Jacobi/`q`-binomial series `∑_N qhalf q N * w^N / qpNat q q N`:

`sfTerm q z m (N - m) = ( (q;q)_m * qhalf q (m+1) * z^{-m} ) * ( qhalf q N * (q^{-m} z)^N / (q;q)_N )`.

The proof is a pure `q`-power bookkeeping computation: the hard `q`-contents are the
two identities `qhalf q (m+1) * qhalf q N * q^{-mN} = qhalfInt q (N - m)` and
`(qpInt (q^{m+1}) q (N-m))⁻¹ = (q;q)_m / (q;q)_N`.
-/

open scoped BigOperators

namespace Work.Haupt

/-- `q ^ a * q ^ b * q ^ c = q ^ (a + b + c)` for `q ≠ 0` and ℤ-exponents. -/
lemma sfShift_zpow_three {q : ℂ} (hq : q ≠ 0) (a b c : ℤ) :
    q ^ a * q ^ b * q ^ c = q ^ (a + b + c) := by
  rw [zpow_add₀ hq (a + b) c, zpow_add₀ hq a b]

/-- The `zpow` form of the base of `qpInt` in `sfTerm`: `q ^ (m + 1)` with a ℤ-exponent. -/
lemma sfShift_base (q : ℂ) (m : ℕ) : q ^ ((m : ℤ) + 1) = q ^ (m + 1) := by
  rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by omega, zpow_natCast]

/-- For `m ≤ N`:  `qhalf q (m+1) * qhalf q N * q^{-mN} = qhalf q (N - m)`. -/
lemma sfShift_qhalf_ge {q : ℂ} (hq : q ≠ 0) {m N : ℕ} (h : m ≤ N) :
    qhalf q (m + 1) * qhalf q N * q ^ (-((m * N : ℕ) : ℤ)) = qhalf q (N - m) := by
  have h1 : qhalf q N = qhalf q (N - m) * qhalf q m * q ^ ((N - m) * m) := by
    have := qhalf_add q (N - m) m
    rwa [Nat.sub_add_cancel h] at this
  have h3 : (q : ℂ) ^ (m * m) * q ^ ((N - m) * m) * q ^ (-((m * N : ℕ) : ℤ)) = 1 := by
    have e : ((m * m : ℕ) : ℤ) + (((N - m) * m : ℕ) : ℤ) + (-((m * N : ℕ) : ℤ)) = 0 := by
      have hm : ((N - m : ℕ) : ℤ) = (N : ℤ) - (m : ℤ) := Nat.cast_sub h
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, hm]
      ring
    rw [← zpow_natCast q (m * m), ← zpow_natCast q ((N - m) * m),
      ← zpow_add₀ hq, ← zpow_add₀ hq, e, zpow_zero]
  calc qhalf q (m + 1) * qhalf q N * q ^ (-((m * N : ℕ) : ℤ))
      = qhalf q (N - m)
          * (q ^ (m * m) * q ^ ((N - m) * m) * q ^ (-((m * N : ℕ) : ℤ))) := by
        rw [h1,
          show qhalf q (m + 1) * (qhalf q (N - m) * qhalf q m * q ^ ((N - m) * m))
                * q ^ (-((m * N : ℕ) : ℤ))
              = qhalf q (N - m) * (qhalf q m * qhalf q (m + 1))
                * (q ^ ((N - m) * m) * q ^ (-((m * N : ℕ) : ℤ))) from by ring,
          qhalf_mul_succ]
        ring
    _ = qhalf q (N - m) * 1 := by rw [h3]
    _ = qhalf q (N - m) := by ring

/-- For `N ≤ m`:  `qhalf q (m+1) * qhalf q N * q^{-mN} = qhalf q (m - N + 1)`. -/
lemma sfShift_qhalf_le {q : ℂ} (hq : q ≠ 0) {m N : ℕ} (h : N ≤ m) :
    qhalf q (m + 1) * qhalf q N * q ^ (-((m * N : ℕ) : ℤ)) = qhalf q (m - N + 1) := by
  have h1 : qhalf q (m + 1)
      = qhalf q (N + 1) * qhalf q (m - N) * q ^ ((N + 1) * (m - N)) := by
    have := qhalf_add q (N + 1) (m - N)
    rwa [show N + 1 + (m - N) = m + 1 from by omega] at this
  have h2 : (q : ℂ) ^ (N * N) * q ^ ((N + 1) * (m - N)) * q ^ (-((m * N : ℕ) : ℤ))
      = q ^ ((m - N : ℕ) : ℤ) := by
    have e : ((N * N : ℕ) : ℤ) + (((N + 1) * (m - N) : ℕ) : ℤ) + (-((m * N : ℕ) : ℤ))
        = ((m - N : ℕ) : ℤ) := by
      push_cast
      simp only [Nat.cast_sub h]
      ring
    rw [← zpow_natCast q (N * N), ← zpow_natCast q ((N + 1) * (m - N)),
      ← zpow_add₀ hq, ← zpow_add₀ hq, e]
  calc qhalf q (m + 1) * qhalf q N * q ^ (-((m * N : ℕ) : ℤ))
      = qhalf q (m - N)
          * (q ^ (N * N) * q ^ ((N + 1) * (m - N)) * q ^ (-((m * N : ℕ) : ℤ))) := by
        rw [h1,
          show qhalf q (N + 1) * qhalf q (m - N) * q ^ ((N + 1) * (m - N)) * qhalf q N
                * q ^ (-((m * N : ℕ) : ℤ))
              = qhalf q (m - N) * (qhalf q N * qhalf q (N + 1))
                * q ^ ((N + 1) * (m - N)) * q ^ (-((m * N : ℕ) : ℤ)) from by ring,
          qhalf_mul_succ]
        ring
    _ = qhalf q (m - N) * q ^ ((m - N : ℕ) : ℤ) := by rw [h2]
    _ = qhalf q (m - N + 1) := by
        rw [zpow_natCast, ← qhalf_succ]

/-- The `q`-factorial quotient: `1/(q^{m+1};q)_{N-m} = (q;q)_m/(q;q)_N`. -/
lemma sfShift_inv_qpInt {q : ℂ} (hqn : ‖q‖ < 1) (m N : ℕ) :
    (qpInt (q ^ ((m : ℤ) + 1)) q ((N : ℤ) - m))⁻¹ = qpNat q q m / qpNat q q N := by
  rcases le_or_gt m N with h | h
  · have hD : qpNat q q N = qpNat q q m * qpNat (q ^ (m + 1)) q (N - m) := by
      have := qpNat_self_add q m (N - m)
      rwa [Nat.sub_add_cancel h] at this
    have hA : qpNat q q m ≠ 0 := qpNat_self_ne_zero hqn m
    rw [show ((N : ℤ) - m) = ((N - m : ℕ) : ℤ) by omega, qpInt_ofNat, sfShift_base, hD,
      div_eq_mul_inv, mul_inv, ← mul_assoc, mul_inv_cancel₀ hA, one_mul]
  · have hD : qpNat q q m = qpNat q q N * qpNat (q ^ (N + 1)) q (m - N) := by
      have := qpNat_self_add q N (m - N)
      rwa [Nat.sub_add_cancel (le_of_lt h)] at this
    have hB : qpNat q q N ≠ 0 := qpNat_self_ne_zero hqn N
    rw [show ((N : ℤ) - m) = -((m - N : ℕ) : ℤ) by omega,
      qpInt_neg_eq (show m - N ≤ m by omega)]
    have hexp : ((m : ℤ) + 1 - ((m - N : ℕ) : ℤ)) = ((N + 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (le_of_lt h)]
      push_cast
      ring
    rw [hexp, zpow_natCast, inv_inv, hD, mul_div_cancel_left₀ _ hB]

theorem sfTerm_shift {q z : ℂ} (hq : q ≠ 0) (hqn : ‖q‖ < 1) (hz : z ≠ 0) (m N : ℕ) :
    sfTerm q z m ((N:ℤ) - m) =
      (qpNat q q m * qhalf q (m+1) * z^(-(m:ℤ))) *
        (qhalf q N * (q^(-(m:ℤ)) * z)^N / qpNat q q N) := by
  have hQ : qhalfInt q ((N : ℤ) - m) = qhalf q (m + 1) * qhalf q N * q ^ (-((m * N : ℕ) : ℤ)) := by
    rcases le_or_gt m N with h | h
    · rw [show ((N : ℤ) - m) = ((N - m : ℕ) : ℤ) by omega, qhalfInt_natCast,
        sfShift_qhalf_ge hq h]
    · rw [show ((N : ℤ) - m) = -((m - N : ℕ) : ℤ) by omega, qhalfInt_neg_natCast,
        sfShift_qhalf_le hq (le_of_lt h)]
  have hZ : z ^ ((N : ℤ) - m) = z ^ (-(m : ℤ)) * z ^ N := by
    rw [show ((N : ℤ) - m) = -(m : ℤ) + N by ring, zpow_add₀ hz, zpow_natCast]
  have hI : (qpInt (q ^ ((m : ℤ) + 1)) q ((N : ℤ) - m))⁻¹
      = qpNat q q m / qpNat q q N := sfShift_inv_qpInt hqn m N
  have hP : (q ^ (-(m : ℤ)) * z) ^ N = q ^ (-((m * N : ℕ) : ℤ)) * z ^ N := by
    rw [mul_pow, ← zpow_natCast (q ^ (-(m : ℤ))) N, ← zpow_mul q (-(m : ℤ)) N,
      show (-(m : ℤ)) * (N : ℤ) = -((m * N : ℕ) : ℤ) by push_cast; ring]
  rw [sfTerm, div_eq_mul_inv, hQ, hZ, hI, hP, div_eq_mul_inv]
  ring

end Work.Haupt
