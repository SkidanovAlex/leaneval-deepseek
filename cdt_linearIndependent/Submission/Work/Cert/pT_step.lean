import Mathlib
import Submission.Work.Cert.aLoop_aux
import Submission.Work.Cert.cx_mul_le
import Submission.Work.CertAux.pT_arith
import Submission.Work.CertAux.norm_step_le

namespace Work.Cert

open Complex

/-- **One step of the `pT`-error recurrence, in ulp units.**

`pT` accumulates the powers `q^{tri k}` (`tri k = k(k+1)/2`) by the floored complex product
`cx (cmr a b c d) (cmi a b c d)` of the old mantissa pair `(a,b)` for `q^{tri k}` and the new
mantissa pair `(c,d)` for `q^{k+1}`.  If the old error is at most `20(k-1)` ulps, the new error
is at most `20k` ulps: writing `u = cx a b`, `v = cx c d`, `r = cx (cmr a b c d) (cmi a b c d)`,
`q = qc qr qi` one has `r - q^{tri (k+1)} = (r - u*v) + u*(v - q^{k+1}) + q^{k+1}*(u - q^{tri k})`,
and the three terms are bounded by `3/S`, `‖u‖ * 16/S ≤ (μ + 20(k-1)/S) * 16/S` and
`‖q‖^{k+1} * 20(k-1)/S ≤ μ² * 20(k-1)/S`, where `μ ≤ 79/100` and `k ≥ 1`.  Using `S ≥ 320` this
gives `3 + 16μ + 320(k-1)/S + 20μ²(k-1) ≤ 20 + 20(k-1)`.

This is exactly the `pT` conjunct of the step `k → k+1` of the `A`-loop invariant
(`Work.Cert.AInv`) proved in `Submission/Work/Cert/aInv_step.lean`; it is used both for the `pT`
error bound and for the growth of the partial-sum error (`8 * tri (k+1) + 1 ≥ 20 k`). -/
theorem pT_step (qr qi : ℤ) (k : ℕ) (hk : 1 ≤ k) (a b c d : ℤ) (μ : ℝ)
    (hμ0 : 0 ≤ μ) (hμ : μ ≤ 79 / 100)
    (hz : ‖qc qr qi‖ ≤ μ)
    (hpn : ‖cx c d - (qc qr qi) ^ (k + 1)‖ ≤ 16 / ((S : ℝ)))
    (hpT : ‖cx a b - (qc qr qi) ^ (tri k)‖ ≤ (20 * ((k - 1 : ℕ) : ℝ)) / ((S : ℝ))) :
    ‖cx (cmr a b c d) (cmi a b c d) - (qc qr qi) ^ (tri (k + 1))‖ ≤
      (20 * (k : ℝ)) / ((S : ℝ)) := by
  have hμ1 : μ ≤ 1 := by linarith
  have htk : 1 ≤ tri k := tri_pos hk
  -- `‖q^{tri k}‖ ≤ μ` since `tri k ≥ 1` and `‖q‖ ≤ μ ≤ 1`
  have hqpow1 : ‖(qc qr qi) ^ (tri k)‖ ≤ μ := by
    rw [norm_pow]
    calc ‖qc qr qi‖ ^ tri k ≤ μ ^ tri k := pow_le_pow_left₀ (norm_nonneg _) hz _
      _ ≤ μ ^ 1 := pow_le_pow_of_le_one hμ0 hμ1 htk
      _ = μ := pow_one μ
  -- `‖q^{k+1}‖ ≤ μ²` since `k + 1 ≥ 2`
  have hqpow2 : ‖(qc qr qi) ^ (k + 1)‖ ≤ μ ^ 2 := by
    rw [norm_pow]
    calc ‖qc qr qi‖ ^ (k + 1) ≤ μ ^ (k + 1) := pow_le_pow_left₀ (norm_nonneg _) hz _
      _ ≤ μ ^ 2 := pow_le_pow_of_le_one hμ0 hμ1 (by omega)
  -- `‖cx a b‖ ≤ μ + 20(k-1)/S`
  have hu_bd : ‖cx a b‖ ≤ μ + 20 * ((k - 1 : ℕ) : ℝ) / (S : ℝ) := by
    have h1 : ‖cx a b‖ ≤ ‖(qc qr qi) ^ (tri k)‖ + ‖cx a b - (qc qr qi) ^ (tri k)‖ := by
      calc ‖cx a b‖ = ‖(qc qr qi) ^ (tri k) + (cx a b - (qc qr qi) ^ (tri k))‖ := by ring_nf
        _ ≤ ‖(qc qr qi) ^ (tri k)‖ + ‖cx a b - (qc qr qi) ^ (tri k)‖ := norm_add_le _ _
    exact le_trans h1 (add_le_add hqpow1 hpT)
  -- the three-term triangle-inequality estimate
  have hstep := Work.CertAux.norm_step_le (qc qr qi) (cx a b) (cx c d)
    (cx (cmr a b c d) (cmi a b c d)) k
    (3 / (S : ℝ)) (μ + 20 * ((k - 1 : ℕ) : ℝ) / (S : ℝ)) (16 / (S : ℝ))
    (20 * ((k - 1 : ℕ) : ℝ) / (S : ℝ)) (μ ^ 2)
    (cx_mul_le a b c d) hu_bd hpn hpT hqpow2
  -- the pure arithmetic budget inequality, multiplied through by `S`
  have harith := Work.CertAux.pT_arith k hk μ hμ0 hμ
  have hfinal : ‖cx (cmr a b c d) (cmi a b c d) - (qc qr qi) ^ (tri (k + 1))‖ ≤
      (20 * (k : ℝ)) / ((S : ℝ)) := by
    linarith [hstep, harith]
  exact hfinal

end Work.Cert
