import Mathlib

namespace Work.Mostow

/-- Reverse triangle-type arithmetic inequality at a cusp: if `X + λ² (st/2) B² ≤ cosh M`
with `st ≤ 1` and `A ≤ L B + Cq`, then `X + (st/2) A² ≤ cosh M + 2 L² cosh M / λ² + Cq²`. -/
theorem cuspReverse_arith {s t L lam Cq A B X M : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s * t ≤ 1)
    (hL : 0 ≤ L) (hlam : 0 < lam) (hCq : 0 ≤ Cq)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAB : A ≤ L * B + Cq) (hX : 1 ≤ X) (hM : 0 ≤ M)
    (hY : X + (lam * s) * (lam * t) / 2 * B ^ 2 ≤ Real.cosh M) :
    X + s * t / 2 * A ^ 2 ≤ Real.cosh M + 2 * L ^ 2 * Real.cosh M / lam ^ 2 + Cq ^ 2 := by
  have hlam2 : (0:ℝ) < lam ^ 2 := by positivity
  have hX0 : (0:ℝ) ≤ X := by linarith [hX]
  -- `(lam*s)*(lam*t)/2*B^2 = lam^2 * (s*t/2*B^2)` is nonnegative
  have hT : 0 ≤ (lam * s) * (lam * t) / 2 * B ^ 2 := by positivity
  -- X ≤ cosh M and  lam^2 (st/2) B^2 ≤ cosh M
  have hXc : X ≤ Real.cosh M := by nlinarith [hY, hT]
  have h1 : lam ^ 2 * (s * t / 2 * B ^ 2) ≤ Real.cosh M := by nlinarith [hY, hX0]
  have hkey2 : lam ^ 2 * (s * t * B ^ 2) ≤ 2 * Real.cosh M := by nlinarith [h1]
  have hkey : s * t * B ^ 2 ≤ 2 * Real.cosh M / lam ^ 2 := by
    rw [le_div_iff₀ hlam2]; nlinarith [hkey2]
  -- (LB + Cq)^2 ≤ 2 L^2 B^2 + 2 Cq^2, hence A^2 ≤ ...
  have hLB0 : 0 ≤ L * B + Cq := by nlinarith [hL, hB, hCq, mul_nonneg hL hB]
  have h_ple : A - (L * B + Cq) ≤ 0 := by linarith
  have h_pge : 0 ≤ A + (L * B + Cq) := by linarith
  have hA2 : A ^ 2 ≤ 2 * L ^ 2 * B ^ 2 + 2 * Cq ^ 2 := by
    have h1 : A ^ 2 ≤ (L * B + Cq) ^ 2 := by
      nlinarith [mul_nonpos_of_nonpos_of_nonneg h_ple h_pge]
    nlinarith [h1, sq_nonneg (L * B - Cq)]
  have hst0 : 0 ≤ s * t := mul_nonneg hs ht
  have hstB : s * t / 2 * A ^ 2 ≤ L ^ 2 * (s * t * B ^ 2) + s * t * Cq ^ 2 := by
    nlinarith [hA2, hst0]
  have h2 : L ^ 2 * (s * t * B ^ 2) ≤ L ^ 2 * (2 * Real.cosh M / lam ^ 2) :=
    mul_le_mul_of_nonneg_left hkey (sq_nonneg L)
  have h3 : s * t * Cq ^ 2 ≤ Cq ^ 2 := by nlinarith [hst, hCq, hst0]
  have hsecond : s * t / 2 * A ^ 2 ≤ L ^ 2 * (2 * Real.cosh M / lam ^ 2) + Cq ^ 2 := by
    linarith [hstB, h2, h3]
  have heq : L ^ 2 * (2 * Real.cosh M / lam ^ 2) + Cq ^ 2
      = Cq ^ 2 + 2 * L ^ 2 * Real.cosh M / lam ^ 2 := by ring
  linarith [hXc, hsecond, heq]

end Work.Mostow
