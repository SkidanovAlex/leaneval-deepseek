import Mathlib

namespace Work.LinnikAreas

/-- Arithmetic "repulsion" estimate: given the lower bound on `y` in terms of
`log (3 / (72 J x))`, with `A = 3 / (8 JB)`, `J x ≤ 1/24` and `J ≤ 2 JB L`,
one gets `y L ≥ A log (1/(x L)) + A log (3/(144 JB))`.

The key point is that both coefficients `24 J x ≤ 1` and `J ≤ 2 JB L`
make two logarithmic quantities non-negative/non-positive in the right way. -/
theorem repelFinalArith {A JB L x y J : ℝ} (hJB : 0 < JB) (hA : A = 3 / (8 * JB))
    (hL : 1 ≤ L) (hJ : 1 ≤ J) (hx : 0 < x) (hJx : J * x ≤ 1 / 24)
    (hJle : J ≤ 2 * JB * L)
    (hy : y ≥ 3 * Real.log (3 / (72 * J * x)) / (4 * J)) :
    y * L ≥ A * Real.log (1 / (x * L)) + A * Real.log (3 / (144 * JB)) := by
  have hJpos : 0 < J := lt_of_lt_of_le zero_lt_one hJ
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  -- The two logarithms appearing are the same up to the factor `3 = 72/24`.
  have hlogeq : Real.log (3 / (72 * J * x)) = Real.log (1 / (24 * J * x)) := by
    congr 1
    field_simp; ring
  -- `T = log (1/(24 J x)) ≥ 0` because `24 J x ≤ 1`.
  have hT : 0 ≤ Real.log (1 / (24 * J * x)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hJx]
  -- `s = log (J/(2 JB L)) ≤ 0` because `J ≤ 2 JB L`.
  have hs : Real.log (J / (2 * JB * L)) ≤ 0 := by
    apply Real.log_nonpos (by positivity)
    rw [div_le_one (by positivity)]
    exact hJle
  -- `k = 2 JB L / J ≥ 1`.
  have hk : 1 ≤ 2 * JB * L / J := by
    rw [le_div_iff₀ hJpos]; linarith [hJle]
  -- Split the `3/(144 JB x L)` logarithm into the two pieces above.
  have hlogr : Real.log (3 / (144 * JB * x * L))
      = Real.log (1 / (24 * J * x)) + Real.log (J / (2 * JB * L)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp; ring
  -- `T ≤ k * T` since `k ≥ 1` and `T ≥ 0`.
  have hTk : Real.log (1 / (24 * J * x))
      ≤ (2 * JB * L / J) * Real.log (1 / (24 * J * x)) := by
    have h := mul_le_mul_of_nonneg_right hk hT
    simpa using h
  -- `T + s ≤ k * T`.
  have hTs : Real.log (1 / (24 * J * x)) + Real.log (J / (2 * JB * L))
      ≤ (2 * JB * L / J) * Real.log (1 / (24 * J * x)) := by
    have h := add_le_add hTk hs
    simpa using h
  -- Core estimate.
  have hcore : Real.log (3 / (144 * JB * x * L))
      ≤ (2 * JB * L / J) * Real.log (1 / (24 * J * x)) := by
    rw [hlogr]; exact hTs
  have hcoef : 0 < 3 / (8 * JB) := by positivity
  have hstep2 : (3 / (8 * JB)) * Real.log (3 / (144 * JB * x * L))
      ≤ (3 / (8 * JB)) * ((2 * JB * L / J) * Real.log (1 / (24 * J * x))) :=
    mul_le_mul_of_nonneg_left hcore (le_of_lt hcoef)
  -- Collapse the coefficient into `(3 T / (4 J)) * L`.
  have heq1 : (3 / (8 * JB)) * ((2 * JB * L / J) * Real.log (1 / (24 * J * x)))
      = (3 * Real.log (1 / (24 * J * x)) / (4 * J)) * L := by
    field_simp; ring
  -- Rewrite the target right-hand side into the collapsed form.
  have hrhs : A * Real.log (1 / (x * L)) + A * Real.log (3 / (144 * JB))
      = (3 / (8 * JB)) * Real.log (3 / (144 * JB * x * L)) := by
    rw [hA, ← mul_add]
    congr 1
    rw [← Real.log_mul (by positivity) (by positivity)]
    congr 1
    field_simp
  have hkey : (3 * Real.log (3 / (72 * J * x)) / (4 * J)) * L
      ≥ A * Real.log (1 / (x * L)) + A * Real.log (3 / (144 * JB)) := by
    rw [hrhs, hlogeq]
    calc (3 * Real.log (1 / (24 * J * x)) / (4 * J)) * L
        = (3 / (8 * JB)) * ((2 * JB * L / J) * Real.log (1 / (24 * J * x))) := heq1.symm
      _ ≥ (3 / (8 * JB)) * Real.log (3 / (144 * JB * x * L)) := hstep2
  -- Multiply the hypothesis lower bound on `y` by `L > 0`.
  have hfin : (3 * Real.log (3 / (72 * J * x)) / (4 * J)) * L ≤ y * L :=
    mul_le_mul_of_nonneg_right hy (le_of_lt hLpos)
  exact le_trans hkey hfin

end Work.LinnikAreas
