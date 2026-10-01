import Mathlib

namespace Work.ZeroDensity.Zeta.balAux

/-- Pointwise bound for the tail of a harmonic-type sum, in the form needed by the
zero-density argument: writing `n = ⌊y⌋₊`, the quantity
`1 / (A * (A - y)) + 1 / A ^ 2` with `A = k + n + 2` is at most
`2 / ((k + 1) * (k + n + 1))`.

The two ingredients are `n ≤ y < n + 1`, which gives `A - y ≥ k + 1` and hence
`1 / (A * (A - y)) ≤ 1 / (A * (k + 1))`, and the algebraic identity
`2 * A ^ 2 - (k + n + 1) * (A + (k + 1)) = A * (n + 2) + (k + 1) ≥ 0`. -/
theorem harmTailPtwise (y : ℝ) (hy : 3 ≤ y) (k : ℕ) :
    (1 : ℝ) / (((k + ⌊y⌋₊ + 2 : ℕ) : ℝ) * (((k + ⌊y⌋₊ + 2 : ℕ) : ℝ) - y))
      + (1 : ℝ) / (((k + ⌊y⌋₊ + 2 : ℕ) : ℝ)) ^ 2
    ≤ 2 / (((k + 1 : ℕ) : ℝ) * (((k + ⌊y⌋₊ + 1 : ℕ) : ℝ))) := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  set n : ℕ := ⌊y⌋₊ with hn
  have hny : (n : ℝ) ≤ y := by
    have h := Nat.floor_le hy0
    rwa [hn]
  have hlt : y < (n : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one y
    rwa [← hn] at h
  have hcastA : ((k + n + 2 : ℕ) : ℝ) = (k : ℝ) + (n : ℝ) + 2 := by push_cast; ring
  have hcastB : ((k + n + 1 : ℕ) : ℝ) = (k : ℝ) + (n : ℝ) + 1 := by push_cast; ring
  have hcastC : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hcastA, hcastB, hcastC]
  -- `A - y ≥ k + 1`
  have hAy : (k : ℝ) + (n : ℝ) + 2 - y ≥ (k : ℝ) + 1 := by linarith
  -- the algebraic core: `B * (A + C) ≤ 2 * A ^ 2`
  have hkey :
      ((k : ℝ) + (n : ℝ) + 1) * (((k : ℝ) + 1) + ((k : ℝ) + (n : ℝ) + 2))
        ≤ 2 * ((k : ℝ) + (n : ℝ) + 2) ^ 2 := by
    have hid : 2 * ((k : ℝ) + (n : ℝ) + 2) ^ 2
          - ((k : ℝ) + (n : ℝ) + 1) * (((k : ℝ) + 1) + ((k : ℝ) + (n : ℝ) + 2))
        = ((k : ℝ) + (n : ℝ) + 2) * ((n : ℝ) + 2) + ((k : ℝ) + 1) := by ring
    nlinarith [hid,
      mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) + (n : ℝ) + 2 by linarith)
        (show (0 : ℝ) ≤ (n : ℝ) + 2 by linarith),
      (show (0 : ℝ) ≤ (k : ℝ) + 1 by linarith)]
  -- bound the `y`-dependent term
  have hstep1 : 1 / (((k : ℝ) + (n : ℝ) + 2) * (((k : ℝ) + (n : ℝ) + 2) - y))
      ≤ 1 / (((k : ℝ) + (n : ℝ) + 2) * ((k : ℝ) + 1)) := by
    apply one_div_le_one_div_of_le
      (by positivity : (0 : ℝ) < ((k : ℝ) + (n : ℝ) + 2) * ((k : ℝ) + 1))
    nlinarith [hAy, show (0 : ℝ) < (k : ℝ) + (n : ℝ) + 2 by positivity]
  -- the remaining purely algebraic estimate
  have hstep2 : 1 / (((k : ℝ) + (n : ℝ) + 2) * ((k : ℝ) + 1))
        + 1 / ((k : ℝ) + (n : ℝ) + 2) ^ 2
      ≤ 2 / (((k : ℝ) + 1) * ((k : ℝ) + (n : ℝ) + 1)) := by
    have hdiff : (1 : ℝ) / (((k : ℝ) + (n : ℝ) + 2) * ((k : ℝ) + 1))
          + 1 / ((k : ℝ) + (n : ℝ) + 2) ^ 2
          - 2 / (((k : ℝ) + 1) * ((k : ℝ) + (n : ℝ) + 1))
        = (((k : ℝ) + (n : ℝ) + 1) * (((k : ℝ) + 1) + ((k : ℝ) + (n : ℝ) + 2))
            - 2 * ((k : ℝ) + (n : ℝ) + 2) ^ 2)
          / (((k : ℝ) + (n : ℝ) + 2) ^ 2 * ((k : ℝ) + 1) * ((k : ℝ) + (n : ℝ) + 1)) := by
      field_simp
      ring
    have hle : (((k : ℝ) + (n : ℝ) + 1) * (((k : ℝ) + 1) + ((k : ℝ) + (n : ℝ) + 2))
          - 2 * ((k : ℝ) + (n : ℝ) + 2) ^ 2)
        / (((k : ℝ) + (n : ℝ) + 2) ^ 2 * ((k : ℝ) + 1) * ((k : ℝ) + (n : ℝ) + 1)) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · positivity
    linarith
  linarith

end Work.ZeroDensity.Zeta.balAux
