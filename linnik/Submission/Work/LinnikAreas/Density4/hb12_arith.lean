import Mathlib

namespace Work.LinnikAreas.Density4

/-- The closing arithmetic of HB Lemma 12.1: from `(NLA)² ≤ S1·S2`, `S1 ≤ LB`,
`S2 ≤ N·S1 + (N²-N)·C·L` and `BC < A²` (with `L > 0`, `S1, S2, B ≥ 0`), deduce
`N ≤ B(B-C)/(A²-BC)`.

Proof outline. Write `n = N`. Combining `S2 ≥ 0` with the upper bound for `S2` and
`S1 ≤ L·B` gives `0 ≤ n·L·B + (n²-n)·C·L`, hence `B + (n-1)·C ≥ 0` (using `n, L > 0`).
Next `(nLA)² ≤ S1·S2 ≤ S1·(n·S1 + (n²-n)·C·L) =: f(S1)`, and the elementary identity
`f(L·B) - f(S1) = n·(L·B - S1)·(L·B + S1 + (n-1)·C·L)` together with
`L·B + S1 + (n-1)·C·L ≥ S1 ≥ 0` gives `f(S1) ≤ f(L·B) = n·L²·B·(B + (n-1)·C)`.
Dividing by `n·L² > 0` yields `n·A² ≤ B² + (n-1)·B·C`, i.e. `n·(A² - B·C) ≤ B·(B - C)`,
and since `A² - B·C > 0` the claim follows. -/
lemma hb12_arith {N : ℕ} (hN : 0 < N) {L A B C S1 S2 : ℝ} (hL : 0 < L)
    (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2) (hB : 0 ≤ B)
    (hCS2 : ((N : ℝ) * L * A) ^ 2 ≤ S1 * S2)
    (hS1ub : S1 ≤ L * B)
    (hS2ub : S2 ≤ (N : ℝ) * S1 + ((N : ℝ) ^ 2 - (N : ℝ)) * C * L)
    (hden : B * C < A ^ 2) :
    (N : ℝ) ≤ B * (B - C) / (A ^ 2 - B * C) := by
  have hn : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  -- `S2 ≥ 0` combined with the upper bound for `S2` and `S1 ≤ L·B`.
  have h1 : (0:ℝ) ≤ (N:ℝ) * S1 + ((N:ℝ)^2 - (N:ℝ)) * C * L := le_trans hS2 hS2ub
  have h2 : (N:ℝ) * S1 ≤ (N:ℝ) * L * B := by nlinarith [hS1ub, hn]
  have h3 : (0:ℝ) ≤ (N:ℝ)*L*B + ((N:ℝ)^2-(N:ℝ))*C*L := by linarith [h1, h2]
  have h4 : (0:ℝ) ≤ L * (B + ((N:ℝ)-1)*C) := by nlinarith [h3, hn]
  have hBn : (0:ℝ) ≤ B + ((N:ℝ) - 1) * C := (mul_nonneg_iff_of_pos_left hL).mp h4
  -- The bracket in the key identity is non-negative.
  have hLB : (0:ℝ) ≤ L * B - S1 := by linarith [hS1ub]
  have hbr : (0:ℝ) ≤ L * B + S1 + ((N:ℝ) - 1) * C * L := by
    nlinarith [hBn, hL, hS1]
  have hprod : (0:ℝ) ≤ (N:ℝ)*(L*B - S1)*(L*B + S1 + ((N:ℝ)-1)*C*L) :=
    mul_nonneg (mul_nonneg (le_of_lt hn) hLB) hbr
  -- Factorisation `f(L·B) - f(S1)`.
  have hfac : (N:ℝ)*L^2*B^2 + ((N:ℝ)^2-(N:ℝ))*C*L^2*B
      - S1*((N:ℝ)*S1 + ((N:ℝ)^2-(N:ℝ))*C*L)
      = (N:ℝ)*(L*B - S1)*(L*B + S1 + ((N:ℝ)-1)*C*L) := by ring
  have hA3 : S1*((N:ℝ)*S1 + ((N:ℝ)^2-(N:ℝ))*C*L)
      ≤ (N:ℝ)*L^2*B^2 + ((N:ℝ)^2-(N:ℝ))*C*L^2*B := by
    linarith [hfac, hprod]
  have hstep : S1 * S2 ≤ S1 * ((N:ℝ) * S1 + ((N:ℝ)^2 - (N:ℝ)) * C * L) :=
    mul_le_mul_of_nonneg_left hS2ub hS1
  have hchain : ((N:ℝ) * L * A)^2 ≤ (N:ℝ)*L^2*B^2 + ((N:ℝ)^2-(N:ℝ))*C*L^2*B :=
    le_trans hCS2 (le_trans hstep hA3)
  -- Divide the chain by `N·L² > 0`.
  have hnL2 : (0:ℝ) < (N:ℝ)*L^2 := by positivity
  have hfac2 : (N:ℝ)*L^2*B^2 + ((N:ℝ)^2-(N:ℝ))*C*L^2*B
      = (N:ℝ)*L^2*(B^2 + ((N:ℝ)-1)*C*B) := by ring
  have hlhs : ((N:ℝ) * L * A)^2 = (N:ℝ)*L^2 * ((N:ℝ)*A^2) := by ring
  have hx : (N:ℝ)*L^2 * ((N:ℝ)*A^2) ≤ (N:ℝ)*L^2*(B^2 + ((N:ℝ)-1)*C*B) := by
    rw [← hlhs, ← hfac2]; exact hchain
  have hdiv : (N:ℝ)*A^2 ≤ B^2 + ((N:ℝ)-1)*C*B := le_of_mul_le_mul_left hx hnL2
  have hfinal : (N:ℝ)*(A^2 - B*C) ≤ B*(B-C) := by nlinarith [hdiv]
  have hdenpos : (0:ℝ) < A^2 - B*C := by linarith [hden]
  rw [le_div_iff₀ hdenpos]
  exact hfinal

end Work.LinnikAreas.Density4
