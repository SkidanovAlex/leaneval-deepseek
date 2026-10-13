import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngClean

/-- Elementary quadratic solve: from `0 < K`, `X, M ≥ 0` and `X² ≤ K (XM + M²)` one gets
`X ≤ (K+1) M`.  The key rearrangement is `X² - KXM - KM² = (X - (K+1)M)(X + M) + M²`. -/
lemma step2_quad_solve {K X M : ℝ} (hK : 0 < K) (hX : 0 ≤ X) (hM : 0 ≤ M)
    (h : X ^ 2 ≤ K * (X * M + M ^ 2)) : X ≤ (K + 1) * M := by
  by_contra hc
  rw [not_le] at hc
  have hd : 0 < X - (K + 1) * M := by linarith
  have hs : 0 < X + M := by nlinarith [hK, hM, hX, hc]
  have key : 0 < (X - (K + 1) * M) * (X + M) := mul_pos hd hs
  nlinarith [key, h]

/-- **The final quadratic solve of Step 2.**

Given the collected estimate of the paper's Step 2,

`X² ≤ Ci·(α²(b² + bX)) + α(5+α)bX + (mX + Cj·m²) + 6mX + AX`

with `0 < α ≤ 1/4`, all variables nonnegative, `Ci, Cj, Cm > 0` universal constants and
`m ≤ Cm·A`, one gets `X ≤ C·(A + αb)` with `C = (max (Ci/4 + 49/4) (Ci + Cj) + 1)·(1 + Cm)`
depending only on `Ci, Cj, Cm` — in particular it is universal in `α`.

Route (elementary arithmetic; `nlinarith` needs the intermediate inequalities spelled out, and
`set_option maxHeartbeats 2000000` may be needed).
Put `M := A + αb + m ≥ 0`, so `αb ≤ M`, `m ≤ M`, `X ≥ 0`.  *Substitute `AX = MX - αbX - mX`*
(the reviewer of this statement's derivation below is the one to use; the naive term-by-term
bound is off by one):

`Ci·(α²(b² + bX)) + α(5+α)bX + (mX + Cj·m²) + 6mX + AX
   = Ci(αb)² + Cj m² + MX + ((Ci+1)α + 4)(αb)X + 6mX`.

Each term is then bounded by a multiple of `M² + MX`:
* `Ci(αb)² ≤ Ci M²` (`0 ≤ αb ≤ M` ⟹ `(αb)² ≤ M²` by `mul_self_le_mul_self`);
* `Cj m² ≤ Cj M²` (same, `0 ≤ m ≤ M`);
* `((Ci+1)α + 4)(αb)X ≤ (Ci/4 + 17/4)·MX` since `(Ci+1)α ≤ (Ci+1)/4` and `αb ≤ M`, `X ≥ 0`;
* `6mX ≤ 6MX`;
so `X² ≤ K·(XM + M²)` with `K := max (Ci/4 + 49/4) (Ci + Cj)` (note
`1 + 1/4 + 17/4 + 6 = 49/4`).
The quadratic solve: from `0 < K`, `0 ≤ X`, `0 ≤ M` and `X² ≤ K(XM + M²)` one has `X ≤ (K+1)M`
(if `(K+1)M < X` then multiply by `X > 0` and by `M ≥ 0` to get `X² ≤ KXM + KM² < X²`, using
`K(K+2) < (K+1)²`).
Finally `M = A + αb + m ≤ (1+Cm)A + αb ≤ (1+Cm)(A + αb)` since `m ≤ Cm·A` and `Cm ≥ 0`. -/
theorem step2_collection {Ci Cj Cm X A b m α : ℝ} (hCi : 0 < Ci) (hCj : 0 < Cj)
    (hCm : 0 < Cm) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hX : 0 ≤ X) (hA : 0 ≤ A) (hb : 0 ≤ b) (hm : 0 ≤ m)
    (h : X ^ 2 ≤ Ci * (α ^ 2 * (b ^ 2 + b * X)) + α * (5 + α) * b * X
      + (m * X + Cj * m ^ 2) + 6 * m * X + A * X)
    (hmA : m ≤ Cm * A) :
    X ≤ (max (Ci / 4 + 49 / 4) (Ci + Cj) + 1) * (1 + Cm) * (A + α * b) := by
  set K := max (Ci / 4 + 49 / 4) (Ci + Cj) with hKdef
  set M := A + α * b + m with hMdef
  have hαb : 0 ≤ α * b := mul_nonneg (le_of_lt hα) hb
  have hMnn : 0 ≤ M := by rw [hMdef]; linarith
  have hαbM : α * b ≤ M := by rw [hMdef]; linarith
  have hmM : m ≤ M := by rw [hMdef]; linarith
  -- the algebraic rearrangement of the hypothesis
  have hid : Ci * (α ^ 2 * (b ^ 2 + b * X)) + α * (5 + α) * b * X
        + (m * X + Cj * m ^ 2) + 6 * m * X + A * X
      = Ci * (α * b) ^ 2 + Cj * m ^ 2 + M * X
        + ((Ci + 1) * α + 4) * (α * b) * X + 6 * m * X := by
    rw [hMdef]; ring
  have h2 : X ^ 2 ≤ Ci * (α * b) ^ 2 + Cj * m ^ 2 + M * X
        + ((Ci + 1) * α + 4) * (α * b) * X + 6 * m * X := by
    rw [← hid]; exact h
  -- term-by-term bounds
  have hsq_ab : (α * b) ^ 2 ≤ M ^ 2 := by
    have hp : 0 ≤ (M - α * b) * (M + α * b) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  have hb1 : Ci * (α * b) ^ 2 ≤ Ci * M ^ 2 :=
    mul_le_mul_of_nonneg_left hsq_ab (le_of_lt hCi)
  have hsq_m : m ^ 2 ≤ M ^ 2 := by
    have hp : 0 ≤ (M - m) * (M + m) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  have hb2 : Cj * m ^ 2 ≤ Cj * M ^ 2 :=
    mul_le_mul_of_nonneg_left hsq_m (le_of_lt hCj)
  have hcoef : (Ci + 1) * α + 4 ≤ Ci / 4 + 17 / 4 := by
    have h1 : (Ci + 1) * α ≤ (Ci + 1) * (1 / 4) :=
      mul_le_mul_of_nonneg_left hα4 (by linarith)
    linarith
  have hcross : ((Ci + 1) * α + 4) * (α * b) * X ≤ (Ci / 4 + 17 / 4) * (M * X) := by
    have h1 : ((Ci + 1) * α + 4) * (α * b) ≤ (Ci / 4 + 17 / 4) * M :=
      mul_le_mul hcoef hαbM hαb (by linarith)
    calc ((Ci + 1) * α + 4) * (α * b) * X
        ≤ ((Ci / 4 + 17 / 4) * M) * X := mul_le_mul_of_nonneg_right h1 hX
      _ = (Ci / 4 + 17 / 4) * (M * X) := by ring
  have h6 : 6 * m * X ≤ 6 * M * X := by
    have h1 : m * X ≤ M * X := mul_le_mul_of_nonneg_right hmM hX
    linarith
  have hcomb : X ^ 2 ≤ (Ci + Cj) * M ^ 2 + (Ci / 4 + 45 / 4) * (M * X) := by
    linarith [h2, hb1, hb2, hcross, h6]
  -- assemble into the canonical quadratic form
  have hK1 : Ci + Cj ≤ K := by rw [hKdef]; exact le_max_right _ _
  have hK2 : Ci / 4 + 45 / 4 ≤ K := by
    rw [hKdef]
    exact le_trans (by linarith) (le_max_left _ _)
  have hKnn : 0 < K := by
    rw [hKdef]
    exact lt_of_lt_of_le (by linarith : (0 : ℝ) < Ci / 4 + 49 / 4) (le_max_left _ _)
  have hquad : X ^ 2 ≤ K * (X * M + M ^ 2) := by
    have t1 : (Ci + Cj) * M ^ 2 ≤ K * M ^ 2 :=
      mul_le_mul_of_nonneg_right hK1 (sq_nonneg M)
    have t2 : (Ci / 4 + 45 / 4) * (M * X) ≤ K * (M * X) :=
      mul_le_mul_of_nonneg_right hK2 (mul_nonneg hMnn hX)
    nlinarith [hcomb, t1, t2]
  have hXM : X ≤ (K + 1) * M := step2_quad_solve hKnn hX hMnn hquad
  -- bound `M`
  have hMbd : M ≤ (1 + Cm) * (A + α * b) := by
    have h2' : A + α * b + m ≤ (1 + Cm) * (A + α * b) := by
      have hp : 0 ≤ Cm * (α * b) := mul_nonneg (le_of_lt hCm) hαb
      nlinarith [hmA, hp]
    rw [hMdef]; exact h2'
  have hfin : X ≤ (K + 1) * ((1 + Cm) * (A + α * b)) :=
    le_trans hXM (mul_le_mul_of_nonneg_left hMbd (by linarith))
  calc X ≤ (K + 1) * ((1 + Cm) * (A + α * b)) := hfin
    _ = (K + 1) * (1 + Cm) * (A + α * b) := by ring

end Work.FTS.EllipticEst.AngClean
