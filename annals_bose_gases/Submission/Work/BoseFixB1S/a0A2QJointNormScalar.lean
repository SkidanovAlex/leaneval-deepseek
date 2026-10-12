import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.a0A2QJointNormScalar` — the scalar core of the sharp hop atom

The proof of `Work.BoseFixB1S.a0A2QJointNormB1Fix` (the joint core `(★)` at normalised,
box-localised states) completes the square **per hopping edge**, with the *nonnegative* multiplier
`fib ≥ 0` (the uncentred fibre) — this is what makes FS's *sharp* weights
`(√(t+1) ± √(μV))²` available on a *signed* pairing (the trap recorded in
`FINDING_hopAmgmB1.md` §4 is avoided because the multiplier is `fib`, not `δ = fib − κ`).

The two elementary facts are:

* `atomA0A2Q` — the per-edge atom, an exact **perfect square**:
  `8Xx² + 2(t−1−m)xy + ((t−1−m)²/(8X))y² = 8X(x + (t−1−m)y/(8X))² ≥ 0` with
  `X = (√(t+1)+√m)²`, i.e. `2xy(t−1−m) ≥ −8Xx² − ((t−1−m)²/(8X))y²` for **all** reals `x,y`
  (no sign condition on `x,y`), with the FS-type weights: `8X` on the `Q`-side and
  `(t−1−m)²/(8X) ≈ (t−m)²/(32t)` on the `P`-side;
* `blockWeightA0A2Q` — the resulting **P-side block weight**: for `t,m ≥ 0`
  `(1/8)·t(t−1−m)²/X ≤ (1/4)(t+1−m)² + m`, which is the per-block inequality that turns the
  P-side demand into the corpus's two supplies `M₁G` (the `(S+1−m)²`-part) and the pair-condensate
  slack `pcb` (via the variance `Var(n₀) = Pc − S² + S`).
-/

namespace Work.BoseFixB1S

/-- The space `X = (√(t+1)+√m)²` is positive (indeed `≥ 1`) for `t ≥ 0`. -/
theorem sqrtSumSq_pos {t m : ℝ} (ht : 0 ≤ t) (hm : 0 ≤ m) :
    0 < (Real.sqrt (t + 1) + Real.sqrt m) ^ 2 := by
  have h1 : 1 ≤ Real.sqrt (t + 1) := by
    calc (1 : ℝ) = Real.sqrt 1 := by simp
      _ ≤ Real.sqrt (t + 1) := Real.sqrt_le_sqrt (by linarith)
  have h2 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  nlinarith

/-- **The per-edge sharp atom** (an exact perfect square, valid for all reals `x, y` and all
`t, m ≥ 0`):

    2xyd ≥ −8Xx² − (d²/(8X))y² ,    d := t − 1 − m,  X := (√(t+1)+√m)² .

No sign hypothesis on `x`, `y` is needed: the atom is the PSD form
`8Xx² + 2dxy + (d²/(8X))y² = 8X(x + dy/(8X))² ≥ 0`. -/
theorem atomA0A2Q {t m x y : ℝ} (_ht : 0 ≤ t) (_hm : 0 ≤ m) :
    2 * x * y * (t - 1 - m)
      ≥ -(8 * (Real.sqrt (t + 1) + Real.sqrt m) ^ 2) * x ^ 2
        - ((t - 1 - m) ^ 2 / (8 * (Real.sqrt (t + 1) + Real.sqrt m) ^ 2)) * y ^ 2 := by
  set X : ℝ := (Real.sqrt (t + 1) + Real.sqrt m) ^ 2 with hXdef
  have hX : 0 < X := by rw [hXdef]; exact sqrtSumSq_pos _ht _hm
  have hsq : 0 ≤ 8 * X * (x + (t - 1 - m) * y / (8 * X)) ^ 2 := by positivity
  have hexp : 8 * X * (x + (t - 1 - m) * y / (8 * X)) ^ 2
      = 8 * X * x ^ 2 + 2 * (t - 1 - m) * x * y
        + ((t - 1 - m) ^ 2 / (8 * X)) * y ^ 2 := by
    field_simp
    ring
  rw [hXdef] at hsq hexp
  linarith [hsq, hexp]

/-- The elementary bound behind the P-side block weight: for `t, m ≥ 0`,

    (t − 1 − m)² ≤ 2(t + 1 − m)² + 8m .

(This is the "shifted square" correction: `t − 1 − m = (t+1−m) − 2`.) -/
theorem sub_one_sub_sq_le {t m : ℝ} (ht : 0 ≤ t) (hm : 0 ≤ m) :
    (t - 1 - m) ^ 2 ≤ 2 * (t + 1 - m) ^ 2 + 8 * m := by
  set u : ℝ := t + 1 - m with hudef
  have hu : 1 - m ≤ u := by rw [hudef]; linarith
  have hmain : 0 ≤ u ^ 2 + 4 * u + 8 * m - 4 := by
    by_cases hm3 : m ≤ 3
    · -- `m ≤ 3`: monotonicity of `v ↦ v²+4v` on `[−2,∞)`
      have h1 : 0 ≤ u - (1 - m) := by linarith
      have h2 : 0 ≤ u + (1 - m) + 4 := by linarith
      have h3 : 0 ≤ (u - (1 - m)) * (u + (1 - m) + 4) := mul_nonneg h1 h2
      nlinarith [h3]
    · -- `m ≥ 3`: `(u+2)² ≥ 0` and `8m − 8 ≥ 0`
      push_neg at hm3
      nlinarith [sq_nonneg (u + 2), hm3]
  have hu2 : (u - 2) ^ 2 = (t - 1 - m) ^ 2 := by rw [hudef]; ring
  nlinarith [hmain, hu2]

/-- **The P-side block weight.**  For `t, m ≥ 0`,

    (1/8)·t(t−1−m)²/(√(t+1)+√m)²  ≤  (1/4)(t+1−m)² + m .

It follows from `t ≤ X` and the shifted-square bound `sub_one_sub_sq_le`. -/
theorem blockWeightA0A2Q {t m : ℝ} (ht : 0 ≤ t) (hm : 0 ≤ m) :
    (1 / 8) * (t * (t - 1 - m) ^ 2 / (Real.sqrt (t + 1) + Real.sqrt m) ^ 2)
      ≤ (1 / 4) * (t + 1 - m) ^ 2 + m := by
  set X : ℝ := (Real.sqrt (t + 1) + Real.sqrt m) ^ 2 with hXdef
  have hX : 0 < X := by rw [hXdef]; exact sqrtSumSq_pos ht hm
  have htX : t ≤ X := by
    have h1 : Real.sqrt (t + 1) ^ 2 = t + 1 := Real.sq_sqrt (by linarith)
    have h2 : 0 ≤ Real.sqrt (t + 1) := Real.sqrt_nonneg _
    have h3 : 0 ≤ Real.sqrt (t + 1) * Real.sqrt m :=
      mul_nonneg h2 (Real.sqrt_nonneg m)
    rw [hXdef]
    nlinarith [h1, h3]
  have hkey := sub_one_sub_sq_le ht hm
  have hmain : t * (t - 1 - m) ^ 2 ≤ X * (2 * (t + 1 - m) ^ 2 + 8 * m) := by
    have h1 : (t - 1 - m) ^ 2 * t ≤ (t - 1 - m) ^ 2 * X :=
      mul_le_mul_of_nonneg_left htX (sq_nonneg _)
    have h2 : (t - 1 - m) ^ 2 * X ≤ (2 * (t + 1 - m) ^ 2 + 8 * m) * X :=
      mul_le_mul_of_nonneg_right hkey hX.le
    linarith [h1, h2]
  have hgoal : (1 / 8) * (t * (t - 1 - m) ^ 2 / X) = t * (t - 1 - m) ^ 2 / (8 * X) := by
    ring_nf
  rw [hgoal]
  rw [div_le_iff₀ (show (0 : ℝ) < 8 * X by positivity)]
  linarith [hmain]

end Work.BoseFixB1S
