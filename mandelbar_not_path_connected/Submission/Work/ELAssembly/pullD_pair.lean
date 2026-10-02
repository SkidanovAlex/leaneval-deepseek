import Mathlib
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELNest.armChain_nest

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

/-! ## The angle arithmetic of the boundary of the `b₂`-polygon

`Work.ELNest.armChain_nest` puts the six boundary angles of the level-`n` `b₂`-polygon
(`armA1 n, armA2 n`, `armB1 n, armB2 n`, `armC1 n, armC2 n`) in closed form: they are the
affine functions

* `armA1 n = 22/63 + (289/21483)·64⁻ⁿ`,   `armA2 n = 25/63 − (41/21483)·64⁻ⁿ`,
* `armB1 n = 25/63 + (1156/21483)·64⁻ⁿ`,  `armB2 n = 37/63 − (164/21483)·64⁻ⁿ`,
* `armC1 n = 37/63 + (4624/21483)·64⁻ⁿ`,  `armC2 n = 22/63 − (656/21483)·64⁻ⁿ`

of `y = 64⁻ⁿ`.  The angle map `Work.EL.T θ = Int.fract (-2θ)` acts on external angles of the
antiholomorphic family, so its sixth iterate is `θ ↦ fract (64 θ)`
(`T_iterate_six`), and `T^[6]` carries the level-`(n+1)` angle back to the level-`n` angle of the
same arm: `64 · (p + q·64^{-(n+1)}) = (p + q·64⁻ⁿ) + k` with an *integer* `k`, and the target
angle lies in `[0,1)`, so `Int.fract` removes `k` and leaves the angle itself.

This file isolates that computation (`T6_affine` plus the six elementary membership bounds), so
that `pullD_pair` is a sequence of exact rational applications of it. -/

/-! ## `T^[6]` and the affine step -/

/-- The sixth iterate of the angle-doubling map `T θ = Int.fract (-2θ)` is the fractional part
of `64 θ = (-2)^6 θ` (the `k = 6` case of `Work.ELNest.T_iterate_succ`). -/
lemma T_iterate_six (θ : ℝ) : (Work.EL.T)^[6] θ = Int.fract (64 * θ) := by
  have h := Work.ELNest.T_iterate_succ 5 θ
  rw [h]
  norm_num

/-- **One affine step of the `b₂`-nest.**  If `64 p = p + k` for an integer `k` and the
level-`n` angle `p + q·64⁻ⁿ` lies in `[0,1)`, then `T^[6]` carries the level-`(n+1)` angle
`p + q·64^{-(n+1)}` to that level-`n` angle.  The only content is
`64·(p + q·64^{-(n+1)}) = (p + q·64⁻ⁿ) + k` (via `64^{-(n+1)} = 64⁻ⁿ/64`) together with
`Int.fract_add_intCast` and `Int.fract_eq_self`. -/
lemma T6_affine (p q : ℝ) (k : ℤ) (n : ℕ) (hp : (64 : ℝ) * p = p + (k : ℝ))
    (h0 : 0 ≤ p + q * ((64 : ℝ) ^ n)⁻¹) (h1 : p + q * ((64 : ℝ) ^ n)⁻¹ < 1) :
    (Work.EL.T)^[6] (p + q * ((64 : ℝ) ^ (n + 1))⁻¹) = p + q * ((64 : ℝ) ^ n)⁻¹ := by
  rw [T_iterate_six, Work.ELNest.inv_pow_succ_64 n]
  have h64 : (64 : ℝ) * (p + q * (((64 : ℝ) ^ n)⁻¹ / 64))
      = (p + q * ((64 : ℝ) ^ n)⁻¹) + (k : ℝ) := by
    have h2 : (64 : ℝ) * (q * (((64 : ℝ) ^ n)⁻¹ / 64)) = q * ((64 : ℝ) ^ n)⁻¹ := by ring
    linarith [hp, h2]
  rw [h64, Int.fract_add_intCast]
  exact Int.fract_eq_self.mpr ⟨h0, h1⟩

/-! ## Elementary bounds on the affine families -/

/-- `64⁻ⁿ ≤ 1`. -/
lemma inv_pow_64_le_one (n : ℕ) : ((64 : ℝ) ^ n)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

/-- For `q ≥ 0` the affine family `p + q·y` is increasing in `y`, so on `y ∈ [0,1]` it is
trapped between `p` and `p + q`. -/
lemma affine_mem_of_le (p q : ℝ) (hp : 0 ≤ p) (hpq : p + q < 1) (hq : 0 ≤ q)
    (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ p + q * y ∧ p + q * y < 1 := by
  constructor
  · nlinarith [mul_nonneg hq hy]
  · nlinarith [mul_le_of_le_one_right hq hy1]

/-- For `q ≤ 0` the affine family `p + q·y` is decreasing in `y`, so on `y ∈ [0,1]` it is
trapped between `p + q` and `p`. -/
lemma affine_mem_of_nonpos (p q : ℝ) (hpq : 0 ≤ p + q) (hp : p < 1) (hq : q ≤ 0)
    (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ p + q * y ∧ p + q * y < 1 := by
  have hqy : q ≤ q * y := by nlinarith
  have hqy' : q * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hq hy
  exact ⟨by linarith, by linarith⟩

/-! ## The three decreasing arm angles in the shape `p + q·64⁻ⁿ`

`Work.ELNest.armA2_closed`, `armB2_closed`, `armC2_closed` present the decreasing families with
a difference; `T6_affine` wants the sum `p + q·y` with the (negative) coefficient `q` in front,
so the three closed forms are recorded once in that shape. -/

/-- `armA2 n = 25/63 − (41/21483)·64⁻ⁿ`, with the coefficient in front. -/
lemma armA2_form (n : ℕ) :
    Work.ELNest.armA2 n = (25 : ℝ) / 63 + (-(41 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ := by
  rw [Work.ELNest.armA2_closed n]; ring

/-- `armB2 n = 37/63 − (164/21483)·64⁻ⁿ`, with the coefficient in front. -/
lemma armB2_form (n : ℕ) :
    Work.ELNest.armB2 n = (37 : ℝ) / 63 + (-(164 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ := by
  rw [Work.ELNest.armB2_closed n]; ring

/-- `armC2 n = 22/63 − (656/21483)·64⁻ⁿ`, with the coefficient in front. -/
lemma armC2_form (n : ℕ) :
    Work.ELNest.armC2 n = (22 : ℝ) / 63 + (-(656 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ := by
  rw [Work.ELNest.armC2_closed n]; ring

/-! ## The six level-`n` angles lie in `[0,1)` -/

/-- The level-`n` arm-`A` first angle lies in `[0,1)`. -/
lemma armA1_bounds (n : ℕ) :
    0 ≤ (22 : ℝ) / 63 + ((289 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ ∧
      (22 : ℝ) / 63 + ((289 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ < 1 :=
  affine_mem_of_le _ _ (by norm_num) (by norm_num) (by norm_num) _
    (by positivity) (inv_pow_64_le_one n)

/-- The level-`n` arm-`A` second angle lies in `[0,1)`. -/
lemma armA2_bounds (n : ℕ) :
    0 ≤ (25 : ℝ) / 63 + (-(41 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ ∧
      (25 : ℝ) / 63 + (-(41 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ < 1 :=
  affine_mem_of_nonpos _ _ (by norm_num) (by norm_num) (by norm_num) _
    (by positivity) (inv_pow_64_le_one n)

/-- The level-`n` arm-`B` first angle lies in `[0,1)`. -/
lemma armB1_bounds (n : ℕ) :
    0 ≤ (25 : ℝ) / 63 + ((1156 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ ∧
      (25 : ℝ) / 63 + ((1156 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ < 1 :=
  affine_mem_of_le _ _ (by norm_num) (by norm_num) (by norm_num) _
    (by positivity) (inv_pow_64_le_one n)

/-- The level-`n` arm-`B` second angle lies in `[0,1)`. -/
lemma armB2_bounds (n : ℕ) :
    0 ≤ (37 : ℝ) / 63 + (-(164 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ ∧
      (37 : ℝ) / 63 + (-(164 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ < 1 :=
  affine_mem_of_nonpos _ _ (by norm_num) (by norm_num) (by norm_num) _
    (by positivity) (inv_pow_64_le_one n)

/-- The level-`n` arm-`C` first angle lies in `[0,1)`. -/
lemma armC1_bounds (n : ℕ) :
    0 ≤ (37 : ℝ) / 63 + ((4624 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ ∧
      (37 : ℝ) / 63 + ((4624 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ < 1 :=
  affine_mem_of_le _ _ (by norm_num) (by norm_num) (by norm_num) _
    (by positivity) (inv_pow_64_le_one n)

/-- The level-`n` arm-`C` second angle lies in `[0,1)`. -/
lemma armC2_bounds (n : ℕ) :
    0 ≤ (22 : ℝ) / 63 + (-(656 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ ∧
      (22 : ℝ) / 63 + (-(656 : ℝ) / 21483) * ((64 : ℝ) ^ n)⁻¹ < 1 :=
  affine_mem_of_nonpos _ _ (by norm_num) (by norm_num) (by norm_num) _
    (by positivity) (inv_pow_64_le_one n)

-- Shell: `namespace Work.ELAssembly` (area `Submission/Work/ELAssembly/`), `open LeanEval.ComplexAnalysis (Tantibar)`.
/-- **The boundary angles of the level-`(n+1)` `b₂`-polygon map to boundary angles of the
level-`n` polygon** (exact rational arithmetic on the closed forms of
`Work.ELNest.armChain_nest`).  All six angles lie in `(0,1)`, so the `fract` representative is
the angle itself. -/
theorem pullD_pair (n : ℕ) :
    ((Work.EL.T)^[6] (Work.ELNest.armA1 (n + 1)) = Work.ELNest.armA1 n) ∧
    ((Work.EL.T)^[6] (Work.ELNest.armA2 (n + 1)) = Work.ELNest.armA2 n) ∧
    ((Work.EL.T)^[6] (Work.ELNest.armB1 (n + 1)) = Work.ELNest.armB1 n) ∧
    ((Work.EL.T)^[6] (Work.ELNest.armB2 (n + 1)) = Work.ELNest.armB2 n) ∧
    ((Work.EL.T)^[6] (Work.ELNest.armC1 (n + 1)) = Work.ELNest.armC1 n) ∧
    ((Work.EL.T)^[6] (Work.ELNest.armC2 (n + 1)) = Work.ELNest.armC2 n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Work.ELNest.armA1_closed (n + 1), Work.ELNest.armA1_closed n]
    exact T6_affine _ _ 22 n (by norm_num) (armA1_bounds n).1 (armA1_bounds n).2
  · rw [armA2_form (n + 1), armA2_form n]
    exact T6_affine _ _ 25 n (by norm_num) (armA2_bounds n).1 (armA2_bounds n).2
  · rw [Work.ELNest.armB1_closed (n + 1), Work.ELNest.armB1_closed n]
    exact T6_affine _ _ 25 n (by norm_num) (armB1_bounds n).1 (armB1_bounds n).2
  · rw [armB2_form (n + 1), armB2_form n]
    exact T6_affine _ _ 37 n (by norm_num) (armB2_bounds n).1 (armB2_bounds n).2
  · rw [Work.ELNest.armC1_closed (n + 1), Work.ELNest.armC1_closed n]
    exact T6_affine _ _ 37 n (by norm_num) (armC1_bounds n).1 (armC1_bounds n).2
  · rw [armC2_form (n + 1), armC2_form n]
    exact T6_affine _ _ 22 n (by norm_num) (armC2_bounds n).1 (armC2_bounds n).2

end Work.ELAssembly
