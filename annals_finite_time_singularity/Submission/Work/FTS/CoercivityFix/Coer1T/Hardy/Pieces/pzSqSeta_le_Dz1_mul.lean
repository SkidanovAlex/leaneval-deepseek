/-
`Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces.pzSqSeta_le_Dz1_mul` — STATUS: **proved**.

The pointwise Hardy-type bookkeeping inequality on a compact box `z ∈ [a,b]`, `0 < a < b`:

    (∂_z f)² · sin(2θ)^{-η} ≤ (b²/(1+a)⁴) · (D_z f · w/sin(2θ)^{η/2})²,

used to dominate `∂_z f · w_θ` by the `D_z`-slot integrand of `H^1` on a box (so that
`pzSqSeta_box_integrable` follows from the integrability of the `D_z` slot).

## Why it is true, and that nothing more is needed

Since `DzIter 1 f z θ = D_z f = z·∂_z f` and `w(z) = (1+z)²/z²`, the right-hand side is
exactly the left-hand side multiplied by the **constant-in-(f,θ) factor**

    (b²/(1+a)⁴) · z² · w(z)² = (b·z·w(z))²/(1+a)⁴,

and the only content of the statement is the elementary bound

    1 ≤ (b²/(1+a)⁴)·z²·w(z)²   for  z ∈ [a,b],

equivalently `(1+a)² ≤ b·z·w(z) = b(1+z)²/z`.  This follows from `a ≤ z ≤ b`, `0 < a`:

    b·(1+z)²/z ≥ (b/z)·(1+a)² ≥ (1+a)²   (since `1 ≤ b/z` ⟺ `z ≤ b`, `z > 0`).

The identity `(w/s^{η/2})² = w²·s^{-η}` used to compare the two sides holds for every
`s ≥ 0` (including `s = 0`, where both sides are `0`), so it holds at the angular
endpoints `θ = 0, π/2` as well: no positivity of `sin(2θ)` is needed, only
`sin(2θ) ≥ 0` on `[0,π/2]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces

open Work.Spaces

/-- The elementary box bound `1 ≤ (b²/(1+a)⁴)·z²·w(z)²` for `z ∈ [a,b]`, `0 < a < b`.
Equivalently `(1+a)² ≤ b·z·w(z) = b(1+z)²/z`, which is immediate from
`(b/z)·(1+a)² ≥ (1+a)²` and `(b/z)·(1+z)² = b(1+z)²/z`. -/
theorem one_le_bSq_div_mul_wSq {a b z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hzb : z ≤ b) :
    1 ≤ b ^ 2 / (1 + a) ^ 4 * (z ^ 2 * w z ^ 2) := by
  have hzpos : 0 < z := lt_of_lt_of_le ha haz
  -- `(1+a)² ≤ b·z·w z`
  have hstep : (1 + a) ^ 2 ≤ b * z * w z := by
    rw [w]
    have h1 : 1 ≤ b / z := (one_le_div hzpos).2 hzb
    have h2 : (1 + a) ^ 2 ≤ (1 + z) ^ 2 := by nlinarith
    have h3 : (1 + z) ^ 2 ≤ (b / z) * (1 + z) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right h1 (sq_nonneg (1 + z))
      simpa using hh
    have h4 : b * z * ((1 + z) ^ 2 / z ^ 2) = (b / z) * (1 + z) ^ 2 := by
      field_simp
    linarith
  -- squaring a nonnegative inequality
  have hsq : ((1 + a) ^ 2) ^ 2 ≤ (b * z * w z) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) hstep 2
  have h1a4 : (0 : ℝ) < (1 + a) ^ 4 := by positivity
  rw [div_mul_eq_mul_div, one_le_div h1a4]
  nlinarith [hsq]

/-- The `θ`-weight identity `(w/s^{η/2})² = w²·s^{-η}` for `s ≥ 0`.  Both sides vanish at
`s = 0`, so no strict positivity is required. -/
theorem div_rpow_sq_eq (c s : ℝ) (hs : 0 ≤ s) :
    (c / s ^ (eta / 2)) ^ 2 = c ^ 2 * s ^ (-(eta)) := by
  have hsq : (s ^ (eta / 2)) ^ 2 = s ^ eta := by
    rw [← Real.rpow_natCast (s ^ (eta / 2)) 2,
        ← Real.rpow_mul hs (eta / 2) ((2 : ℕ) : ℝ)]
    rw [show eta / 2 * ((2 : ℕ) : ℝ) = eta by norm_num]
  rw [div_pow, hsq, div_eq_mul_inv, Real.rpow_neg hs]

theorem pzSqSeta_le_Dz1_mul {f : ℝ → ℝ → ℝ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.pz f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (b ^ 2 / (1 + a) ^ 4) *
          (Work.Spaces.DzIter 1 f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  intro z hz θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · have := Real.pi_pos; linarith [hθ.2]
  -- `D_z f = z·∂_z f`
  have hDz : DzIter 1 f z θ = z * pz f z θ := by
    simp [DzIter, Dz]
  -- the box factor is `≥ 1` (uses `hab` through `0 < b`)
  have hfac : 1 ≤ b ^ 2 / (1 + a) ^ 4 * (z ^ 2 * w z ^ 2) :=
    one_le_bSq_div_mul_wSq ha hz.1 hz.2
  have _hb : 0 < b := lt_trans ha hab
  -- the `θ`-weight identity
  have hY : (w z / Real.sin (2 * θ) ^ (eta / 2)) ^ 2 = w z ^ 2 * Real.sin (2 * θ) ^ (-(eta)) :=
    div_rpow_sq_eq (w z) (Real.sin (2 * θ)) hsin
  have hpz : 0 ≤ (pz f z θ) ^ 2 := sq_nonneg _
  have hS : 0 ≤ Real.sin (2 * θ) ^ (-(eta)) := Real.rpow_nonneg hsin _
  -- the right-hand side, expanded
  have hRw : (z * pz f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2
      = z ^ 2 * (pz f z θ) ^ 2 * w z ^ 2 * Real.sin (2 * θ) ^ (-(eta)) := by
    rw [mul_pow, mul_pow, hY]
    ring
  calc (pz f z θ) ^ 2 * Real.sin (2 * θ) ^ (-(eta))
      = ((pz f z θ) ^ 2 * Real.sin (2 * θ) ^ (-(eta))) * 1 := by rw [mul_one]
    _ ≤ ((pz f z θ) ^ 2 * Real.sin (2 * θ) ^ (-(eta))) *
          (b ^ 2 / (1 + a) ^ 4 * (z ^ 2 * w z ^ 2)) :=
        mul_le_mul_of_nonneg_left hfac (mul_nonneg hpz hS)
    _ = (b ^ 2 / (1 + a) ^ 4) *
          (DzIter 1 f z θ * (w z / Real.sin (2 * θ) ^ (eta / 2))) ^ 2 := by
        rw [hDz, hRw]; ring

end Work.FTS.CoercivityFix.Coer1T.Hardy.Pieces
