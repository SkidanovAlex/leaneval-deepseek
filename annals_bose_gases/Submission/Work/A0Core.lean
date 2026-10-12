import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A₀-core algebra — the exact FS remainder-form conversion (sub-lemma (b) half)

FS `lm:appinteractionestimate` (final_v2.tex eq:A0) introduces, per small box
`B` (`|B| =: V`), the condensate quadratic

    A₀(n₀) := (n₀(n₀−1)/(2|B|²))·∬w₂ − (μn₀/|B|)·∬w₁
              − ¼(μ − (n₀+1)/|B|)²·∬w₁

whose per-sector surrogate (n₀ ↦ S := cS1, n₀(n₀−1) ↦ S²−S, with the corpus
values ∬w₁ = 8π·a v·V and ∬w₂ = V·∫g₂ = V·(8π·a v + D), D := ∫g₀·ω₀ ≥ 0
the `ĝω(0)`-mass, `FSKernelCompare.g2_integral_eq_av_add_g0w0`) reads

    A₀-form(S) := ½V⁻¹(8πa)(S²−S) − 8πa·μ·S
                  − ¼(μ − S·V⁻¹ − V⁻¹)²·(8πa·V) + ½V⁻¹·D·(S²−S) .

**`a0_form_square_identity`** — the EXACT algebraic conversion (the step FS
phrase as "using eq:w>g ... we find", performed here with the exact mass
identity, no box-boundary errors):

    A₀-form(S) = ¼(u−μ)²·(8πa·V) − ½μ²·(8πa·V)      [FS remainder main term]
                 + 4πa·(μ − 2u) − 2πa·V⁻¹            [n₀ ↔ n₀+1 & 1/V errors]
                 + ½V⁻¹·D·(S²−S)                      [the ĝω(0)-slack, D ≥ 0]

with u := S/V.  (`V := ℓ³`, i.e. the small-box volume; the identity is a
polynomial identity in the parameters — pure real algebra.)

**Corollary `a0_form_ge_fs_main`** — the remainder-group lower-bound form:
under `0 ≤ a`, `0 ≤ μ`, `0 ≤ u` the linear piece satisfies
`4πa(μ−2u) ≥ −4πa(μ+2u)`, so

    A₀-form(S) ≥ ¼(u−μ)²·(8πa·V) − ½μ²·(8πa·V)
                 − 4πa·(2u+μ) − 2πa·V⁻¹ + ½V⁻¹·D·(S²−S)

and the `−4πa(2u+μ) − 2πa·V⁻¹`-block is exactly the FS `Cμa(1+u/μ)`-type
error (absorbable in the box assembly; `2πa·V⁻¹ ≤ 2πa·μ` once `μV ≥ 1`).

This module is deliberately corpus-free (pure real).  The word-level lemma
that PRODUCES the `−¼(μ−u−1/V)²·(8πaV)`-term from q1word (the CS bound on
the `(ρ₀−μ)`-weighted one-body Q–P cross of eq:Q1n0, whose P-part evaluates
by `OneBodyMass.onebody_mass_condensate`) is the next step of the joint
q1/q2 assembly (design note Session-125 addendum).
-/

noncomputable section

open scoped Real

namespace Submission

set_option autoImplicit false

namespace BoseGases

/-- **Exact A₀ conversion** (pure real): with `V` the box volume, `S` the
condensate count, `u := S/V`, `a` the scattering length, `μ` the chemical
potential and `D` the `∫g₀ω₀`-mass (so `∬w₁ = 8πaV`,
`∬w₂ = 8πaV + V·D`), the A₀-form equals the FS remainder main term
`¼(u−μ)²·8πaV − ½μ²·8πaV` plus the explicit `n₀↔n₀+1`/`1/V`-errors
`4πa(μ−2u) − 2πa·V⁻¹` and the nonneg `ĝω(0)`-slack `½V⁻¹D(S²−S)`. -/
lemma a0_form_square_identity (V S μ a D : ℝ) (hV : V ≠ 0) :
    (1 / 2 : ℝ) * V⁻¹ * (8 * π * a) * (S ^ 2 - S)
        - (8 * π * a) * μ * S
        - (1 / 4 : ℝ) * (μ - S * V⁻¹ - V⁻¹) ^ 2 * (8 * π * a * V)
        + (1 / 2 : ℝ) * V⁻¹ * D * (S ^ 2 - S)
      = (1 / 4 : ℝ) * (S * V⁻¹ - μ) ^ 2 * (8 * π * a * V)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * a * V)
        + 4 * π * a * (μ - 2 * (S * V⁻¹))
        - 2 * π * a * V⁻¹
        + (1 / 2 : ℝ) * V⁻¹ * D * (S ^ 2 - S) := by
  field_simp [hV]
  ring

/-- **FS remainder-form lower bound**: under `0 ≤ a`, `0 ≤ μ`, `0 ≤ S`,
`0 < V` the A₀-form is at least the FS main term minus the
`Cμa(1+u/μ)`-type block `4πa·(2u+μ) + 2πa·V⁻¹` (plus the nonneg-slack
`½V⁻¹D(S²−S)`, which the downstream eq:w>g/`A₂`-absorption consumes). -/
lemma a0_form_ge_fs_main (V S μ a D : ℝ) (hV : 0 < V) (hμ : 0 ≤ μ)
    (ha : 0 ≤ a) :
    (1 / 4 : ℝ) * (S * V⁻¹ - μ) ^ 2 * (8 * π * a * V)
        - (1 / 2 : ℝ) * μ ^ 2 * (8 * π * a * V)
        - 4 * π * a * (2 * (S * V⁻¹) + μ)
        - 2 * π * a * V⁻¹
        + (1 / 2 : ℝ) * V⁻¹ * D * (S ^ 2 - S)
      ≤ (1 / 2 : ℝ) * V⁻¹ * (8 * π * a) * (S ^ 2 - S)
        - (8 * π * a) * μ * S
        - (1 / 4 : ℝ) * (μ - S * V⁻¹ - V⁻¹) ^ 2 * (8 * π * a * V)
        + (1 / 2 : ℝ) * V⁻¹ * D * (S ^ 2 - S) := by
  have hlin : 4 * π * a * (μ - 2 * (S * V⁻¹)) ≥ - 4 * π * a * (2 * (S * V⁻¹) + μ) := by
    have hc : 0 ≤ 4 * π * a := by positivity
    have hcmp : - (2 * (S * V⁻¹) + μ) ≤ μ - 2 * (S * V⁻¹) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hcmp hc]
  have hid := a0_form_square_identity V S μ a D (ne_of_gt hV)
  nlinarith

/-- **FS Step-4 pure-real atom** (the `n₀`-replacement inequality of
`lm:appinteractionestimate`, final_v2.tex ~3745): for `0 ≤ n`, `0 ≤ m`,

    n·(√(n+1) − √m)² ≤ (n+1 − m)² .

With `A := √(n+1)`, `B := √m` the difference is `(A−B)²·((A+B)²−n) ≥ 0`.
Used to pass from the CS term `−¼V⁻¹(√(n₀+1)−√(μV))²·(8πa·n₀)` to the A₀
quadratic `−¼((n₀+1)/V−μ)²·(8πaV)` (both sides scaled by the same `∬w₁/V²`). -/
lemma condensate_sqrt_square_le (n m : ℝ) (hn : 0 ≤ n) (hm : 0 ≤ m) :
    n * (Real.sqrt (n + 1) - Real.sqrt m) ^ 2 ≤ (n + 1 - m) ^ 2 := by
  have hn1 : 0 ≤ n + 1 := by nlinarith
  let A : ℝ := Real.sqrt (n + 1)
  let B : ℝ := Real.sqrt m
  have hA : 0 ≤ A := Real.sqrt_nonneg (n + 1)
  have hB : 0 ≤ B := Real.sqrt_nonneg m
  have hA2 : A ^ 2 = n + 1 := by
    dsimp [A]
    rw [Real.sq_sqrt hn1]
  have hB2 : B ^ 2 = m := by
    dsimp [B]
    rw [Real.sq_sqrt hm]
  have hdiff : (n + 1 - m) ^ 2 - n * (A - B) ^ 2 = (A - B) ^ 2 * ((A + B) ^ 2 - n) := by
    nlinarith [hA2, hB2]
  have h1 : 0 ≤ (A - B) ^ 2 := sq_nonneg (A - B)
  have h2 : 0 ≤ (A + B) ^ 2 - n := by
    have hAB : 0 ≤ A + B := add_nonneg hA hB
    have hnn : n ≤ (A + B) ^ 2 := by
      have hAsq : n + 1 ≤ (A + B) ^ 2 := by
        calc
          n + 1 = A ^ 2 := hA2.symm
          _ ≤ (A + B) ^ 2 := by
            have hB0 : 0 ≤ 2 * A * B + B ^ 2 := by positivity
            nlinarith
      nlinarith
    nlinarith
  have hprod : 0 ≤ (A - B) ^ 2 * ((A + B) ^ 2 - n) := mul_nonneg h1 h2
  nlinarith


/-- **Step-4 P-part (A₀-quadratic coefficient)**: the CS-P-part of the
eq:Q1n0 w₁-line, `−¼V⁻¹(√(S+1)−√(μV))²·(8πa·S)` (`S := cS1`, `V := ℓ³`,
`∬w₁ = 8πaV`), is at least the A₀-quadratic piece
`−¼V⁻¹(8πa)·(S+1−μV)² = −¼((S+1)/V−μ)²·(8πaV)` — the
`condensate_sqrt_square_le` (`S(√(S+1)−√m)² ≤ (S+1−m)²`) multiplied by the
nonpositive coefficient.  This is the step that joins the CS to the
`−¼(μ−u−1/V)²·8πaV`-term of A₀ (`A0Core.a0_form_square_identity`). -/
lemma step4_Ppart_quadratic (a V S m : ℝ) (ha : 0 ≤ a) (hV : 0 < V)
    (hS : 0 ≤ S) (hm : 0 ≤ m) :
    - (1 / 4 : ℝ) * V⁻¹ * (8 * π * a) * S * (Real.sqrt (S + 1) - Real.sqrt m) ^ 2
      ≥ - (1 / 4 : ℝ) * V⁻¹ * (8 * π * a) * (S + 1 - m) ^ 2 := by
  have hsq := condensate_sqrt_square_le S m hS hm
  have hcoef : 0 ≤ (1 / 4 : ℝ) * V⁻¹ * (8 * π * a) := by
    have hpi : 0 ≤ (1 / 4 : ℝ) * (8 * π) := by positivity
    positivity
  have hmul := mul_le_mul_of_nonneg_left hsq hcoef
  -- hmul : (1/4)V⁻¹(8πa)·S·(…)² ≤ (1/4)V⁻¹(8πa)(S+1−m)²
  nlinarith

end BoseGases

end Submission