/-
Copyright: work module for the Elgindi finite-time singularity project.

# Elementary domination lemmas for the `sin(2θ)`-weights

Three elementary facts about the angular weight `s = sin(2θ)` on the quadrant, used by the
pointwise comparisons of the vanishing-family assembly:

* `sin_two_mem_Icc`: `s ∈ [0,1]` on `Iθ = [0,π/2]`;
* `sq_mul_sin_le_HkIntegrand_zero`: the **singular** (`η`-weighted) `ℋ^0`-integrand dominates
  any *vanishing* weight `s^a` with `a ≥ -η`:
  `(h z θ · w z)² · s^a ≤ HkIntegrand α 0 h z θ = (h z θ · w z / s^{η/2})²`;
* `sq_mul_sin_le_sq_mul_sin`: the *monotonicity in the exponent* of the vanishing weights on
  the quadrant: `b ≤ a` (both `≥ 0`) gives `(X²·s^a) ≤ (X²·s^b)`.

All proofs are elementary `rpow` algebra.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.ClassC.VanishFamilyDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false

/-- `sin(2θ) ∈ [0,1]` on the angular interval `Iθ = [0,π/2]`. -/
theorem sin_two_mem_Icc {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Real.sin (2 * θ) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨sin_two_nonneg_of_mem_Iθ' hθ, ?_⟩
  rw [Work.Spaces.Iθ] at hθ
  exact Real.sin_le_one _

/-- `sin(2θ) > 0` on the open interval `(0,π/2)`. -/
theorem sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `(s^{e/2})² = s^e` for `s > 0`. -/
theorem sq_rpow_half {s e : ℝ} (hs : 0 < s) : (s ^ (e / 2)) ^ 2 = s ^ e := by
  rw [sq, ← Real.rpow_add hs, show e / 2 + e / 2 = e by ring]

/-- The angular weight of `HkIntegrand α 0 h` is `(h·w)² · s^{-η}` on the open interval. -/
theorem HkIntegrand_zero_eq_sq_mul_rpow (α : ℝ) (h : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.HkIntegrand α 0 h z θ
      = (h z θ * Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  rw [HkIntegrand_zero_eq_classC, div_eq_mul_inv, mul_pow, mul_pow, inv_pow,
    sq_rpow_half hs, ← Real.rpow_neg (le_of_lt hs)]
  ring

/-- **Domination of a vanishing weight by the singular `ℋ^0`-integrand**: for `a ≥ -η`,
`(h·w)²·s^a ≤ HkIntegrand α 0 h` on the open interval. -/
theorem sq_mul_sin_le_HkIntegrand_zero (α : ℝ) (h : ℝ → ℝ → ℝ) {z θ : ℝ} {a : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (ha : -(Work.Spaces.eta) ≤ a) :
    (h z θ * Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ a
      ≤ Work.Spaces.HkIntegrand α 0 h z θ := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := (sin_two_mem_Icc ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩).2
  rw [HkIntegrand_zero_eq_sq_mul_rpow α h hθ]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 ha

/-- **Monotonicity in the exponent of the vanishing weights**, on the open interval:
for `0 ≤ b ≤ a`, the weight `s^b` dominates `s^a`. -/
theorem sq_mul_sin_le_sq_mul_sin {X θ : ℝ} {a b : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (_hb : 0 ≤ b) (hba : b ≤ a) :
    X ^ 2 * (Real.sin (2 * θ)) ^ a ≤ X ^ 2 * (Real.sin (2 * θ)) ^ b := by
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem_Ioo hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := (sin_two_mem_Icc ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩).2
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_ge hs hs1 hba

end Work.FTS.ClassC
