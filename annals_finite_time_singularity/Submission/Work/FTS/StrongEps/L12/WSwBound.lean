import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.GalBasis.cc.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.L12

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Two elementary monotonicity facts

* `Work.Spaces.w z = (1+z)²/z² = (1 + 1/z)²` is antitone on `(0,∞)`;
* on `[ε, π/2-ε]` (with `ε ≤ π/4`) the function `θ ↦ sin(2θ)` stays above `sin(2ε)`,
  by symmetry about `θ = π/4` and monotonicity of `sin` on `[0,π/2]`.
-/

/-- `Work.Spaces.w` is antitone on the positive halfline: `w b ≤ w a` for `0 < a ≤ b`,
because `w z = (1 + 1/z)²` and `z ↦ 1 + 1/z` is antitone and nonnegative there. -/
theorem w_le_w_of_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Work.Spaces.w b ≤ Work.Spaces.w a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hb' : Work.Spaces.w b = (1 + 1 / b) ^ 2 := by
    rw [Work.Spaces.w]
    field_simp
    ring
  have ha' : Work.Spaces.w a = (1 + 1 / a) ^ 2 := by
    rw [Work.Spaces.w]
    field_simp
    ring
  rw [hb', ha']
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  have h : 1 / b ≤ 1 / a := one_div_le_one_div_of_le ha hab
  linarith

/-- On the middle interval `[ε, π/2-ε]`, `sin(2·) ≥ sin(2ε)` when `ε ≤ π/4`.  Indeed
`sin(2θ) = sin(π - 2θ)` and both `2θ` (when `2θ ≤ π/2`) and `π - 2θ` (when `2θ ≥ π/2`)
lie in `[2ε, π/2]`. -/
theorem sin_two_le_sin_two {ε θ : ℝ} (hε : 0 < ε) (hε4 : ε ≤ π / 4) (h1 : ε ≤ θ)
    (h2 : θ ≤ π / 2 - ε) : Real.sin (2 * ε) ≤ Real.sin (2 * θ) := by
  have hp := Real.pi_pos
  rcases le_or_gt (2 * θ) (π / 2) with hcase | hcase
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hcase (by linarith)
  · rw [show Real.sin (2 * θ) = Real.sin (π - 2 * θ) from (Real.sin_pi_sub (2 * θ)).symm]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

/-- `Sw θ = sin(2θ)^{η/2}` is monotone on the middle interval `[ε, π/2-ε]`, `ε ≤ π/4`. -/
theorem Sw_le_Sw_of_mem {ε θ : ℝ} (hε : 0 < ε) (hε4 : ε ≤ π / 4) (h1 : ε ≤ θ)
    (h2 : θ ≤ π / 2 - ε) : Work.FTS.GalBasis.cc.Sw ε ≤ Work.FTS.GalBasis.cc.Sw θ := by
  have hsin : 0 ≤ Real.sin (2 * ε) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hexp : 0 ≤ Work.Spaces.eta / 2 := by norm_num [Work.Spaces.eta]
  exact Real.rpow_le_rpow hsin (sin_two_le_sin_two hε hε4 h1 h2) hexp

/-- `Sw` is positive in the interior of the angular interval. -/
theorem Sw_pos_of_pos {θ : ℝ} (h1 : 0 < θ) (h2 : θ < π / 2) :
    0 < Work.FTS.GalBasis.cc.Sw θ := by
  refine Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi ?_ ?_) _
  · linarith
  · linarith [Real.pi_pos]

/-- namespace `Work.FTS.StrongEps.L12`, declaration name `WSwBound`.
The weight ratio `w s / Sw θ` (with `w s = (1+s)²/s²` and `Sw θ = sin(2θ)^{η/2}`) is bounded on the
box `[δ,R] × [ε, π/2-ε]` uniformly in `R` by its value at the corner `(δ, ε)`, for `ε ≤ π/4`.
Indeed `w` is antitone on `(0,∞)` (it equals `(1+1/s)²`), and on `[ε, π/2-ε]` one has
`sin(2θ) ≥ sin(2ε)` because `2θ ∈ [2ε, π-2ε]` with `2ε ≤ π/2`, so
`Sw θ = sin(2θ)^{η/2} ≥ Sw ε > 0`; dividing the two inequalities gives the claim. -/
theorem WSwBound (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hε4 : ε ≤ π / 4) :
    ∀ s θ : ℝ, δ ≤ s → ε ≤ θ → θ ≤ π / 2 - ε →
      Work.Spaces.w s / Work.FTS.GalBasis.cc.Sw θ
        ≤ Work.Spaces.w δ / Work.FTS.GalBasis.cc.Sw ε := by
  intro s θ hs h1 h2
  have hw : Work.Spaces.w s ≤ Work.Spaces.w δ := w_le_w_of_le hδ hs
  have hSw : Work.FTS.GalBasis.cc.Sw ε ≤ Work.FTS.GalBasis.cc.Sw θ :=
    Sw_le_Sw_of_mem hε hε4 h1 h2
  have hSwe : 0 < Work.FTS.GalBasis.cc.Sw ε :=
    Sw_pos_of_pos hε (by linarith [hε4, Real.pi_pos])
  have hSwt : 0 < Work.FTS.GalBasis.cc.Sw θ :=
    Sw_pos_of_pos (lt_of_lt_of_le hε h1) (by linarith [hε, Real.pi_pos])
  have hinv : (Work.FTS.GalBasis.cc.Sw θ)⁻¹ ≤ (Work.FTS.GalBasis.cc.Sw ε)⁻¹ :=
    (inv_le_inv₀ hSwt hSwe).mpr hSw
  have hwδ : 0 ≤ Work.Spaces.w δ := by
    rw [Work.Spaces.w]; positivity
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul hw hinv (by positivity) hwδ

end Work.FTS.StrongEps.L12
