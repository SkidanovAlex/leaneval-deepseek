/-
Copyright: work module for the Elgindi finite-time singularity project.

# Domination of a single slot by the `ℋ⁶`-integrand, for an arbitrary angular weight

`HkIntegrand α 6 f` is (a sum of squares containing) each of the two block weights
times a single slot of `f`:

* `(D_z^j f · (w / sin(2θ)^{η/2}))²`   for `j ≤ 6`  (`Work.Spaces.sq_le_HkIntegrand_z`);
* `(D_z^j D_θ^i f · W)²`              for `1 ≤ i`, `i + j ≤ 6`
  (`Work.Spaces.sq_le_HkIntegrand_mixed`, `W = w · sin(2θ)^{-γ/2}`).

Here we prove that the *same* bound holds with the fixed angular weights replaced by an
arbitrary nonnegative angular weight `θw` that is *dominated* by the corresponding one:
`θw θ ≤ sin(2θ)^{-η}` in the `D_z`-case and `θw θ ≤ sin(2θ)^{-γ}` in the mixed case.  This is
the pointwise core of every "leaf weight" argument of the level-six rows: a weight that is
merely smaller than a block weight may be inserted in front of a single slot at no cost.

The only `rpow` algebra needed is `(a ^ p)² = a ^ (p · 2)` for `a ≥ 0`, together with the
definitional unfolding of the two block weights (`Wt = w · wTheta`, `wTheta α θ =
sin(2θ)^{-γ/2}`); after that the comparison is `mul_le_mul_of_nonneg_{left,right}`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- `(a ^ p) ^ 2 = a ^ (p * 2)` for `a ≥ 0`: the only `rpow` algebra needed below.  (Same
proof as `Work.FTS.H2.sq_rpow_mul_two`, reproduced here to keep the import cone small.) -/
private lemma sq_rpow_two {a : ℝ} (ha : 0 ≤ a) (p : ℝ) : (a ^ p) ^ 2 = a ^ (p * 2) := by
  rw [← Real.rpow_natCast (a ^ p) 2]
  exact (Real.rpow_mul ha p 2).symm

/-- `sin (2θ) ≥ 0` for `0 ≤ θ ≤ π/2`, in the strict form used here. -/
private lemma sin_two_nonneg {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩

theorem fkSlotDom : ∀ (α : ℝ) (f : ℝ → ℝ → ℝ),
    (∀ (j i : ℕ) (θw : ℝ → ℝ), 1 ≤ i → i + j ≤ 6 →
      (∀ θ ∈ Work.Spaces.Iθ, 0 ≤ θw θ) →
      (∀ θ ∈ Work.Spaces.Iθ, θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ) ∧
    (∀ (j : ℕ) (θw : ℝ → ℝ), j ≤ 6 →
      (∀ θ ∈ Work.Spaces.Iθ, 0 ≤ θw θ) →
      (∀ θ ∈ Work.Spaces.Iθ, θw θ ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter j f z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α 6 f z θ) := by
  intro α f
  constructor
  · -- ## mixed slots `(j, i)`, `1 ≤ i`, `i + j ≤ 6`, weight subordinate to `sin(2θ)^{-γ}`
    intro j i θw hi hij _hnn hle z θ _hz hθ0 hθ1
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ0 hθ1
    -- `(sin(2θ)^{-γ/2})² = sin(2θ)^{-γ}`
    have hgam : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      rw [sq_rpow_two hs]
      congr 1
      ring
    calc (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.mixed j i f z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Work.Spaces.mixed j i f z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hle θ hθI) (sq_nonneg _)) (sq_nonneg _)
      _ = (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          rw [Work.Spaces.Wt, Work.Spaces.wTheta]
          simp only [mul_pow, hgam]
          ring
      _ ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
          Work.Spaces.sq_le_HkIntegrand_mixed α 6 f z θ i j hi (by omega)
  · -- ## pure `D_z` slots `j`, `j ≤ 6`, weight subordinate to `sin(2θ)^{-η}`
    intro j θw hj _hnn hle z θ _hz hθ0 hθ1
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
    have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ0 hθ1
    -- `(sin(2θ)^{-η/2})² = sin(2θ)^{-η}`
    have heta : ((Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
        = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      rw [sq_rpow_two hs]
      congr 1
      ring
    calc (Work.Spaces.w z) ^ 2 * θw θ * (Work.Spaces.DzIter j f z θ) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            * (Work.Spaces.DzIter j f z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hle θ hθI) (sq_nonneg _)) (sq_nonneg _)
      _ = (Work.Spaces.DzIter j f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hs (Work.Spaces.eta / 2)]
          simp only [mul_pow, heta]
          ring
      _ ≤ Work.Spaces.HkIntegrand α 6 f z θ :=
          Work.Spaces.sq_le_HkIntegrand_z α 6 f z θ j (by omega)

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
