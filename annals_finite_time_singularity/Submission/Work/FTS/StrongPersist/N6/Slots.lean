/-
# `Work.FTS.StrongPersist.N6.Slots`

The level-six single-slot dominations used by the `ℋ⁶` product rule.  These are the
verbatim level-six shifts of the `ℋ⁴`-versions in `Submission/Work/H2/T1Q/PwBdQ.lean`:

* `dzIter_sq_w_sq_le6`: `(D_z^j f)² w² ≤ HkIntegrand α 6 f` for `j ≤ 6`;
* `mixed_sq_w_sq_le_HkIntegrand6`: `(D_z^b D_θ^a f)² w² ≤ HkIntegrand α 6 f` for `a + b ≤ 6`;
* `mixed_sq_le_HkIntegrand6`: `(D_z^b D_θ^a f)² ≤ HkIntegrand α 6 f` for `a + b ≤ 6`.

Nothing new is proved here: the `ℋ⁶`-integrand contains the corresponding slot with the
weight `sin(2θ)^{-η/2}` (pure `D_z`-slots) resp. `Wt` (mixed slots), both of which are `≥ w`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.TransportS.SupDzAux.HalfLineWindow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The weighted square of a pure `D_z`-slot of order `≤ 6` is dominated by the
`ℋ⁶`-integrand. -/
theorem dzIter_sq_w_sq_le6 (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (j : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) (hj : j ≤ 6) :
    (DzIter j f z θ) ^ 2 * (w z) ^ 2 ≤ HkIntegrand α 6 f z θ := by
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hη : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(eta)) :=
    Work.H2.T1Q.one_le_rpow_neg hsin (Real.sin_le_one _) eta_nonneg
  calc (DzIter j f z θ) ^ 2 * (w z) ^ 2
      = (DzIter j f z θ) ^ 2 * (w z) ^ 2 * 1 := by ring
    _ ≤ (DzIter j f z θ) ^ 2 * (w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) :=
        mul_le_mul_of_nonneg_left hη (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (DzIter j f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 := by
        rw [mul_pow, Work.H2.T1Q.div_rpow_sq (w z) (Real.sin (2 * θ)) eta hsin]
        ring
    _ ≤ HkIntegrand α 6 f z θ :=
        sq_le_HkIntegrand_z α 6 f z θ j hj

/-- On the open quadrant, the squared weighted mixed slot `(D_z^b D_θ^a f)² w²` of order
`a + b ≤ 6` is dominated by the `ℋ⁶`-integrand of `f`. -/
theorem mixed_sq_w_sq_le_HkIntegrand6 (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (b a : ℕ)
    (hab : a + b ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (mixed b a f z θ) ^ 2 * (w z) ^ 2 ≤ HkIntegrand α 6 f z θ := by
  have hθIθ : θ ∈ Iθ := ⟨le_of_lt hθ0, le_of_lt hθ1⟩
  have hsin : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [mixed_zero_right]
    have h1 : (1 : ℝ) ≤ (Real.sin (2 * θ)) ^ (-(eta)) :=
      Work.H2.T1Q.one_le_rpow_neg hsin hs1 eta_nonneg
    have hrew : (DzIter b f z θ
          * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        = (DzIter b f z θ) ^ 2 * (w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-(eta)) := by
      rw [mul_pow, Work.H2.T1Q.div_rpow_sq (w z) (Real.sin (2 * θ)) eta hsin]
      ring
    have hz2 := sq_le_HkIntegrand_z α 6 f z θ b (by omega)
    rw [hrew] at hz2
    calc (DzIter b f z θ) ^ 2 * (w z) ^ 2
        ≤ (DzIter b f z θ) ^ 2 * (w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(eta)) :=
          le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)) h1
      _ ≤ HkIntegrand α 6 f z θ := hz2
  · calc (mixed b a f z θ) ^ 2 * (w z) ^ 2
        ≤ (mixed b a f z θ) ^ 2 * (Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_left
            (Work.H2.T1Q.w_sq_le_Wt_sq α hα hθIθ hsin) (sq_nonneg _)
      _ = (mixed b a f z θ * Wt α z θ) ^ 2 := (mul_pow _ _ 2).symm
      _ ≤ HkIntegrand α 6 f z θ :=
          sq_le_HkIntegrand_mixed α 6 f z θ a b ha (by omega)

/-- On the open quadrant, the squared mixed slot itself is dominated by the `ℋ⁶`-integrand. -/
theorem mixed_sq_le_HkIntegrand6 (α : ℝ) (hα : 0 < α) (f : ℝ → ℝ → ℝ) (b a : ℕ)
    (hab : a + b ≤ 6) {z θ : ℝ} (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (mixed b a f z θ) ^ 2 ≤ HkIntegrand α 6 f z θ := by
  calc (mixed b a f z θ) ^ 2
      = (mixed b a f z θ) ^ 2 * 1 := by ring
    _ ≤ (mixed b a f z θ) ^ 2 * (w z) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        nlinarith [Work.FTS.TransportS.one_le_w hz, Work.FTS.TransportS.w_pos_of_pos hz]
    _ ≤ HkIntegrand α 6 f z θ :=
        mixed_sq_w_sq_le_HkIntegrand6 α hα f b a hab hz hθ0 hθ1

end Work.FTS.StrongPersist.N6
