/-
# A positive lower bound for `‖LSeries axisChi4‖` just to the right of `σ = 1`

`axisChi4` is the quadratic character `χ₄` modulo `4`, and its `L`-series agrees with the
entire Dirichlet `L`-function `chi4C.LFunction` on `re s > 1`.  Since `χ₄` is a nontrivial
real primitive character, `chi4C.LFunction 1 ≠ 0` (indeed `L(1, χ₄) = π/4`), and
`chi4C.LFunction` is continuous at `1`.  Hence there is a neighbourhood of the real point
`σ = 1` on which `‖chi4C.LFunction (σ : ℂ)‖ ≥ ‖chi4C.LFunction 1‖ / 2 > 0`, which is the
claimed lower bound.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.axisChi4_LSeries_facts

namespace Work.FIArea6Hecke.R

open Complex
open scoped BigOperators

theorem axisChi4_LSeries_lower_bound_near_one :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ σ : ℝ, 1 < σ → σ < 1 + δ →
      c ≤ ‖LSeries Work.FIArea6Hecke.R.axisChi4 (σ : ℂ)‖ := by
  -- `chi4C.LFunction 1 ≠ 0`, hence its norm is strictly positive.
  have hne1 : chi4C.LFunction 1 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re chi4C (Or.inl chi4C_ne_one) le_rfl
  have hpos1 : 0 < ‖chi4C.LFunction 1‖ := norm_pos_iff.mpr hne1
  -- The `L`-function is continuous.
  have hcont : Continuous (fun s : ℂ => chi4C.LFunction s) :=
    (DirichletCharacter.differentiable_LFunction chi4C_ne_one).continuous
  -- The real function `σ ↦ ‖chi4C.LFunction (σ : ℂ)‖` is continuous at `1`.
  set g : ℝ → ℝ := fun σ => ‖chi4C.LFunction (σ : ℂ)‖ with hg
  have hgcont : ContinuousAt g 1 := by
    have hthis := (hcont.comp Complex.continuous_ofReal).continuousAt (x := (1 : ℝ))
    simpa [g] using hthis.norm
  have hg1 : g 1 = ‖chi4C.LFunction 1‖ := by simp [g]
  -- Epsilon–delta continuity gives a `δ` with `g σ > ‖chi4C.LFunction 1‖ / 2` on `(1-δ, 1+δ)`.
  rw [Metric.continuousAt_iff] at hgcont
  obtain ⟨δ, hδpos, hδ⟩ := hgcont (‖chi4C.LFunction 1‖ / 2) (by linarith)
  refine ⟨‖chi4C.LFunction 1‖ / 2, δ, by linarith, hδpos, ?_⟩
  intro σ h1 h2
  have hdist : dist σ 1 < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith : (0 : ℝ) < σ - 1)]
    linarith
  have hb := hδ hdist
  rw [hg1] at hb
  have hgt : ‖chi4C.LFunction 1‖ / 2 < g σ := by
    have := (abs_lt.mp hb).1
    linarith
  rw [LSeries_axisChi4_eq_LFunction (by simpa using h1)]
  exact le_of_lt hgt

end Work.FIArea6Hecke.R
