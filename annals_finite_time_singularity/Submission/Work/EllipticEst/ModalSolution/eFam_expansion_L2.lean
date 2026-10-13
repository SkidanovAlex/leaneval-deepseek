import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_norm_fts
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.ModalSolution.eFam_parseval
import Submission.Work.EllipticEst.ModalSolution.eFam_pythagoras_alt
import Submission.Work.EllipticEst.ModalSolution.eFam_residual_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution

open MeasureTheory

/-- **Convergence of the modal expansion of a source slice in `L²(Iθ, cos θ dθ)`.**

The angular eigenfunctions `eFam m θ = cos θ · gC (2m+1) (sin θ)` are orthogonal for the weight
`cos θ` (`eFam_orthogonal`), have positive norms `∫ eFam m ^ 2 cos θ` (`eFam_norm_fts`) and are
*complete* (`eFam_complete`); hence they form an orthogonal basis of `L²(Iθ, cos θ dθ)` and the
Fourier expansion of a slice `θ ↦ F z θ` converges in that space.  Writing
`c m = cmode m F z` for the Fourier coefficient of the slice and `D m = ∫ eFam m ^ 2 cos θ`, the
two ingredients are

* `eFam_parseval`: `∑_{m ≤ N} c m ^ 2 * D m → ∫ F z θ ^ 2 cos θ` (Parseval);
* `eFam_pythagoras_alt`: `∫ (F z θ - ∑_{m ≤ N} c m eFam m θ) ^ 2 cos θ = ∫ F z θ ^ 2 cos θ - ∑_{m ≤ N} c m ^ 2 D m`
  (the truncated Pythagorean identity, i.e. the best-approximation property of the truncated
  expansion in the weighted `L²` space);

so the residuals of the truncations tend to `0`; `eFam_residual_integrable` supplies the
integrability needed to rewrite each `∫⁻` of an `ENNReal.ofReal` as the `ofReal` of the
corresponding real integral, and `ENNReal.continuous_ofReal` transfers the limit. -/
theorem eFam_expansion_L2 (F : ℝ → ℝ → ℝ) (z : ℝ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => F z θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hz : MeasureTheory.IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    Filter.Tendsto (fun N : ℕ => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal ((F z θ - ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ))
      Filter.atTop (nhds 0) := by
  -- The residual at truncation order `N`, as a real function of `θ`.
  have hL : Filter.Tendsto
      (fun N : ℕ => ∫ θ in Work.Spaces.Iθ,
        (F z θ - ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
            * Real.cos θ)
      Filter.atTop (nhds 0) := by
    -- Pythagoras turns the residual into `G - P N`, and Parseval gives `P N → G`.
    have hkey : (fun N : ℕ => ∫ θ in Work.Spaces.Iθ,
        (F z θ - ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
            * Real.cos θ)
        = fun N : ℕ => (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)
            - ∑ m ∈ Finset.range (N + 1), (Work.FTS.PhiStar.Series.cmode m F z) ^ 2 *
                (∫ θ in Work.Spaces.Iθ,
                  Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ) := by
      funext N
      exact eFam_pythagoras_alt F z N hmeas hz
    rw [hkey]
    have h1 : Filter.Tendsto (fun _ : ℕ => (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ))
        Filter.atTop (nhds (∫ θ in Work.Spaces.Iθ, F z θ ^ 2 * Real.cos θ)) :=
      tendsto_const_nhds
    have h2 := h1.sub (eFam_parseval F z hmeas hz)
    simpa using h2
  -- Integrability of every residual, and its non-negativity (`cos θ ≥ 0` on `Iθ`).
  have hint : ∀ N : ℕ, MeasureTheory.IntegrableOn
      (fun θ => (F z θ - ∑ m ∈ Finset.range (N + 1),
        Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
          * Real.cos θ) Work.Spaces.Iθ := fun N => eFam_residual_integrable F z N hmeas hz
  have hnn : ∀ N : ℕ, 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
      (fun θ => (F z θ - ∑ m ∈ Finset.range (N + 1),
        Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
          * Real.cos θ) := by
    intro N
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
      with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
  -- Each `∫⁻` of an `ENNReal.ofReal` is the `ofReal` of the real integral.
  have hEq : ∀ N : ℕ, ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        (F z θ - ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
            * Real.cos θ)
      = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((F z θ - ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
            * Real.cos θ) := by
    intro N
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint N) (hnn N)
  refine Filter.Tendsto.congr (fun N => hEq N) ?_
  have hfin : Filter.Tendsto
      (fun N : ℕ => ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
        (F z θ - ∑ m ∈ Finset.range (N + 1),
          Work.FTS.PhiStar.Series.cmode m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
            * Real.cos θ))
      Filter.atTop (nhds (ENNReal.ofReal 0)) :=
    (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hL
  simpa using hfin

end Work.EllipticEst.ModalSolution
