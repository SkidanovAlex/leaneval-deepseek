import Mathlib
import Submission.Work.NN.Core.Main
import Submission.Work.NN.Core.exists_dbarDataBound

/-!
# The analytic core from a uniform family of small-ball solvers

This module composes the headline `Work.NN.Core.local_holomorphic_functions` with the automatic
Hölder datum bound `Work.NN.Core.exists_dbarDataBound`: a caller who can supply `∂̄_J`-solvers on
every small ball with a *uniform* constant `C₁` needs no explicit datum bound and no explicit
smallness hypothesis — they are met automatically by choosing the radius small.
-/

open LeanEval.Geometry.NewlanderNirenberg
open Submission
open Set
open scoped ContDiff Topology

namespace Work.NN.Core

variable {n : ℕ}

/-- **Convenience form of the analytic core.**  If on every small ball there is a `∂̄_J`-solver
`DbarSolverH n J α (ball 0 r) (ball 0 (r/2))` with `C₀` bounded by a constant `C₁` independent of
`r`, then the analytic core holds.  Indeed the datum `∂̄_J z_j` is `C^{0,α}`-small on a small ball
(`exists_dbarDataBound`), so the smallness hypothesis `C₀ δ ‖tupleDerivInv T‖ < 1` can be met by
shrinking the ball. -/
theorem local_holomorphic_functions_of_ball_solver {U : Set (E n)}
    {J : E n → E n →L[ℝ] E n} {T : E n ≃L[ℝ] F n}
    (hU : IsOpen U) (hJ : IsAlmostComplexOn J U) (hN : NijenhuisVanishesOn J U)
    (hT : ∀ v : E n, T (J 0 v) = Complex.I • T v)
    (h0U : (0 : E n) ∈ U)
    (hA : ContDiffAt ℝ 1 (perturbation J T) 0)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (H : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ r : ℝ, 0 < r →
      ∃ S : DbarSolverH n J α (Metric.ball (0 : E n) r) (Metric.ball (0 : E n) (r / 2)),
        S.C₀ ≤ C₁) :
    ∃ V : Set (E n), IsOpen V ∧ 0 ∈ V ∧ V ⊆ U ∧
      ∃ u : Fin n → E n → ℂ, IsHolomorphicFrame J V u := by
  obtain ⟨C₁, hC₁0, H⟩ := H
  set κ : ℝ := max C₁ 1 * (‖tupleDerivInv T‖ + 1) with hκdef
  have hκpos : 0 < κ := by
    rw [hκdef]
    have h1 : 0 < max C₁ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have h2 : 0 < ‖tupleDerivInv T‖ + 1 := by have := norm_nonneg (tupleDerivInv T); linarith
    exact mul_pos h1 h2
  refine local_holomorphic_functions_of_exists hU hJ hN hT ?_
  -- choose the radius: small enough for the datum bound and inside `U`
  obtain ⟨r₁, hr₁pos, hdata₁⟩ :=
    exists_dbarDataBound (n := n) (T := T) (J := J) hα0 hα1 hT hA (1 / (κ + 1)) (by positivity)
  obtain ⟨ε, hεpos, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0U)
  set r : ℝ := min r₁ ε with hrdef
  have hrpos : 0 < r := lt_min hr₁pos hεpos
  have hrε : r ≤ ε := min_le_right _ _
  have hrr₁ : r ≤ r₁ := min_le_left _ _
  -- the datum is small on the small ball
  have hdata : DbarDataBound J (zvec T) α (Metric.ball (0 : E n) r) (1 / (κ + 1)) :=
    dbarDataBound_mono hdata₁ (Metric.ball_subset_ball hrr₁)
  obtain ⟨S, hSC⟩ := H r hrpos
  -- the smallness condition
  have hsmall : S.C₀ * (1 / (κ + 1)) * ‖tupleDerivInv T‖ < 1 := by
    have hSmul : S.C₀ * (1 / (κ + 1)) * ‖tupleDerivInv T‖
        ≤ κ * (1 / (κ + 1)) := by
      rw [hκdef]
      have h1 : S.C₀ * (1 / (κ + 1)) * ‖tupleDerivInv T‖
          ≤ C₁ * (1 / (κ + 1)) * ‖tupleDerivInv T‖ := by
        have h2 : 0 ≤ (1 / (κ + 1)) * ‖tupleDerivInv T‖ := by positivity
        nlinarith [hSC, h2]
      have h3 : C₁ ≤ max C₁ 1 := le_max_left _ _
      have h4 : ‖tupleDerivInv T‖ ≤ ‖tupleDerivInv T‖ + 1 := by linarith [norm_nonneg (tupleDerivInv T)]
      have h5 : 0 < (1 / (κ + 1)) := by positivity
      have h6 : 0 ≤ (1 / (κ + 1)) * ‖tupleDerivInv T‖ := by positivity
      calc S.C₀ * (1 / (κ + 1)) * ‖tupleDerivInv T‖
          ≤ C₁ * (1 / (κ + 1)) * ‖tupleDerivInv T‖ := h1
        _ ≤ max C₁ 1 * (1 / (κ + 1)) * (‖tupleDerivInv T‖ + 1) := by
              have h7 : C₁ * (1 / (κ + 1)) ≤ max C₁ 1 * (1 / (κ + 1)) := by
                exact mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt h5)
              nlinarith [h7, h4, h5, norm_nonneg (tupleDerivInv T), hC₁0]
        _ = κ * (1 / (κ + 1)) := by rw [hκdef]; ring
    have hlt : κ * (1 / (κ + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by linarith)]; linarith
    linarith
  refine ⟨Metric.ball (0 : E n) r, Metric.ball (0 : E n) (r / 2), α, 1 / (κ + 1), S,
    Metric.isOpen_ball, Metric.isOpen_ball, Metric.mem_ball_self (by linarith), ?_, hα0, hα1,
    by positivity, hdata, hsmall⟩
  intro y hy
  exact hεU (Metric.ball_subset_ball hrε (Metric.ball_subset_ball (by linarith) hy))

end Work.NN.Core
