import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EpsEngine.IterContMeas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open Filter

set_option autoImplicit false

/-- The Picard iterates converge pointwise to the limit family, as soon as the increments
`wseq F h₀ n` (`n ≥ 1`) are dominated by a geometric sequence.  The proof is the telescoping
of the increments: the partial sums `∑_{n<N} wseq F h₀ (n+1)` are the tail of the sum whose
total is the (absolutely convergent) series defining `limFam`. -/
theorem tendsto_slice_iter_limFam {F : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn} {δ Cpt r : ℝ}
    (hCpt : 0 ≤ Cpt) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hwpt : ∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → 1 ≤ n → ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ n τ z θ| ≤ δ * Cpt * r ^ n) :
    ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Filter.Tendsto (fun N : ℕ => Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ N) τ z θ)
        Filter.atTop (nhds (Work.FTS.Galerkin.slice
          (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀) τ z θ)) := by
  intro τ hτ z θ hz hθ0 hθ1
  -- the geometric majorant is nonnegative: take `max (δ*Cpt) 0` in place of `δ*Cpt`
  have hrnorm : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  have hgeo : Summable (fun n : ℕ => max (δ * Cpt) 0 * r ^ (n + 1)) := by
    have h := (summable_geometric_of_norm_lt_one hrnorm).mul_left (max (δ * Cpt) 0 * r)
    refine h.congr (fun n => ?_)
    rw [pow_succ']; ring
  have hbnd : ∀ n : ℕ, |Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ (n + 1) τ z θ|
      ≤ max (δ * Cpt) 0 * r ^ (n + 1) := by
    intro n
    refine le_trans (hwpt (n + 1) τ hτ (by omega) z θ hz hθ0 hθ1) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hr0 _)
  have hsumm : Summable
      (fun n : ℕ => Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ (n + 1) τ z θ) :=
    Summable.of_norm_bounded hgeo fun n => by rw [Real.norm_eq_abs]; exact hbnd n
  have htsum : HasSum (fun n : ℕ => Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ (n + 1) τ z θ)
      (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ
        - (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ)) := by
    have h2 : Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ
        - (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ)
        = ∑' n, Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ (n + 1) τ z θ := by
      simp only [Work.FTS.StrongEps.EpsLocalPStar.limFam]
      ring
    rw [h2]
    exact hsumm.hasSum
  have h1 := htsum.tendsto_sum_nat
  have h3 : Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.range N,
          Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ (n + 1) τ z θ)
        + (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ))
      Filter.atTop (nhds (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ)) := by
    have h := h1.add_const (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ)
    have h4 : (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ
        - (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ))
        + (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ)
        = Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ := by ring
    rw [h4] at h
    exact h
  have heq : (fun N : ℕ => (∑ n ∈ Finset.range N,
        Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ (n + 1) τ z θ)
      + (h₀ z θ + Work.FTS.StrongEps.EpsLocalPStar.wseq F h₀ 0 τ z θ))
      =ᶠ[Filter.atTop] (fun N : ℕ => Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (N + 1)) τ z θ) := by
    filter_upwards with N
    rw [Work.FTS.StrongEps.EpsLocalPStar.sum_wseq_shift]
    ring
  have htend : Filter.Tendsto (fun N : ℕ => Work.FTS.Galerkin.slice
      (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (N + 1)) τ z θ) Filter.atTop
      (nhds (Work.FTS.StrongEps.EpsLocalPStar.limFam F h₀ z θ τ)) :=
    (Filter.tendsto_congr' heq).mp h3
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp htend

end Work.FTS.EpsEngine
