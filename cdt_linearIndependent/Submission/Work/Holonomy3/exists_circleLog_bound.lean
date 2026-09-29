import Mathlib
import Submission.Work.Holonomy3.comp_defs

/-!
# A uniform bound for `circleLog (φ p)` on `[0,1]`

For a finite family of admissible maps `φ p` (`p : Fin (l+1)`) the functions
`t ↦ circleLog (φ p) t = log ‖φ p (e^{2πit})‖` are continuous on `[0,1]` and share a common
nonnegative bound `G₀`.

Continuity: `t ↦ e^{2πit}` is continuous and takes values on the unit circle, hence in the closed
unit disc, on which `φ p` is continuous; composing gives continuity of `t ↦ φ p (e^{2πit})`, and the
norm of that function is everywhere nonzero because `φ p` is zero-free on the unit circle and
`‖e^{2πit}‖ = 1`.  `Real.log` is continuous on the positive reals.

The bound: each `circleLog (φ p)` is continuous on the compact interval `[0,1]`, hence bounded
there; since `Fin (l+1)` is finite, the supremum of the finitely many bounds is a common bound.
-/

namespace Work.Holonomy3

open Complex Metric Filter Topology
open scoped BigOperators

theorem exists_circleLog_bound {l : ℕ} (φ : Fin (l + 1) → ℂ → ℂ)
    (hadm : ∀ k, Submission.CDTPlan.AdmissibleMap (φ k)) :
    ∃ G₀ : ℝ, 0 ≤ G₀ ∧
      (∀ p, ContinuousOn (Submission.CDTPlan.circleLog (φ p)) (Set.Icc 0 1)) ∧
      ∀ p t, t ∈ Set.Icc 0 1 → |Submission.CDTPlan.circleLog (φ p) t| ≤ G₀ := by
  -- the circle parametrisation `t ↦ e^{2πit}` and its unit modulus
  have hcirc : Continuous (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))) := by
    fun_prop
  have hcirc_norm : ∀ t : ℝ, ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]; simp
  -- `circleLog (φ p)` is continuous on `[0,1]`
  have hcont : ∀ p, ContinuousOn (Submission.CDTPlan.circleLog (φ p)) (Set.Icc 0 1) := by
    intro p
    have hmaps : Set.MapsTo (fun t : ℝ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))
        (Set.Icc 0 1) (Metric.closedBall (0 : ℂ) 1) := by
      intro t ht
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [hcirc_norm t]
    have hcomp : ContinuousOn
        (fun t : ℝ => φ p (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))) (Set.Icc 0 1) :=
      (hadm p).1.comp hcirc.continuousOn hmaps
    have hne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖φ p (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))‖ ≠ 0 := by
      intro t ht
      rw [norm_ne_zero_iff]
      exact (hadm p).2.2.2 _ (hcirc_norm t)
    change ContinuousOn
      (fun t : ℝ => Real.log ‖φ p (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)))‖)
      (Set.Icc 0 1)
    exact hcomp.norm.log hne
  -- per-index bounds on the compact interval
  obtain ⟨C, hC⟩ : ∃ C : Fin (l+1) → ℝ,
      ∀ p, ∀ t ∈ Set.Icc 0 1, ‖Submission.CDTPlan.circleLog (φ p) t‖ ≤ C p := by
    choose C hC using fun p => isCompact_Icc.exists_bound_of_continuousOn (hcont p)
    exact ⟨C, hC⟩
  refine ⟨max 0 (Finset.univ.sup' Finset.univ_nonempty C), le_max_left _ _, hcont, ?_⟩
  intro p t ht
  have h1 : |Submission.CDTPlan.circleLog (φ p) t| ≤ C p := by
    simpa [Real.norm_eq_abs] using hC p t ht
  have h2 : C p ≤ Finset.univ.sup' Finset.univ_nonempty C :=
    Finset.le_sup' C (Finset.mem_univ p)
  exact le_trans h1 (le_trans h2 (le_max_right _ _))

end Work.Holonomy3
