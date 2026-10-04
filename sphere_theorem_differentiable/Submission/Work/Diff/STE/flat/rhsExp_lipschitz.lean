/-
# The Galerkin right-hand side is Lipschitz and bounded near the initial datum

This file proves `Work.Diff.STE.flat.rhsExp_lipschitz`: the explicit Galerkin right-hand side
`a ↦ rhsExp Φ a`, whose entries are the Fourier coefficients of `x ↦ Φ (x, jetExp a x)`, is
Lipschitz on the ball `closedBall a₀ r` (with the *same* constant `K` as the hypothesis) and
bounded there.

The mathematics is elementary.  The hypothesis `hLip` controls the *joint* dependence on
`(a, x)` on `closedBall a₀ r ×ˢ closedCube n`.  Since the Fourier coefficient of a function on
the torus is the integral over the (half-open) unit cube `(0,1]ⁿ ⊂ [0,1]ⁿ`, and the characters
have modulus one, the sup-norm estimate

`‖Φ (x, jetExp a x) - Φ (x, jetExp a' x)‖ ≤ K * ‖a - a'‖`

on `closedCube n` passes to the coefficients (`norm_fourierCoeff_sub_le`), giving

`‖rhsExp Φ a - rhsExp Φ a'‖ ≤ K * ‖a - a'‖`.

The only side condition of `norm_fourierCoeff_sub_le` is continuity of the two entry functions on
`closedCube n`, which is immediate from `hLip` (it is Lipschitz in `x` there).

Boundedness on the ball then follows from the Lipschitz bound at the centre `a₀`.
-/
import Mathlib
import Submission.Work.Diff.STE.flat.GalerkinDefs
import Submission.Work.Diff.STE.flat.norm_fourierCoeff_sub_le
import Submission.Work.Diff.STE.LayerA

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open scoped BigOperators

/-- The half-open unit cube `(0,1]ⁿ` is contained in the closed cube `[0,1]ⁿ`. -/
lemma unitCube_subset_closedCube (n : ℕ) :
    Work.Diff.STE.unitCube (ι := Fin n) ⊆ Work.Diff.STE.Flat.Galerkin.closedCube n := by
  intro x hx
  simp only [Work.Diff.STE.unitCube, Work.Diff.STE.Flat.Galerkin.closedCube, Set.mem_pi,
    Set.mem_univ, true_implies] at hx ⊢
  exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩

/-- **Lipschitz in the space variable at a fixed coefficient family.**  If `a` is in the ball on
which the joint Lipschitz hypothesis holds, then `x ↦ Φ (x, jetExp a x)` is `K`-Lipschitz on the
closed cube (the second coordinate of the product metric does all the work). -/
lemma lipschitzOnWith_fixed_coeff {n N : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (K : NNReal) (r : NNReal) (a₀ : Work.Diff.STE.Flat.Galerkin.Coeff n N)
    (hLip : LipschitzOnWith K
      (fun p : Work.Diff.STE.Flat.Galerkin.Coeff n N × (Fin n → ℝ) =>
        Φ (p.2, Work.Diff.STE.Flat.Galerkin.jetExp p.1 p.2))
      (Metric.closedBall a₀ (r : ℝ) ×ˢ Work.Diff.STE.Flat.Galerkin.closedCube n))
    {a : Work.Diff.STE.Flat.Galerkin.Coeff n N} (ha : a ∈ Metric.closedBall a₀ (r : ℝ)) :
    LipschitzOnWith K (fun x : Fin n → ℝ => Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a x))
      (Work.Diff.STE.Flat.Galerkin.closedCube n) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have h := hLip.dist_le_mul (a, x) ⟨ha, hx⟩ (a, y) ⟨ha, hy⟩
  rwa [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] at h

/-- Continuity on the closed cube of a single entry of `x ↦ Φ (x, jetExp a x)`, from the Lipschitz
hypothesis.  This is the side condition of `norm_fourierCoeff_sub_le`. -/
lemma continuousOn_entry {n N : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (K : NNReal) (r : NNReal) (a₀ : Work.Diff.STE.Flat.Galerkin.Coeff n N)
    (hLip : LipschitzOnWith K
      (fun p : Work.Diff.STE.Flat.Galerkin.Coeff n N × (Fin n → ℝ) =>
        Φ (p.2, Work.Diff.STE.Flat.Galerkin.jetExp p.1 p.2))
      (Metric.closedBall a₀ (r : ℝ) ×ˢ Work.Diff.STE.Flat.Galerkin.closedCube n))
    {a : Work.Diff.STE.Flat.Galerkin.Coeff n N} (ha : a ∈ Metric.closedBall a₀ (r : ℝ))
    (i j : Fin n) :
    ContinuousOn (fun x : Fin n → ℝ => Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a x) i j)
      (Work.Diff.STE.Flat.Galerkin.closedCube n) := by
  have hproj : Continuous fun M : Work.Diff.STE.Flat.MatC n => M i j :=
    (continuous_apply j).comp (continuous_apply i)
  exact hproj.comp_continuousOn
    (lipschitzOnWith_fixed_coeff Φ K r a₀ hLip ha).continuousOn

theorem rhsExp_lipschitz {n N : ℕ}
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (K : NNReal) (r : NNReal) (hr : 0 < r) (a₀ : Work.Diff.STE.Flat.Galerkin.Coeff n N)
    (hLip : LipschitzOnWith K
      (fun p : Work.Diff.STE.Flat.Galerkin.Coeff n N × (Fin n → ℝ) =>
        Φ (p.2, Work.Diff.STE.Flat.Galerkin.jetExp p.1 p.2))
      (Metric.closedBall a₀ (r : ℝ) ×ˢ Work.Diff.STE.Flat.Galerkin.closedCube n)) :
    ∃ K' : NNReal, LipschitzOnWith K' (Work.Diff.STE.Flat.Galerkin.rhsExp Φ)
        (Metric.closedBall a₀ (r : ℝ)) ∧
      ∃ L : NNReal, ∀ a ∈ Metric.closedBall a₀ (r : ℝ),
        ‖Work.Diff.STE.Flat.Galerkin.rhsExp Φ a‖ ≤ L := by
  classical
  -- the core estimate: the difference of the right-hand sides is controlled by `K * ‖a - a'‖`
  have key : ∀ a a' : Work.Diff.STE.Flat.Galerkin.Coeff n N,
      a ∈ Metric.closedBall a₀ (r : ℝ) → a' ∈ Metric.closedBall a₀ (r : ℝ) →
      ‖Work.Diff.STE.Flat.Galerkin.rhsExp Φ a - Work.Diff.STE.Flat.Galerkin.rhsExp Φ a'‖
        ≤ (K : ℝ) * ‖a - a'‖ := by
    intro a a' ha ha'
    set C : ℝ := (K : ℝ) * ‖a - a'‖ with hCdef
    have hC : 0 ≤ C := by
      rw [hCdef]; exact mul_nonneg K.coe_nonneg (norm_nonneg _)
    -- the pointwise bound on the cube, transferred to each entry of the right-hand side
    have hentry : ∀ k : Work.Diff.STE.Flat.box n N, ∀ i j : Fin n,
        ‖(Work.Diff.STE.Flat.Galerkin.rhsExp Φ a
            - Work.Diff.STE.Flat.Galerkin.rhsExp Φ a') k i j‖ ≤ C := by
      intro k i j
      have hpt : ∀ x ∈ Work.Diff.STE.unitCube (ι := Fin n),
          ‖Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a x) i j
              - Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a' x) i j‖ ≤ C := by
        intro x hx
        have hx' : x ∈ Work.Diff.STE.Flat.Galerkin.closedCube n :=
          unitCube_subset_closedCube n hx
        have h := hLip.dist_le_mul (a, x) ⟨ha, hx'⟩ (a', x) ⟨ha', hx'⟩
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_eq_norm, dist_eq_norm] at h
        calc ‖Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a x) i j
                - Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a' x) i j‖
            = ‖(Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a x)
                  - Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a' x)) i j‖ := by simp
          _ ≤ ‖(Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a x)
                  - Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a' x)) i‖ := norm_le_pi_norm _ _
          _ ≤ ‖Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a x)
                  - Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a' x)‖ := norm_le_pi_norm _ _
          _ ≤ C := h
      have h := norm_fourierCoeff_sub_le
        (f := fun x => Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a x) i j)
        (g := fun x => Φ (x, Work.Diff.STE.Flat.Galerkin.jetExp a' x) i j)
        (continuousOn_entry Φ K r a₀ hLip ha i j)
        (continuousOn_entry Φ K r a₀ hLip ha' i j) hC hpt k.1
      exact h
    -- the sup norm on the coefficient space is the sup over the entries
    have hsup : ‖Work.Diff.STE.Flat.Galerkin.rhsExp Φ a
        - Work.Diff.STE.Flat.Galerkin.rhsExp Φ a'‖ ≤ C := by
      rw [pi_norm_le_iff_of_nonneg hC]
      intro k
      rw [pi_norm_le_iff_of_nonneg hC]
      intro i
      rw [pi_norm_le_iff_of_nonneg hC]
      intro j
      exact hentry k i j
    rw [hCdef] at hsup
    exact hsup
  refine ⟨K, ?_, ?_⟩
  · -- Lipschitz on the ball
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha a' ha'
    rw [dist_eq_norm, dist_eq_norm]
    exact key a a' ha ha'
  · -- bounded on the ball, from the bound at the centre
    have ha0 : a₀ ∈ Metric.closedBall a₀ (r : ℝ) := by
      rw [Metric.mem_closedBall, dist_self]; exact NNReal.coe_nonneg r
    refine ⟨⟨(K : ℝ) * r + ‖Work.Diff.STE.Flat.Galerkin.rhsExp Φ a₀‖,
      add_nonneg (mul_nonneg K.coe_nonneg (NNReal.coe_nonneg r)) (norm_nonneg _)⟩, ?_⟩
    intro a ha
    have h1 : ‖Work.Diff.STE.Flat.Galerkin.rhsExp Φ a
        - Work.Diff.STE.Flat.Galerkin.rhsExp Φ a₀‖ ≤ (K : ℝ) * ‖a - a₀‖ :=
      key a a₀ ha ha0
    have h2 : ‖a - a₀‖ ≤ (r : ℝ) := by
      have hr' := Metric.mem_closedBall.mp ha
      rwa [dist_eq_norm] at hr'
    have h3 : (K : ℝ) * ‖a - a₀‖ ≤ (K : ℝ) * r :=
      mul_le_mul_of_nonneg_left h2 K.coe_nonneg
    have h5 : ‖Work.Diff.STE.Flat.Galerkin.rhsExp Φ a‖
        ≤ (K : ℝ) * r + ‖Work.Diff.STE.Flat.Galerkin.rhsExp Φ a₀‖ := by
      calc ‖Work.Diff.STE.Flat.Galerkin.rhsExp Φ a‖
          = ‖(Work.Diff.STE.Flat.Galerkin.rhsExp Φ a
              - Work.Diff.STE.Flat.Galerkin.rhsExp Φ a₀)
              + Work.Diff.STE.Flat.Galerkin.rhsExp Φ a₀‖ := by ring_nf
        _ ≤ ‖Work.Diff.STE.Flat.Galerkin.rhsExp Φ a
              - Work.Diff.STE.Flat.Galerkin.rhsExp Φ a₀‖
              + ‖Work.Diff.STE.Flat.Galerkin.rhsExp Φ a₀‖ := norm_add_le _ _
        _ ≤ (K : ℝ) * r + ‖Work.Diff.STE.Flat.Galerkin.rhsExp Φ a₀‖ := by linarith
    exact h5

end Work.Diff.STE.flat
