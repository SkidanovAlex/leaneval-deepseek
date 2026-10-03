/-
# Pointwise weighted bound for the smoothing weight `lipWeight`

`lipWeight ψ ε N' m = ε (N')⁻¹ ∑_{m' ∈ [1,N']} ψ(ε(m - m'))` is the coefficient of the
smoothing operator of Proposition `lip` of Krause--Mirek--Tao (§5).  This module proves the
*pointwise* weighted estimate

  `‖lipWeight ψ ε N' m‖ · max 0 (|m| - N')
     ≤ C (N')⁻¹ ∑_{y ∈ [1,N']} ε ⟨ε(m-y)⟩^{-12} |m - y|`

with a constant `C` depending only on `ψ`.  The point is that the weight away from the window
`[1,N']` gains the extra factor `(N')⁻¹` (this is the estimate used to bound the spatial tail of
the smoothed progression average).

The proof is elementary: `max 0 (|m| - N') ≤ |m - y|` for every `y ∈ [1,N']` (the distance to
the window is at most the distance to any point of the window), and Schwartz decay bounds each
summand `ψ(ε(m-y))` by `C ⟨ε(m-y)⟩^{-12}`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lipDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.KMTAreas.A4

/-- The distance from `m` to the window `[1,N']` is at most the distance from `m` to any point
`y` of the window. -/
lemma window_le_dist {N' : ℕ} {m : ℤ} {y : ℕ} (hy : y ∈ Finset.Icc 1 N') :
    max 0 (|(m : ℝ)| - (N' : ℝ)) ≤ |(m : ℝ) - (y : ℝ)| := by
  refine max_le (abs_nonneg _) ?_
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hy).1
  have hyN : (y : ℝ) ≤ (N' : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hy).2
  have htri : |(m : ℝ)| - |(y : ℝ)| ≤ |(m : ℝ) - (y : ℝ)| :=
    abs_sub_abs_le_abs_sub (m : ℝ) (y : ℝ)
  have hyabs : |(y : ℝ)| = (y : ℝ) := abs_of_nonneg (by positivity)
  rw [hyabs] at htri
  linarith

theorem lipWeightAbsMomentPointwise (ψ : Work.Analysis.InverseTheory.SchwartzR) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 → ∀ {N' : ℕ}, 1 ≤ N' → ∀ m : ℤ,
      ‖Work.KMTAreas.A4.lipWeight ψ ε N' m‖ * max 0 (|(m : ℝ)| - (N' : ℝ))
        ≤ C * (N' : ℝ)⁻¹
          * ∑ y ∈ Finset.Icc 1 N',
              ε * Work.Analysis.InverseTheory.jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))) * |(m : ℝ) - (y : ℝ)| := by
  refine ⟨(2 : ℝ) ^ 12 * (Work.Analysis.InverseTheory.schwartzSeminormSum ψ + 1), ?_, ?_⟩
  · have h := Work.Analysis.InverseTheory.schwartzSeminormSum_nonneg ψ; positivity
  · intro ε hε0 hε1 N' hN' m
    set C : ℝ := (2 : ℝ) ^ 12 * (Work.Analysis.InverseTheory.schwartzSeminormSum ψ + 1) with hCdef
    have hCpos : 0 < C := by
      rw [hCdef]
      have h := Work.Analysis.InverseTheory.schwartzSeminormSum_nonneg ψ
      positivity
    have hN'pos : (0 : ℝ) < (N' : ℝ) := by
      have h : (1 : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hN'
      linarith
    have hdecay : ∀ t : ℝ, ‖ψ t‖ ≤ C * Work.Analysis.InverseTheory.jbDecay 12 t := by
      intro t
      rw [hCdef]
      exact Work.Analysis.InverseTheory.schwartz_decay ψ t
    set X : ℝ := max 0 (|(m : ℝ)| - (N' : ℝ)) with hXdef
    have hXnonneg : 0 ≤ X := by rw [hXdef]; exact le_max_left 0 _
    have hεc : 0 ≤ ε * (N' : ℝ)⁻¹ :=
      mul_nonneg hε0.le (inv_nonneg.mpr hN'pos.le)
    -- Step 1: `‖lipWeight‖ ≤ ε (N')⁻¹ ∑_y ‖ψ(ε(m-y))‖`.
    have hnorm : ‖Work.KMTAreas.A4.lipWeight ψ ε N' m‖
        ≤ ε * (N' : ℝ)⁻¹ * ∑ y ∈ Finset.Icc 1 N', ‖ψ (ε * ((m : ℝ) - (y : ℝ)))‖ := by
      have hεnorm : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_of_nonneg hε0.le]
      have hcnorm : ‖(((N' : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N' : ℝ)⁻¹ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hN'pos.le)]
      have hsum : ‖∑ y ∈ Finset.Icc 1 N', ψ (ε * ((m : ℝ) - (y : ℝ)))‖
          ≤ ∑ y ∈ Finset.Icc 1 N', ‖ψ (ε * ((m : ℝ) - (y : ℝ)))‖ := norm_sum_le _ _
      calc ‖Work.KMTAreas.A4.lipWeight ψ ε N' m‖
          = ε * ((N' : ℝ)⁻¹ * ‖∑ y ∈ Finset.Icc 1 N', ψ (ε * ((m : ℝ) - (y : ℝ)))‖) := by
            simp only [Work.KMTAreas.A4.lipWeight, norm_mul, hεnorm, hcnorm]
        _ ≤ ε * ((N' : ℝ)⁻¹ * ∑ y ∈ Finset.Icc 1 N', ‖ψ (ε * ((m : ℝ) - (y : ℝ)))‖) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hN'pos.le)) hε0.le
        _ = ε * (N' : ℝ)⁻¹ * ∑ y ∈ Finset.Icc 1 N', ‖ψ (ε * ((m : ℝ) - (y : ℝ)))‖ := by ring
    -- Step 2: Schwartz decay plus `X ≤ |m - y|`, summed over the window.
    have hB : (∑ y ∈ Finset.Icc 1 N', ‖ψ (ε * ((m : ℝ) - (y : ℝ)))‖) * X
        ≤ C * ∑ y ∈ Finset.Icc 1 N',
            Work.Analysis.InverseTheory.jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))) * |(m : ℝ) - (y : ℝ)| := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_le_sum (fun y hy => ?_)
      have h1 : ‖ψ (ε * ((m : ℝ) - (y : ℝ)))‖
          ≤ C * Work.Analysis.InverseTheory.jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))) := hdecay _
      have h2 : X ≤ |(m : ℝ) - (y : ℝ)| := by
        rw [hXdef]
        exact window_le_dist hy
      have h3 : ‖ψ (ε * ((m : ℝ) - (y : ℝ)))‖ * X
          ≤ (C * Work.Analysis.InverseTheory.jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))))
              * |(m : ℝ) - (y : ℝ)| :=
        mul_le_mul h1 h2 hXnonneg
          (mul_nonneg hCpos.le (Work.Analysis.InverseTheory.jbDecay_nonneg 12 _))
      calc ‖ψ (ε * ((m : ℝ) - (y : ℝ)))‖ * X
          ≤ (C * Work.Analysis.InverseTheory.jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))))
              * |(m : ℝ) - (y : ℝ)| := h3
        _ = C * (Work.Analysis.InverseTheory.jbDecay 12 (ε * ((m : ℝ) - (y : ℝ)))
              * |(m : ℝ) - (y : ℝ)|) := by ring
    -- Factoring the common `ε` out of the sum on the right-hand side.
    have hS1 : (∑ y ∈ Finset.Icc 1 N',
          ε * Work.Analysis.InverseTheory.jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))) * |(m : ℝ) - (y : ℝ)|)
        = ε * ∑ y ∈ Finset.Icc 1 N',
            Work.Analysis.InverseTheory.jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))) * |(m : ℝ) - (y : ℝ)| := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y hy => by ring)
    calc ‖Work.KMTAreas.A4.lipWeight ψ ε N' m‖ * X
        ≤ (ε * (N' : ℝ)⁻¹ * ∑ y ∈ Finset.Icc 1 N', ‖ψ (ε * ((m : ℝ) - (y : ℝ)))‖) * X :=
          mul_le_mul_of_nonneg_right hnorm hXnonneg
      _ = ε * (N' : ℝ)⁻¹ * ((∑ y ∈ Finset.Icc 1 N', ‖ψ (ε * ((m : ℝ) - (y : ℝ)))‖) * X) := by ring
      _ ≤ ε * (N' : ℝ)⁻¹ * (C * ∑ y ∈ Finset.Icc 1 N',
            Work.Analysis.InverseTheory.jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))) * |(m : ℝ) - (y : ℝ)|) :=
          mul_le_mul_of_nonneg_left hB hεc
      _ = C * (N' : ℝ)⁻¹ * ∑ y ∈ Finset.Icc 1 N',
              ε * Work.Analysis.InverseTheory.jbDecay 12 (ε * ((m : ℝ) - (y : ℝ))) * |(m : ℝ) - (y : ℝ)| := by
          rw [hS1]; ring

end Work.KMTAreas.A4
