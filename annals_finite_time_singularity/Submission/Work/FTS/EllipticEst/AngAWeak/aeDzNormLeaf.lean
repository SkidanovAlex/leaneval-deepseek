import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.EllipticEst.AngAWeak.aeSigmaEnergyOwn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AngAWeak

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The radial first-order half of Step 1 of `prop:H2` in the almost-everywhere class, in the
form used as a leaf**: given that the `u`-mass is bounded by `M` times the source mass, the
`α`-weighted `ρ`-norm of `z ∂_z u` is bounded by a constant depending only on `M` times the
source mass.

The analytic input is `AngAWeak.aeSigmaEnergyOwn`,
`α² |z∂_zu|²_ρ ≤ C (|G|²_ρ + |u|²_ρ)`; the remaining content is the arithmetic of the square
roots, using `(|f|_ρ)² = |f|²_ρ`. -/
theorem aeDzNormLeaf (M : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G → Work.FTS.EllipticEst.H2W.Ae.nrm α u ≤ M * Work.FTS.EllipticEst.H2W.Ae.nrm α G → α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u) ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by
  obtain ⟨Cs, hCspos, hCs⟩ := aeSigmaEnergyOwn
  have hCs0 : 0 ≤ Cs := le_of_lt hCspos
  refine ⟨Real.sqrt (Cs * (1 + M ^ 2)), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α u G hA hMu
  -- the `u`-mass bound in squared form
  have hmu : Work.Spaces.HkSq α 0 u ≤ M ^ 2 * Work.Spaces.HkSq α 0 G := by
    by_cases hM : 0 ≤ M
    · have h2 : (Work.FTS.EllipticEst.H2W.Ae.nrm α u) ^ 2
          ≤ (M * Work.FTS.EllipticEst.H2W.Ae.nrm α G) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hMu 2
      simp only [Work.FTS.EllipticEst.H2W.Ae.nrm] at h2
      rw [mul_pow, Work.FTS.EllipticEst.Honest.hksq_sqrt_sq,
        Work.FTS.EllipticEst.Honest.hksq_sqrt_sq] at h2
      exact h2
    · have hMlt : M < 0 := not_le.mp hM
      have h3 : Work.FTS.EllipticEst.H2W.Ae.nrm α u = 0 := by
        have h4 : M * Work.FTS.EllipticEst.H2W.Ae.nrm α G ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_lt hMlt) (Real.sqrt_nonneg _)
        have h5 : 0 ≤ Work.FTS.EllipticEst.H2W.Ae.nrm α u := Real.sqrt_nonneg _
        linarith
      have h3' : Work.Spaces.HkSq α 0 u = 0 := by
        have h3'' : Real.sqrt (Work.Spaces.HkSq α 0 u) = 0 := h3
        exact (Real.sqrt_eq_zero (Work.Spaces.HkSq_nonneg α 0 u)).mp h3''
      rw [h3']
      exact mul_nonneg (sq_nonneg M) (Work.Spaces.HkSq_nonneg α 0 G)
  -- the squared estimate
  have hkey : α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
      ≤ Cs * (1 + M ^ 2) * Work.Spaces.HkSq α 0 G := by
    have h1 := hCs α u G hA
    have h2 : Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u
        ≤ (1 + M ^ 2) * Work.Spaces.HkSq α 0 G := by linarith [hmu]
    calc α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ Cs * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := h1
      _ ≤ Cs * ((1 + M ^ 2) * Work.Spaces.HkSq α 0 G) :=
          mul_le_mul_of_nonneg_left h2 hCs0
      _ = Cs * (1 + M ^ 2) * Work.Spaces.HkSq α 0 G := by ring
  -- square roots
  have hsq : (α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)) ^ 2
      ≤ (Real.sqrt (Cs * (1 + M ^ 2)) * Work.FTS.EllipticEst.H2W.Ae.nrm α G) ^ 2 := by
    rw [mul_pow, mul_pow]
    simp only [Work.FTS.EllipticEst.H2W.Ae.nrm]
    rw [Work.FTS.EllipticEst.Honest.hksq_sqrt_sq, Work.FTS.EllipticEst.Honest.hksq_sqrt_sq,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Cs * (1 + M ^ 2))]
    exact hkey
  have h2 : |α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)|
      ≤ |Real.sqrt (Cs * (1 + M ^ 2)) * Work.FTS.EllipticEst.H2W.Ae.nrm α G| :=
    (sq_le_sq).mp hsq
  simp only [Work.FTS.EllipticEst.H2W.Ae.nrm] at h2
  rw [abs_of_nonneg (mul_nonneg (le_of_lt hA.hα) (Real.sqrt_nonneg _)),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at h2
  exact h2

end Work.FTS.EllipticEst.AngAWeak
