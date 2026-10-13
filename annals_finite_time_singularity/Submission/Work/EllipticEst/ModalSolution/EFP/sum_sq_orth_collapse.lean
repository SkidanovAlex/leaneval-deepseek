import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.EFP

theorem sum_sq_orth_collapse (s : Finset ℕ) (c : ℕ → ℝ) (e : ℕ → ℝ → ℝ)
    (hcont : ∀ m, Continuous (e m))
    (horth : ∀ m ∈ s, ∀ n ∈ s, m ≠ n →
      (∫ θ in Work.Spaces.Iθ, e m θ * e n θ * Real.cos θ) = 0) :
    (∫ θ in Work.Spaces.Iθ, (∑ m ∈ s, c m * e m θ) ^ 2 * Real.cos θ)
      = ∑ m ∈ s, c m ^ 2 * (∫ θ in Work.Spaces.Iθ, e m θ ^ 2 * Real.cos θ) := by
  classical
  -- integrability of every summand on the compact interval `Iθ`
  have hint : ∀ m ∈ s, ∀ n ∈ s, MeasureTheory.Integrable
      (fun θ : ℝ => c m * c n * (e m θ * e n θ * Real.cos θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro m hm n hn
    have h1 : Continuous (fun θ : ℝ => e m θ * e n θ * Real.cos θ) :=
      ((hcont m).mul (hcont n)).mul Real.continuous_cos
    have hc : Continuous (fun θ : ℝ => c m * c n * (e m θ * e n θ * Real.cos θ)) :=
      continuous_const.mul h1
    exact ContinuousOn.integrableOn_compact isCompact_Icc hc.continuousOn
  -- pointwise expansion of the square into a double sum
  have hpt : ∀ θ : ℝ, (∑ m ∈ s, c m * e m θ) ^ 2 * Real.cos θ
      = ∑ m ∈ s, ∑ n ∈ s, c m * c n * (e m θ * e n θ * Real.cos θ) := by
    intro θ
    have hsq : (∑ m ∈ s, c m * e m θ) ^ 2 * Real.cos θ
        = (∑ m ∈ s, c m * e m θ) * (∑ n ∈ s, c n * e n θ * Real.cos θ) := by
      have hsm : (∑ n ∈ s, c n * e n θ) * Real.cos θ
          = ∑ n ∈ s, c n * e n θ * Real.cos θ :=
        Finset.sum_mul s (fun n => c n * e n θ) (Real.cos θ)
      calc (∑ m ∈ s, c m * e m θ) ^ 2 * Real.cos θ
          = ((∑ m ∈ s, c m * e m θ) * (∑ n ∈ s, c n * e n θ)) * Real.cos θ := by
            rw [sq]
        _ = (∑ m ∈ s, c m * e m θ) * ((∑ n ∈ s, c n * e n θ) * Real.cos θ) := by
            rw [mul_assoc]
        _ = (∑ m ∈ s, c m * e m θ) * (∑ n ∈ s, c n * e n θ * Real.cos θ) := by
            rw [hsm]
    calc (∑ m ∈ s, c m * e m θ) ^ 2 * Real.cos θ
        = (∑ m ∈ s, c m * e m θ) * (∑ n ∈ s, c n * e n θ * Real.cos θ) := hsq
      _ = ∑ m ∈ s, ∑ n ∈ s, c m * c n * (e m θ * e n θ * Real.cos θ) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun n _ => by ring))
  -- the inner sum over `n` collapses to the diagonal term `n = m`
  have hfix : ∀ m ∈ s, (∑ n ∈ s, ∫ θ in Work.Spaces.Iθ,
        c m * c n * (e m θ * e n θ * Real.cos θ))
      = c m ^ 2 * (∫ θ in Work.Spaces.Iθ, e m θ ^ 2 * Real.cos θ) := by
    intro m hm
    rw [Finset.sum_eq_single_of_mem m hm]
    · rw [MeasureTheory.integral_const_mul,
        show c m * c m = c m ^ 2 by ring]
      have hi : (∫ θ in Work.Spaces.Iθ, e m θ * e m θ * Real.cos θ)
          = (∫ θ in Work.Spaces.Iθ, e m θ ^ 2 * Real.cos θ) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro θ _
        ring
      rw [hi]
    · intro n hn hnm
      rw [MeasureTheory.integral_const_mul, horth m hm n hn (Ne.symm hnm), mul_zero]
  calc (∫ θ in Work.Spaces.Iθ, (∑ m ∈ s, c m * e m θ) ^ 2 * Real.cos θ)
      = (∫ θ in Work.Spaces.Iθ,
          ∑ m ∈ s, ∑ n ∈ s, c m * c n * (e m θ * e n θ * Real.cos θ)) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        intro θ _
        exact hpt θ
    _ = (∑ m ∈ s, ∫ θ in Work.Spaces.Iθ,
            ∑ n ∈ s, c m * c n * (e m θ * e n θ * Real.cos θ)) :=
        MeasureTheory.integral_finsetSum (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
          (s := s)
          (f := fun m θ => ∑ n ∈ s, c m * c n * (e m θ * e n θ * Real.cos θ))
          (fun m hm => MeasureTheory.integrable_finsetSum
            (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) s
            (f := fun n θ => c m * c n * (e m θ * e n θ * Real.cos θ))
            (fun n hn => hint m hm n hn))
    _ = (∑ m ∈ s, c m ^ 2 * (∫ θ in Work.Spaces.Iθ, e m θ ^ 2 * Real.cos θ)) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact (MeasureTheory.integral_finsetSum
            (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) s
            (f := fun n θ => c m * c n * (e m θ * e n θ * Real.cos θ))
            (fun n hn => hint m hm n hn)).trans (hfix m hm)

end Work.EllipticEst.ModalSolution.EFP
