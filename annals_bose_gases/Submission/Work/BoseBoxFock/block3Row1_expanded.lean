import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.kernelExpandedAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem block3Row1_expanded {n N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (c : ℂ)
    (E : Work.BoseB7.Q3Env (Work.BoseBoxFock.Lab N))
    (Theta : Work.BoseDict.Xn n → ℂ) (hΘm : Measurable Theta)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Theta x‖ ≤ C)
    (hΘs : Function.support Theta ⊆ Work.MB.boxPow n (Work.BoseBoxFock.ellH v μ)) :
    (∑ k : Work.BoseBoxFock.Lab N,
        (E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
          (∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
              ∫ u : EuclideanSpace ℝ (Fin 3),
              (starRingEnd ℂ) (Theta x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
                * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c y)
                * Work.BoseBoxFock.pinQ v μ N k (x p.2)
                * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
                * Theta (Function.update (Function.update x p.1 y) p.2 u)))
      = (E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0) •
          (∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x : Work.BoseDict.Xn n, ∫ y : EuclideanSpace ℝ (Fin 3),
              ∫ u : EuclideanSpace ℝ (Fin 3),
              (starRingEnd ℂ) (Theta x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
                * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c y)
                * Work.BoseBoxFock.K1exp v μ N
                    (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ)) (x p.2) u
                * Theta (Function.update (Function.update x p.1 y) p.2 u)) := by
  classical
  -- The coefficient `E.ell⁻³(W₁(0) + W₁ω(0))` does not depend on the mode, so it factors out of
  -- the mode sum; the remaining kernel sum is the four-term expansion at the weight `1`.
  have hΘb' : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Theta x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hΘb
    exact ⟨max C 0, le_max_right _ _, fun x => le_trans (hC x) (le_max_left _ _)⟩
  -- each summand of the mode sum is integrable on the threefold product space
  have hInt : ∀ (k : Work.BoseBoxFock.Lab N) (p : Fin n × Fin n),
      p ∈ Submission.BoseGases.pairSet n →
      MeasureTheory.Integrable (fun z : (Work.BoseDict.Xn n × EuclideanSpace ℝ (Fin 3)) ×
          EuclideanSpace ℝ (Fin 3) =>
        (starRingEnd ℂ) (Theta z.1.1) * Work.BoseBoxFock.pinCond v μ c (z.1.1 p.1)
          * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c z.1.2)
          * Work.BoseBoxFock.pinQ v μ N k (z.1.1 p.2)
          * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k z.2)
          * Theta (Function.update (Function.update z.1.1 p.1 z.1.2) p.2 z.2))
        (Work.BoseBoxFock.v3 n) := by
    intro k p hp
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    obtain ⟨CΘ, hCΘ0, hCΘ⟩ := hΘb'
    obtain ⟨Cα, hCα0, hCα⟩ := Work.BoseBoxFock.pinCond_bdd v μ c
    obtain ⟨Cγ, hCγ0, hCγ⟩ := Work.BoseBoxFock.pinQ_bdd v μ N k
    have hbase := Work.BoseBoxFock.integrable_state_triple (Θ := Theta)
      (α := fun x : Work.BoseDict.Xn n =>
        Work.BoseBoxFock.pinCond v μ c (x p.1) * Work.BoseBoxFock.pinQ v μ N k (x p.2))
      (β := fun y : EuclideanSpace ℝ (Fin 3) =>
        (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c y))
      (γ := fun u : EuclideanSpace ℝ (Fin 3) =>
        (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u))
      (i := p.1) (j := p.2) hij (Cα := Cα * Cγ) (Cβ := Cα) (Cγ := Cγ) (CΘ := CΘ)
      (mul_nonneg hCα0 hCγ0) hCα0 hCγ0 hCΘ0
      (((Work.BoseBoxFock.pinCond_measurable v μ c).comp (measurable_pi_apply p.1)).mul
        ((Work.BoseBoxFock.pinQ_measurable v μ N k).comp (measurable_pi_apply p.2)))
      (fun x => by
        rw [norm_mul]
        exact mul_le_mul (hCα (x p.1)) (hCγ (x p.2)) (norm_nonneg _) hCα0)
      (Complex.continuous_conj.measurable.comp (Work.BoseBoxFock.pinCond_measurable v μ c))
      (fun y => by rw [Complex.norm_conj]; exact hCα y)
      (Complex.continuous_conj.measurable.comp (Work.BoseBoxFock.pinQ_measurable v μ N k))
      (fun u => by rw [Complex.norm_conj]; exact hCγ u)
      hΘm hCΘ hΘs
    exact hbase.congr (Filter.Eventually.of_forall fun z => by ring)
  rw [Work.BoseBoxFock.sum_smul_pullout_triple (Submission.BoseGases.pairSet n)
    (E.ell ^ (-(3 : ℝ)) * E.W1 0 + E.ell ^ (-(3 : ℝ)) * E.W1omega0)
    (fun k p x y u =>
      (starRingEnd ℂ) (Theta x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
        * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c y)
        * Work.BoseBoxFock.pinQ v μ N k (x p.2)
        * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
        * Theta (Function.update (Function.update x p.1 y) p.2 u)) hInt]
  congr 1
  refine Finset.sum_congr rfl (fun p hp => ?_)
  refine Work.BoseBoxFock.integral_triple_congr_of_forall (fun x y u => ?_)
  -- the pointwise kernel expansion at the weight `1`
  have hker : (∑ k : Work.BoseBoxFock.Lab N,
        Work.BoseBoxFock.pinQ v μ N k (x p.2)
          * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u))
      = Work.BoseBoxFock.K1exp v μ N (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ)) (x p.2) u :=
    Work.BoseBoxFock.pinQ_kernel_one N v μ (x p.2) u
  calc (∑ k : Work.BoseBoxFock.Lab N, (starRingEnd ℂ) (Theta x)
          * Work.BoseBoxFock.pinCond v μ c (x p.1)
          * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c y)
          * Work.BoseBoxFock.pinQ v μ N k (x p.2)
          * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
          * Theta (Function.update (Function.update x p.1 y) p.2 u))
      = ∑ k : Work.BoseBoxFock.Lab N, (1 : ℂ) * (((starRingEnd ℂ) (Theta x)
          * Work.BoseBoxFock.pinCond v μ c (x p.1)
          * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c y))
          * (Work.BoseBoxFock.pinQ v μ N k (x p.2)
            * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u))
          * Theta (Function.update (Function.update x p.1 y) p.2 u)) :=
        Finset.sum_congr rfl (fun k _ => by ring)
    _ = (((starRingEnd ℂ) (Theta x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
            * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c y))
          * ∑ k : Work.BoseBoxFock.Lab N, (1 : ℂ) * (Work.BoseBoxFock.pinQ v μ N k (x p.2)
              * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)))
          * Theta (Function.update (Function.update x p.1 y) p.2 u) :=
        Work.BoseBoxFock.sum_mul_factor (fun _ : Work.BoseBoxFock.Lab N => (1 : ℂ))
          ((starRingEnd ℂ) (Theta x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
            * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c y))
          (Theta (Function.update (Function.update x p.1 y) p.2 u))
          (fun k : Work.BoseBoxFock.Lab N => Work.BoseBoxFock.pinQ v μ N k (x p.2)
            * (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u))
    _ = (((starRingEnd ℂ) (Theta x) * Work.BoseBoxFock.pinCond v μ c (x p.1)
            * (starRingEnd ℂ) (Work.BoseBoxFock.pinCond v μ c y))
          * Work.BoseBoxFock.K1exp v μ N (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ))
              (x p.2) u)
          * Theta (Function.update (Function.update x p.1 y) p.2 u) := by
        rw [Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => by rw [one_mul]), hker]
    _ = _ := by ring

end Work.BoseBoxFock
