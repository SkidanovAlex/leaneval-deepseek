import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.kernelFormAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.potPairRowsKernelBlock2Local` — the Bogoliubov block of the `Q₂` row in
# kernel form (self-contained proof)

This is the second block of `Work.BoseBoxFock.potPairRows_cIPn_pinned_gen` (the Bogoliubov row
`½W₁(a₀†a₀†a_k a_{−k} + h.c.)`), with the mode sum moved inside the three position integrals.

The proof is the two-instantiation run of the toolbox of `kernelFormAux`:
`sum_mul_iterated_triple_eq` for the finite-sum/triple-integral exchange, `integrable_state_triple`
plus the a.e. pull-backs `ae_v3_*` for the integrability of the two families of summands, and the
elementary `Finset.mul_sum`/`sum_mul`/`ring` rearrangement for the pointwise identity.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem potPairRowsKernelBlock2Local {n : ℕ} {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    (E : Work.BoseB7.Q3Env Mode) (Fp G : Mode → Ω → ℂ) (Th T : Ω → ℂ) (Theta : Xn n → ℂ)
    (ℓ : ℝ)
    (hGm : ∀ k, Measurable (G k)) (hGb : ∀ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖G k z‖ ≤ C)
    (hTm : Measurable T) (hTb : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖T z‖ ≤ C)
    (hFp : ∀ k, Fp k =ᵐ[volume] G k) (hTh : Th =ᵐ[volume] T)
    (hΘm : Measurable Theta) (hΘb : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖Theta z‖ ≤ C)
    (hΘs : Function.support Theta ⊆ Work.MB.boxPow n ℓ) :
    (∑ k : Mode, E.W1 k •
        ((∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
              (starRingEnd ℂ) (Theta x) * Th (x p.1) * (starRingEnd ℂ) (Fp k y) * Th (x p.2)
                * (starRingEnd ℂ) (Fp (-k) u)
                * Theta (Function.update (Function.update x p.1 y) p.2 u))
          + (∑ p ∈ Submission.BoseGases.pairSet n,
              ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
              (starRingEnd ℂ) (Theta x) * Fp k (x p.1) * (starRingEnd ℂ) (Th y)
                * Fp (-k) (x p.2) * (starRingEnd ℂ) (Th u)
                * Theta (Function.update (Function.update x p.1 y) p.2 u))))
      = (∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
            (starRingEnd ℂ) (Theta x) * Th (x p.1) * Th (x p.2)
              * (∑ k : Mode, E.W1 k * ((starRingEnd ℂ) (Fp k y) * (starRingEnd ℂ) (Fp (-k) u)))
              * Theta (Function.update (Function.update x p.1 y) p.2 u))
        + (∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
            (starRingEnd ℂ) (Theta x)
              * (∑ k : Mode, E.W1 k * (Fp k (x p.1) * Fp (-k) (x p.2)))
              * (starRingEnd ℂ) (Th y) * (starRingEnd ℂ) (Th u)
              * Theta (Function.update (Function.update x p.1 y) p.2 u)) := by
  classical
  -- ### integrability of the two families of summands
  have hInt1 : ∀ k p, p ∈ Submission.BoseGases.pairSet n →
      Integrable (fun z : (Xn n × Ω) × Ω =>
        (starRingEnd ℂ) (Theta z.1.1) * Th (z.1.1 p.1) * (starRingEnd ℂ) (Fp k z.1.2)
          * Th (z.1.1 p.2) * (starRingEnd ℂ) (Fp (-k) z.2)
          * Theta (Function.update (Function.update z.1.1 p.1 z.1.2) p.2 z.2)) (v3 n) := by
    intro k p hp
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    obtain ⟨CG, hCG0, hCG⟩ := hGb k
    obtain ⟨CG', hCG0', hCG'⟩ := hGb (-k)
    obtain ⟨CT, hCT0, hCT⟩ := hTb
    obtain ⟨CΘ, hCΘ0, hCΘ⟩ := hΘb
    have hη : Integrable (fun z : (Xn n × Ω) × Ω =>
        (starRingEnd ℂ) (Theta z.1.1) * (T (z.1.1 p.1) * T (z.1.1 p.2))
          * (starRingEnd ℂ) (G k z.1.2) * (starRingEnd ℂ) (G (-k) z.2)
          * Theta (Function.update (Function.update z.1.1 p.1 z.1.2) p.2 z.2)) (v3 n) := by
      refine integrable_state_triple (Θ := Theta) (α := fun x : Xn n => T (x p.1) * T (x p.2))
        (β := fun y : Ω => (starRingEnd ℂ) (G k y)) (γ := fun u : Ω => (starRingEnd ℂ) (G (-k) u))
        (i := p.1) (j := p.2) hij (Cα := CT * CT) (Cβ := CG) (Cγ := CG') (CΘ := CΘ)
        (mul_nonneg hCT0 hCT0) hCG0 hCG0' hCΘ0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCΘ hΘs
      · exact (hTm.comp (measurable_pi_apply p.1)).mul ((hTm.comp (measurable_pi_apply p.2)))
      · intro x
        rw [norm_mul]
        exact mul_le_mul (hCT _) (hCT _) (norm_nonneg _) hCT0
      · exact Complex.continuous_conj.measurable.comp (hGm k)
      · intro y
        rw [Complex.norm_conj]
        exact hCG y
      · exact Complex.continuous_conj.measurable.comp (hGm (-k))
      · intro u
        rw [Complex.norm_conj]
        exact hCG' u
      · exact hΘm
    have hη' : Integrable (fun z : (Xn n × Ω) × Ω =>
        (starRingEnd ℂ) (Theta z.1.1) * T (z.1.1 p.1) * (starRingEnd ℂ) (G k z.1.2)
          * T (z.1.1 p.2) * (starRingEnd ℂ) (G (-k) z.2)
          * Theta (Function.update (Function.update z.1.1 p.1 z.1.2) p.2 z.2)) (v3 n) :=
      hη.congr (Filter.Eventually.of_forall fun z => by ring)
    have hs1 : ∀ᵐ z ∂v3 n,
        (starRingEnd ℂ) (G k z.1.2) = (starRingEnd ℂ) (Fp k z.1.2) :=
      (ae_v3_fst_snd (hFp k).symm).mono fun z hz => by rw [hz]
    have hs2 : ∀ᵐ z ∂v3 n,
        (starRingEnd ℂ) (G (-k) z.2) = (starRingEnd ℂ) (Fp (-k) z.2) :=
      (ae_v3_snd (hFp (-k)).symm).mono fun z hz => by rw [hz]
    refine hη'.congr ?_
    filter_upwards [ae_v3_fst_fst_eval p.1 hTh.symm, ae_v3_fst_fst_eval p.2 hTh.symm,
      hs1, hs2] with z h1 h2 h3 h4
    simp only [h1, h2, h3, h4]
  have hInt2 : ∀ k p, p ∈ Submission.BoseGases.pairSet n →
      Integrable (fun z : (Xn n × Ω) × Ω =>
        (starRingEnd ℂ) (Theta z.1.1) * Fp k (z.1.1 p.1) * (starRingEnd ℂ) (Th z.1.2)
          * Fp (-k) (z.1.1 p.2) * (starRingEnd ℂ) (Th z.2)
          * Theta (Function.update (Function.update z.1.1 p.1 z.1.2) p.2 z.2)) (v3 n) := by
    intro k p hp
    have hij : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    obtain ⟨CG, hCG0, hCG⟩ := hGb k
    obtain ⟨CG', hCG0', hCG'⟩ := hGb (-k)
    obtain ⟨CT, hCT0, hCT⟩ := hTb
    obtain ⟨CΘ, hCΘ0, hCΘ⟩ := hΘb
    have hη : Integrable (fun z : (Xn n × Ω) × Ω =>
        (starRingEnd ℂ) (Theta z.1.1) * (G k (z.1.1 p.1) * G (-k) (z.1.1 p.2))
          * (starRingEnd ℂ) (T z.1.2) * (starRingEnd ℂ) (T z.2)
          * Theta (Function.update (Function.update z.1.1 p.1 z.1.2) p.2 z.2)) (v3 n) := by
      refine integrable_state_triple (Θ := Theta)
        (α := fun x : Xn n => G k (x p.1) * G (-k) (x p.2))
        (β := fun y : Ω => (starRingEnd ℂ) (T y)) (γ := fun u : Ω => (starRingEnd ℂ) (T u))
        (i := p.1) (j := p.2) hij (Cα := CG * CG') (Cβ := CT) (Cγ := CT) (CΘ := CΘ)
        (mul_nonneg hCG0 hCG0') hCT0 hCT0 hCΘ0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ hCΘ hΘs
      · exact ((hGm k).comp (measurable_pi_apply p.1)).mul
          ((hGm (-k)).comp (measurable_pi_apply p.2))
      · intro x
        rw [norm_mul]
        exact mul_le_mul (hCG _) (hCG' _) (norm_nonneg _) hCG0
      · exact Complex.continuous_conj.measurable.comp hTm
      · intro y
        rw [Complex.norm_conj]
        exact hCT y
      · exact Complex.continuous_conj.measurable.comp hTm
      · intro u
        rw [Complex.norm_conj]
        exact hCT u
      · exact hΘm
    have hη' : Integrable (fun z : (Xn n × Ω) × Ω =>
        (starRingEnd ℂ) (Theta z.1.1) * G k (z.1.1 p.1) * (starRingEnd ℂ) (T z.1.2)
          * G (-k) (z.1.1 p.2) * (starRingEnd ℂ) (T z.2)
          * Theta (Function.update (Function.update z.1.1 p.1 z.1.2) p.2 z.2)) (v3 n) :=
      hη.congr (Filter.Eventually.of_forall fun z => by ring)
    have hs1 : ∀ᵐ z ∂v3 n, (starRingEnd ℂ) (T z.1.2) = (starRingEnd ℂ) (Th z.1.2) :=
      (ae_v3_fst_snd hTh.symm).mono fun z hz => by rw [hz]
    have hs2 : ∀ᵐ z ∂v3 n, (starRingEnd ℂ) (T z.2) = (starRingEnd ℂ) (Th z.2) :=
      (ae_v3_snd hTh.symm).mono fun z hz => by rw [hz]
    refine hη'.congr ?_
    filter_upwards [ae_v3_fst_fst_eval p.1 (hFp k).symm, ae_v3_fst_fst_eval p.2 (hFp (-k)).symm,
      hs1, hs2] with z h1 h2 h3 h4
    simp only [h1, h2, h3, h4]
  -- ### the two sub-blocks
  have hdist : (∑ k : Mode, E.W1 k •
        ((∑ p ∈ Submission.BoseGases.pairSet n,
            ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
              (starRingEnd ℂ) (Theta x) * Th (x p.1) * (starRingEnd ℂ) (Fp k y) * Th (x p.2)
                * (starRingEnd ℂ) (Fp (-k) u)
                * Theta (Function.update (Function.update x p.1 y) p.2 u))
          + (∑ p ∈ Submission.BoseGases.pairSet n,
              ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
              (starRingEnd ℂ) (Theta x) * Fp k (x p.1) * (starRingEnd ℂ) (Th y)
                * Fp (-k) (x p.2) * (starRingEnd ℂ) (Th u)
                * Theta (Function.update (Function.update x p.1 y) p.2 u))))
      = (∑ k : Mode, E.W1 k •
            (∑ p ∈ Submission.BoseGases.pairSet n,
              ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
                (starRingEnd ℂ) (Theta x) * Th (x p.1) * (starRingEnd ℂ) (Fp k y) * Th (x p.2)
                  * (starRingEnd ℂ) (Fp (-k) u)
                  * Theta (Function.update (Function.update x p.1 y) p.2 u)))
        + (∑ k : Mode, E.W1 k •
            (∑ p ∈ Submission.BoseGases.pairSet n,
              ∫ x : Xn n, ∫ y : Ω, ∫ u : Ω,
                (starRingEnd ℂ) (Theta x) * Fp k (x p.1) * (starRingEnd ℂ) (Th y)
                  * Fp (-k) (x p.2) * (starRingEnd ℂ) (Th u)
                  * Theta (Function.update (Function.update x p.1 y) p.2 u))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => smul_add _ _ _)
  rw [hdist]
  congr 1
  · simp only [Complex.real_smul]
    rw [sum_mul_iterated_triple_eq (s := Submission.BoseGases.pairSet n)
      (c := fun k : Mode => (((E.W1 k : ℝ)) : ℂ))
      (A := fun k p x y u =>
        (starRingEnd ℂ) (Theta x) * Th (x p.1) * (starRingEnd ℂ) (Fp k y) * Th (x p.2)
          * (starRingEnd ℂ) (Fp (-k) u) * Theta (Function.update (Function.update x p.1 y) p.2 u))
      hInt1]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    refine integral_triple_congr_of_forall (fun x y u => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  · simp only [Complex.real_smul]
    rw [sum_mul_iterated_triple_eq (s := Submission.BoseGases.pairSet n)
      (c := fun k : Mode => (((E.W1 k : ℝ)) : ℂ))
      (A := fun k p x y u =>
        (starRingEnd ℂ) (Theta x) * Fp k (x p.1) * (starRingEnd ℂ) (Th y) * Fp (-k) (x p.2)
          * (starRingEnd ℂ) (Th u) * Theta (Function.update (Function.update x p.1 y) p.2 u))
      hInt2]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    refine integral_triple_congr_of_forall (fun x y u => ?_)
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring

end Work.BoseBoxFock
