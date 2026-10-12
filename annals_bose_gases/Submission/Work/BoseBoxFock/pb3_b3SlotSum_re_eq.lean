import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseBoxFock.PB3Aux3
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

noncomputable section

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-!
# `Work.BoseBoxFock.pb3_b3SlotSum_re_eq`

The block-III slot form `b3SlotSum` at the *constant-weight* kernel `K1exp v μ N 1` is, per pair,
the `Lab N`-sum of the `(pinQ, pinQ)`-rank-one slot forms.  This is a pure linearity statement: the
only inputs are the kernel expansion `K1exp_one_eq` and the exchange of a finite sum with the two
Bochner integrals (justified by boundedness and compact support of `pinQ`).
-/

/-- A measurable bounded function on `E3` supported in a set of finite measure is integrable. -/
theorem pb3b3_integrable_of_bounded_supportE {s : Set E3} (hs : volume s < ⊤) {f : E3 → ℂ}
    (hm : Measurable f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) (hsup : Function.support f ⊆ s) :
    Integrable f volume := by
  obtain ⟨C, hC⟩ := hb
  refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset (μ := volume) (s := s)
    (f := f) hsup).mp ?_
  exact MeasureTheory.IntegrableOn.of_bound (s := s) (μ := volume) hs
    hm.aestronglyMeasurable.restrict (max C 0)
    (Filter.Eventually.of_forall fun x => le_trans (hC x) (le_max_left _ _))

/-- The fibre integrand `u ↦ conj (pinQ_k u) · Ψ (x[j ↦ u])` is integrable: `pinQ_k` is
measurable and supported in the (finite-measure) box, `Ψ` is bounded. -/
theorem pb3b3_fibre_integrable {n N : ℕ} {v : E3 → ℝ} {μ : ℝ} (j : Fin n) (k : Lab N)
    {Ψ : Xn n → ℂ} (hΨm : Measurable Ψ) (hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C) (x : Xn n) :
    Integrable (fun u : E3 => (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (Function.update x j u)) := by
  obtain ⟨Ck, hCk0, hCk⟩ := pinQ_bdd v μ N k
  obtain ⟨CΨ, hCΨ⟩ := hΨb
  have hkm : Measurable (pinQ v μ N k) := pinQ_measurable v μ N k
  have hks : Function.support (pinQ v μ N k) ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) :=
    pb3_pinQ_support k
  refine pb3b3_integrable_of_bounded_supportE
    (volume_boxL_lt_top (ellH v μ) (ellH_pos v μ)) ?_ ?_ ?_
  · exact (Complex.continuous_conj.measurable.comp hkm).mul (hΨm.comp (by fun_prop))
  · exact ⟨Ck * max CΨ 0, fun u => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hCk u) (le_trans (hCΨ _) (le_max_left _ _)) (norm_nonneg _) hCk0⟩
  · intro u hu
    exact hks (Function.mem_support.mpr fun h0 => hu (by simp [h0]))

/-- **The fibre swap**: the `u`-integral of the rank-one kernel `Σ_k pinQ_k(x_j)·conj(pinQ_k u)`
against a state fibre is the `k`-sum of the individual `u`-integrals. -/
theorem pb3b3_uSlot_swap {n N : ℕ} {v : E3 → ℝ} {μ : ℝ} (j : Fin n)
    {Ψ : Xn n → ℂ} (hΨm : Measurable Ψ) (hΨb : ∃ C : ℝ, ∀ x, ‖Ψ x‖ ≤ C) (x : Xn n) :
    (∫ u : E3, (∑ k : Lab N, pinQ v μ N k (x j) * (starRingEnd ℂ) (pinQ v μ N k u))
        * Ψ (Function.update x j u))
      = ∑ k : Lab N, pinQ v μ N k (x j)
          * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u) * Ψ (Function.update x j u) := by
  rw [show (∫ u : E3, (∑ k : Lab N, pinQ v μ N k (x j) * (starRingEnd ℂ) (pinQ v μ N k u))
        * Ψ (Function.update x j u))
      = ∫ u : E3, ∑ k : Lab N, pinQ v μ N k (x j)
          * ((starRingEnd ℂ) (pinQ v μ N k u) * Ψ (Function.update x j u)) from
    integral_congr_ae (Filter.Eventually.of_forall fun u => by
      simp only [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring))]
  rw [MeasureTheory.integral_finset_sum Finset.univ (fun k _ =>
      (pb3b3_fibre_integrable j k hΨm hΨb x).const_mul _)]
  exact Finset.sum_congr rfl (fun k _ => MeasureTheory.integral_const_mul _ _)

/-- **The pair swap**: the `x`-integral of the state against the fibre swap is the `k`-sum of the
`x`-integrals.  Integrability in `x` is `integrable_pairTerm`. -/
theorem pb3b3_pair_swap {n N : ℕ} {v : E3 → ℝ} {μ : ℝ} (i j : Fin n)
    {Θ : Xn n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n (ellH v μ)) :
    (∫ x : Xn n, (starRingEnd ℂ) (Θ x)
        * (∫ u : E3, (∑ k : Lab N, pinQ v μ N k (x j) * (starRingEnd ℂ) (pinQ v μ N k u))
            * aPC (ellH v μ) i Θ (Function.update x j u)))
      = ∑ k : Lab N, ∫ x : Xn n, (starRingEnd ℂ) (Θ x)
          * (pinQ v μ N k (x j) * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
              * aPC (ellH v μ) i Θ (Function.update x j u)) := by
  classical
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  obtain ⟨CΘ, hCΘ⟩ := hΘb
  have hΘb' : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C := ⟨CΘ, hCΘ⟩
  have hCΘ0 : 0 ≤ CΘ := le_trans (norm_nonneg _) (hCΘ (Classical.arbitrary (Xn n)))
  have hΨm : Measurable (aPC (ellH v μ) i Θ) := aPC_measurable' i hΘm
  have hΨb : ∃ C : ℝ, ∀ x, ‖aPC (ellH v μ) i Θ x‖ ≤ C :=
    ⟨CΘ, fun x => aPC_bound_pointwise hℓ i hCΘ hCΘ0 x⟩
  rw [show (∫ x : Xn n, (starRingEnd ℂ) (Θ x)
        * (∫ u : E3, (∑ k : Lab N, pinQ v μ N k (x j) * (starRingEnd ℂ) (pinQ v μ N k u))
            * aPC (ellH v μ) i Θ (Function.update x j u)))
      = ∫ x : Xn n, ∑ k : Lab N, (starRingEnd ℂ) (Θ x)
          * (pinQ v μ N k (x j) * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
              * aPC (ellH v μ) i Θ (Function.update x j u)) from
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [pb3b3_uSlot_swap (v := v) (μ := μ) (N := N)
        (Ψ := aPC (ellH v μ) i Θ) j hΨm hΨb x, Finset.mul_sum])]
  rw [MeasureTheory.integral_finset_sum Finset.univ (fun k _ =>
    integrable_pairTerm j k hΘm hΘb' hΘs hΨm hΨb)]

theorem pb3_b3SlotSum_re_eq {n N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))} :
    (Work.BoseBoxFock.b3SlotSum (Work.BoseBoxFock.ellH v μ)
        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
          (Φ : Submission.BoseGases.X n → ℝ))
        (Work.BoseBoxFock.K1exp v μ N (fun _ : Work.BoseBoxFock.Lab N => (1 : ℝ)))).re
      = ∑ p ∈ Submission.BoseGases.pairSet n, ∑ k : Work.BoseBoxFock.Lab N,
          (∫ x : Submission.BoseGases.X n,
            (starRingEnd ℂ) (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ) x)
            * (Work.BoseBoxFock.pinQ v μ N k (x p.2)
                * ∫ u : EuclideanSpace ℝ (Fin 3),
                    (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
                    * Work.BoseBoxFock.aPC (Work.BoseBoxFock.ellH v μ) p.1
                        (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ)
                          (Φ : Submission.BoseGases.X n → ℝ))
                        (Function.update x p.2 u))).re := by
  classical
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  have hΘm : Measurable (boxRestrictC (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ)) :=
    boxRestrictC_measurable' (ellH v μ) hΦc
  obtain ⟨CΘ, hCΘ0, hCΘ⟩ := boxRestrictC_bound' hℓ hΦc
  have hΘb : ∃ C : ℝ, ∀ x, ‖boxRestrictC (ellH v μ)
      (Φ : Submission.BoseGases.X n → ℝ) x‖ ≤ C := ⟨CΘ, hCΘ⟩
  have hΘs : Function.support (boxRestrictC (ellH v μ)
      (Φ : Submission.BoseGases.X n → ℝ)) ⊆ Submission.BoseGases.abox n (ellH v μ) :=
    boxRestrictC_support' (ellH v μ) _
  -- the complex identity
  have hmain : b3SlotSum (ellH v μ)
      (boxRestrictC (ellH v μ) (Φ : Submission.BoseGases.X n → ℝ))
      (K1exp v μ N (fun _ : Lab N => (1 : ℝ)))
      = ∑ p ∈ Submission.BoseGases.pairSet n, ∑ k : Lab N,
          ∫ x : Xn n, (starRingEnd ℂ) (boxRestrictC (ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ) x)
            * (pinQ v μ N k (x p.2)
                * ∫ u : E3, (starRingEnd ℂ) (pinQ v μ N k u)
                    * aPC (ellH v μ) p.1 (boxRestrictC (ellH v μ)
                        (Φ : Submission.BoseGases.X n → ℝ))
                        (Function.update x p.2 u)) := by
    rw [b3SlotSum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    simp only [slotOne]
    have hInner : ∀ x : Xn n,
        (∫ u : E3, K1exp v μ N (fun _ : Lab N => (1 : ℝ)) (x p.2) u
            * aPC (ellH v μ) p.1 (boxRestrictC (ellH v μ)
                (Φ : Submission.BoseGases.X n → ℝ)) (Function.update x p.2 u))
        = ∫ u : E3, (∑ k : Lab N, pinQ v μ N k (x p.2)
              * (starRingEnd ℂ) (pinQ v μ N k u))
            * aPC (ellH v μ) p.1 (boxRestrictC (ellH v μ)
                (Φ : Submission.BoseGases.X n → ℝ)) (Function.update x p.2 u) := by
      intro x
      refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
      simp only [K1exp_one_eq]
    rw [show (∫ x : Xn n, (starRingEnd ℂ) (boxRestrictC (ellH v μ)
            (Φ : Submission.BoseGases.X n → ℝ) x)
          * (∫ u : E3, K1exp v μ N (fun _ : Lab N => (1 : ℝ)) (x p.2) u
              * aPC (ellH v μ) p.1 (boxRestrictC (ellH v μ)
                  (Φ : Submission.BoseGases.X n → ℝ)) (Function.update x p.2 u)))
        = ∫ x : Xn n, (starRingEnd ℂ) (boxRestrictC (ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ) x)
          * (∫ u : E3, (∑ k : Lab N, pinQ v μ N k (x p.2)
                * (starRingEnd ℂ) (pinQ v μ N k u))
              * aPC (ellH v μ) p.1 (boxRestrictC (ellH v μ)
                  (Φ : Submission.BoseGases.X n → ℝ)) (Function.update x p.2 u)) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hInner x])]
    exact pb3b3_pair_swap (v := v) (μ := μ) (N := N) p.1 p.2 hΘm hΘb hΘs
  rw [hmain]
  simp only [Complex.re_sum]

end

end Work.BoseBoxFock
