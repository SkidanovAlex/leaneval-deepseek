import Mathlib
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.EntJacobsAux
import Submission.Work.EKLComp.HcondFam_tendsto
import Submission.Work.EKLComp.ent_generating
import Submission.Work.EKLComp.JacRefiningGenSeq
import Submission.Work.EKLEntJacobs.kernel_mean
import Submission.Work.EKLEntJacobs.Hcond_kernel
import Submission.Work.EKLEntJacobs.fiber_inv
import Submission.Work.EKLEntJacobs.jensen
import Submission.Work.EKLEntJacobs.hPart_le_hPartCond
import Submission.Work.EKLEntJacobs.hPartCond_eq

/-!
# C3 (E7) — Jacobs' theorem

`ent μ T = ∫⁻ x, ent (condExpKernel μ (invariants T) x) T ∂μ`: the entropy of a measure
preserving system is the integral of the entropies of the conditional measures on the
`T`-invariant σ-algebra (Walters 8.4, the ergodic-decomposition formula for entropy).

## Structure of the proof

Write `κ x := condExpKernel μ (invariants T) x`.

1. *Per-partition identity.*  For every finite partition `Q`,
   `hPart μ T Q = ∫ x, hPart (κ x) T Q ∂μ`.
   The `≤` half is `EKLEntJacobs.hPart_le_hPartCond` (approximating `invariants T` by finitely
   generated `T`-invariant sub-σ-algebras; the Jensen gap is `o(N)`), combined with
   `EKLEntJacobs.hPartCond_eq`.  The `≥` half is Jensen's inequality
   (`EKLEntJacobs.jensen`, `EKLEntJacobs.Hcond_kernel`).
2. *Assembly.*  The Kolmogorov–Sinai generating-sequence theorem
   (`Work.EKLComp.ent_generating`, applied both to `μ` and — a.e., using
   `EKLEntJacobs.fiber_inv` — to the `T`-invariant measures `κ x`) plus monotone convergence
   give the two inequalities.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 800000

namespace Work.EKLComp

open Work.EKLContract

variable {X : Type} [mX : MeasurableSpace X] [StandardBorelSpace X]

/-- The conditional entropy with respect to `invariants T` is nonnegative. -/
theorem HcondFam_nonneg_inv (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    {ι : Type} [Fintype ι] {A : ι → Set X} :
    0 ≤ HcondFam μ A (MeasurableSpace.invariants T) := by
  rw [HcondFam]
  refine integral_nonneg_of_ae ?_
  have h : ∀ᵐ x ∂μ, ∀ i, 0 ≤ Real.negMulLog
      (condExp (MeasurableSpace.invariants T) μ ((A i).indicator (fun _ => (1 : ℝ))) x) := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [condExp_indicator_mem_Icc μ (MeasurableSpace.invariants T)
      (MeasurableSpace.invariants_le T) (A i)] with x hx
    exact Real.negMulLog_nonneg hx.1 hx.2
  filter_upwards [h] with x hx
  exact Finset.sum_nonneg fun i _ => hx i

/-- `hPart` is monotone under refinement of the partition. -/
theorem jac_Hfam_joinSets_le_of_refines (ν : Measure X) [IsProbabilityMeasure ν] (T : X → X)
    (hT : Measurable T) {Q Q' : FinPart X} (h : Refines Q' Q) (N : ℕ) :
    Hfam ν (joinSets T Q N) ≤ Hfam ν (joinSets T Q' N) := by
  classical
  choose f hf using fun i => h i
  refine Core.Hfam_mono ν (Core.joinSets_isMPart hT Q N) (Core.joinSets_isMPart hT Q' N)
    (fun (w : Fin N → Fin Q'.n) (k : Fin N) => f (w k)) ?_
  intro w x hx
  simp only [joinSets, Set.mem_iInter, Set.mem_preimage] at hx ⊢
  intro k
  exact hf (w k) (hx k)

theorem hPart_mono_refines (ν : Measure X) [IsProbabilityMeasure ν] (T : X → X)
    (hT : Measurable T) {Q Q' : FinPart X} (h : Refines Q' Q) :
    hPart ν T Q ≤ hPart ν T Q' := by
  rw [hPart, hPart]
  refine le_ciInf fun N => ?_
  refine le_trans (ciInf_le ?_ N)
    (div_le_div_of_nonneg_right (jac_Hfam_joinSets_le_of_refines ν T hT h (N + 1)) (by positivity))
  exact ⟨0, by rintro y ⟨M, rfl⟩; exact div_nonneg (Core.Hfam_nonneg ν _) (by positivity)⟩

theorem refines_iterate (P : ℕ → FinPart X)
    (hmono : ∀ m, Refines (P (m + 1)) (P m)) :
    ∀ {m n : ℕ}, m ≤ n → Refines (P n) (P m) := by
  intro m n hmn
  induction n, hmn using Nat.le_induction with
  | base => exact fun i => ⟨i, subset_rfl⟩
  | succ n hmn ih =>
      intro i
      obtain ⟨j, hj⟩ := hmono n i
      obtain ⟨k, hk⟩ := ih j
      exact ⟨k, hj.trans hk⟩

/-- `hPart` at a probability measure is bounded by the Shannon bound of the partition. -/
theorem hPart_le_log_card (ν : Measure X) [IsProbabilityMeasure ν] (T : X → X)
    (hT : Measurable T) (Q : FinPart X) : hPart ν T Q ≤ Real.log Q.n := by
  refine le_trans (Core.hPart_le_avg ν T Q 0) ?_
  simp only [Nat.cast_zero, zero_add, div_one]
  refine le_trans (Core.Hfam_le_log_card ν (Core.joinSets_isMPart hT Q 1)) ?_
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, pow_one]

/-- Jensen's inequality, transported to the conditional entropy w.r.t. `invariants T`. -/
theorem HcondFam_inv_le_Hfam (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    {ι : Type} [Fintype ι] {A : ι → Set X} (hA : ∀ i, MeasurableSet (A i)) :
    HcondFam μ A (MeasurableSpace.invariants T) ≤ Hfam μ A := by
  have hk : HcondFam μ A (MeasurableSpace.invariants T)
      = ∫ x, ∑ i, Real.negMulLog
          (((condExpKernel μ (MeasurableSpace.invariants T) x) (A i)).toReal) ∂μ :=
    EKLEntJacobs.Hcond_kernel μ T hA
  rw [hk]
  exact EKLEntJacobs.jensen μ T hA

/-- The conditional Fekete infimum is at most the unconditional one (Jensen direction). -/
theorem hPartCond_le_hPart (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (Q : FinPart X) :
    hPartCond μ T Q (MeasurableSpace.invariants T) ≤ hPart μ T Q := by
  have hterm : ∀ N : ℕ,
      HcondFam μ (joinSets T Q (N + 1)) (MeasurableSpace.invariants T) / ((N : ℝ) + 1)
        ≤ Hfam μ (joinSets T Q (N + 1)) / ((N : ℝ) + 1) := by
    intro N
    have hA : ∀ i : Fin (N + 1) → Fin Q.n, MeasurableSet (joinSets T Q (N + 1) i) :=
      fun i => Core.joinSets_measurable hT Q (N + 1) i
    exact div_le_div_of_nonneg_right (HcondFam_inv_le_Hfam μ T hA) (by positivity)
  rw [hPartCond, hPart]
  refine ciInf_mono ?_ hterm
  refine ⟨0, ?_⟩
  rintro y ⟨N, rfl⟩
  exact div_nonneg (HcondFam_nonneg_inv μ T) (by positivity)

/-- **The per-partition identity** (Jacobs for a fixed finite partition). -/
theorem hPart_eq_integral_hPart_fiber (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasurePreserving T μ μ) (Q : FinPart X) :
    hPart μ T Q
      = ∫ x, hPart (condExpKernel μ (MeasurableSpace.invariants T) x) T Q ∂μ := by
  refine le_antisymm ?_ ?_
  · refine le_trans (EKLEntJacobs.hPart_le_hPartCond μ T hT hmp Q) ?_
    exact le_of_eq (EKLEntJacobs.hPartCond_eq μ T hT hmp Q)
  · rw [← EKLEntJacobs.hPartCond_eq μ T hT hmp Q]
    exact hPartCond_le_hPart μ T hT Q

/-- Measurability of `x ↦ hPart (κ x) T Q` in the fibre variable. -/
theorem measurable_hPart_fiber (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (Q : FinPart X) :
    Measurable fun x => hPart (condExpKernel μ (MeasurableSpace.invariants T) x) T Q := by
  simp only [hPart]
  refine Measurable.iInf (f := fun N x =>
    Hfam (condExpKernel μ (MeasurableSpace.invariants T) x) (joinSets T Q (N + 1)) /
      ((N : ℝ) + 1)) fun N => ?_
  have hmeas : ∀ i : Fin (N + 1) → Fin Q.n,
      Measurable fun x => (condExpKernel μ (MeasurableSpace.invariants T) x)
        (joinSets T Q (N + 1) i) := by
    intro i
    exact (Kernel.measurable_coe (condExpKernel μ (MeasurableSpace.invariants T))
        (Core.joinSets_measurable hT Q (N + 1) i)).mono
      (MeasurableSpace.invariants_le T) le_rfl
  have hsum : Measurable fun x =>
      ∑ i, Real.negMulLog
        (((condExpKernel μ (MeasurableSpace.invariants T) x) (joinSets T Q (N + 1) i)).toReal) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact Real.continuous_negMulLog.measurable.comp ((hmeas i).ennreal_toReal)
  simpa only [Hfam, div_eq_mul_inv, one_mul] using hsum.mul_const (1 / ((N : ℝ) + 1))

/-- `x ↦ hPart (κ x) T Q` is integrable (bounded by the Shannon bound). -/
theorem integrable_hPart_fiber (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (Q : FinPart X) :
    Integrable (fun x => hPart (condExpKernel μ (MeasurableSpace.invariants T) x) T Q) μ := by
  haveI (x : X) : IsProbabilityMeasure (condExpKernel μ (MeasurableSpace.invariants T) x) :=
    IsMarkovKernel.is_probability_measure' x
  refine Integrable.of_bound (measurable_hPart_fiber μ T hT Q).aestronglyMeasurable
    (Real.log Q.n) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Core.hPart_nonneg _ T Q)]
  exact hPart_le_log_card _ T hT Q

/-- **Jacobs' theorem** (Walters 8.4): the entropy of a measure preserving system is the
integral of the fibre entropies over the invariant σ-algebra. -/
theorem ent_jacobs {X : Type} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ) :
    Work.EKLContract.ent μ T =
      ∫⁻ x, Work.EKLContract.ent (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) T ∂μ := by
  classical
  obtain ⟨P, hmono, hgen⟩ := JacRefiningGenSeq (X := X)
  haveI (x : X) : IsProbabilityMeasure (condExpKernel μ (MeasurableSpace.invariants T) x) :=
    IsMarkovKernel.is_probability_measure' x
  have hE4μ : ent μ T = ⨆ m, ENNReal.ofReal (hPart μ T (P m)) :=
    ent_generating μ T hT hmp P hmono hgen
  have hmonoPart : Monotone fun m => fun x =>
      ENNReal.ofReal (hPart (condExpKernel μ (MeasurableSpace.invariants T) x) T (P m)) := by
    intro m n hmn x
    refine ENNReal.ofReal_le_ofReal ?_
    exact hPart_mono_refines _ T hT (refines_iterate P hmono hmn)
  have hmeasPart : ∀ m, Measurable fun x =>
      ENNReal.ofReal (hPart (condExpKernel μ (MeasurableSpace.invariants T) x) T (P m)) :=
    fun m => (measurable_hPart_fiber μ T hT (P m)).ennreal_ofReal
  refine le_antisymm ?_ ?_
  · rw [hE4μ]
    refine iSup_le fun m => ?_
    rw [hPart_eq_integral_hPart_fiber μ T hT hmp (P m)]
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_hPart_fiber μ T hT (P m))
      (ae_of_all _ fun x => Core.hPart_nonneg _ T (P m))]
    refine lintegral_mono fun x => ?_
    exact le_iSup (fun Q : FinPart X =>
      ENNReal.ofReal (hPart (condExpKernel μ (MeasurableSpace.invariants T) x) T Q)) (P m)
  · have hpt : ∀ᵐ x ∂μ, ent (condExpKernel μ (MeasurableSpace.invariants T) x) T
        = ⨆ m, ENNReal.ofReal
            (hPart (condExpKernel μ (MeasurableSpace.invariants T) x) T (P m)) := by
      filter_upwards [EKLEntJacobs.fiber_inv μ T hT hmp] with x hx
      exact ent_generating _ T hT hx P hmono hgen
    rw [lintegral_congr_ae hpt, lintegral_iSup hmeasPart hmonoPart]
    refine iSup_le fun m => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_hPart_fiber μ T hT (P m))
      (ae_of_all _ fun x => Core.hPart_nonneg _ T (P m))]
    rw [← hPart_eq_integral_hPart_fiber μ T hT hmp (P m)]
    rw [hE4μ]
    exact le_iSup (fun m => ENNReal.ofReal (hPart μ T (P m))) m

end Work.EKLComp
