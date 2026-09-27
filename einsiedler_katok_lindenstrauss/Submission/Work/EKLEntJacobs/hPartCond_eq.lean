import Mathlib
import Submission.Work.EKLComp.EntJacobsAux
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.tendsto_hPart
import Submission.Work.EKLEntJacobs.fiber_inv
import Submission.Work.EKLEntJacobs.Hcond_kernel
import Submission.Work.EKLEntJacobs.kernel_mean

/-!
# The conditional entropy as the integral of the fibre entropies

`hPartCond μ T Q (invariants T) = ∫ x, hPart (condExpKernel μ (invariants T) x) T Q ∂μ`.

The left-hand side is the Fekete infimum `⨅ N, H_μ(⋁_{k<N}T^{-k}Q | invariants T)/(N+1)` of the
conditional entropies w.r.t. the σ-algebra of `T`-invariant sets; the right-hand side is the
integral of the Kolmogorov–Sinai entropy of the conditional measures `κ_x` on the `T`-invariant
σ-algebra (Walters 8.4 / Jacobs' theorem, per-partition form).

Both sides are the limit of the same sequence `N ↦ H_μ(⋁_{k<N}T^{-k}Q | invariants T)/N`:

* the conditional Fekete infimum equals that limit because `N ↦ H_μ(⋁_{k<N}T^{-k}Q | invariants T)`
  is subadditive (a.e. subadditivity of `Hfam` for the a.e. `T`-invariant conditional measures,
  integrated);
* the fibre integral equals the limit by dominated convergence, using that a.e. `κ_x` is
  `T`-invariant (`fiber_inv`) and Fekete's lemma for each such measure, together with the uniform
  bound `Hfam ≤ log (card)`.
-/

namespace Work.EKLEntJacobs

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators

noncomputable section

/-! ## A Fekete lemma: the infimum `⨅ N, a (N+1) / (N+1)` is the limit of `a n / n` -/

theorem ciInf_succ_div_eq_lim {a : ℕ → ℝ} (hsub : Subadditive a) (hnonneg : ∀ n, 0 ≤ a n) :
    (⨅ N : ℕ, a (N + 1) / ((N : ℝ) + 1)) = Subadditive.lim hsub := by
  have hbdd : BddBelow (Set.range fun n : ℕ => a n / n) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact div_nonneg (hnonneg n) (Nat.cast_nonneg n)
  have hlim := hsub.tendsto_lim hbdd
  have hbdd' : BddBelow (Set.range fun N : ℕ => a (N + 1) / ((N : ℝ) + 1)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨N, rfl⟩
    exact div_nonneg (hnonneg (N + 1)) (by positivity)
  refine le_antisymm ?_ ?_
  · by_contra hcon
    rw [not_le] at hcon
    set δ : ℝ := ((⨅ N : ℕ, a (N + 1) / ((N : ℝ) + 1)) - Subadditive.lim hsub) / 2 with hδ
    have hδpos : 0 < δ := by rw [hδ]; linarith
    have hev : ∀ᶠ n : ℕ in atTop, a n / n < Subadditive.lim hsub + δ :=
      hlim.eventually (isOpen_Iio.mem_nhds (lt_add_of_pos_right (Subadditive.lim hsub) hδpos))
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
    have h1 : (⨅ N : ℕ, a (N + 1) / ((N : ℝ) + 1)) ≤ a (N₀ + 1) / ((N₀ : ℝ) + 1) :=
      ciInf_le hbdd' N₀
    have h2 : a (N₀ + 1) / ((N₀ : ℝ) + 1) < Subadditive.lim hsub + δ := by
      have := hN₀ (N₀ + 1) (by omega)
      simpa [Nat.cast_add, Nat.cast_one] using this
    rw [hδ] at h2
    linarith
  · refine le_ciInf fun N => ?_
    have := hsub.lim_le_div hbdd (show N + 1 ≠ 0 by omega)
    simpa [Nat.cast_add, Nat.cast_one] using this

/-! ## Rewriting `HcondFam` along `invariants T` as an integral of the fibre `Hfam` -/

theorem HcondFam_join_eq_integral {X : Type} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (Q : Work.EKLContract.FinPart X) (N : ℕ) :
    Work.EKLComp.HcondFam μ (Work.EKLContract.joinSets T Q N) (MeasurableSpace.invariants T)
      = ∫ x, Work.EKLContract.Hfam
          (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
          (Work.EKLContract.joinSets T Q N) ∂μ := by
  rw [Hcond_kernel μ T (fun i => Work.EKLComp.Core.joinSets_measurable hT Q N i)]
  simp only [Work.EKLContract.Hfam]

/-! ## Measurability and integrability of the fibre entropy -/

theorem measurable_Hfam_fiber {X : Type} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (Q : Work.EKLContract.FinPart X) (N : ℕ) :
    Measurable (fun x => Work.EKLContract.Hfam
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
        (Work.EKLContract.joinSets T Q N)) := by
  simp only [Work.EKLContract.Hfam]
  refine Finset.measurable_sum Finset.univ (fun i _ => ?_)
  have hmeas : Measurable (fun x =>
      ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x
        (Work.EKLContract.joinSets T Q N i)) :=
    (Kernel.measurable_coe (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T))
        (Work.EKLComp.Core.joinSets_measurable hT Q N i)).mono
      (MeasurableSpace.invariants_le T) le_rfl
  exact Real.continuous_negMulLog.measurable.comp hmeas.ennreal_toReal

theorem integrable_Hfam_fiber {X : Type} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (Q : Work.EKLContract.FinPart X) (N : ℕ) :
    Integrable (fun x => Work.EKLContract.Hfam
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
        (Work.EKLContract.joinSets T Q N)) μ := by
  refine Integrable.of_bound (measurable_Hfam_fiber μ T hT Q N).aestronglyMeasurable
    (Real.log (Fintype.card (Fin N → Fin Q.n) : ℝ)) ?_
  filter_upwards with x
  haveI : IsProbabilityMeasure
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
    IsMarkovKernel.isProbabilityMeasure x
  rw [Real.norm_of_nonneg (Work.EKLComp.Core.Hfam_nonneg
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
      (Work.EKLContract.joinSets T Q N))]
  exact Work.EKLComp.Core.Hfam_le_log_card
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
      (Work.EKLComp.Core.joinSets_isMPart hT Q N)

/-! ## Subadditivity of the conditional entropy sequence -/

theorem subadditive_HcondFam_join {X : Type} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (Q : Work.EKLContract.FinPart X) :
    Subadditive (fun N => Work.EKLComp.HcondFam μ
      (Work.EKLContract.joinSets T Q N) (MeasurableSpace.invariants T)) := by
  intro m n
  show Work.EKLComp.HcondFam μ (Work.EKLContract.joinSets T Q (m + n))
        (MeasurableSpace.invariants T)
      ≤ Work.EKLComp.HcondFam μ (Work.EKLContract.joinSets T Q m)
          (MeasurableSpace.invariants T)
        + Work.EKLComp.HcondFam μ (Work.EKLContract.joinSets T Q n)
          (MeasurableSpace.invariants T)
  rw [HcondFam_join_eq_integral μ T hT Q (m + n),
      HcondFam_join_eq_integral μ T hT Q m,
      HcondFam_join_eq_integral μ T hT Q n]
  have hle : (fun x => Work.EKLContract.Hfam
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
        (Work.EKLContract.joinSets T Q (m + n)))
      ≤ᵐ[μ] (fun x => Work.EKLContract.Hfam
          (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
          (Work.EKLContract.joinSets T Q m)
        + Work.EKLContract.Hfam
          (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
          (Work.EKLContract.joinSets T Q n)) := by
    filter_upwards [fiber_inv μ T hT hmp] with x hx
    exact Work.EKLComp.Core.Hfam_joinSets_add_le
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) hx Q m n
  calc ∫ x, Work.EKLContract.Hfam
          (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
          (Work.EKLContract.joinSets T Q (m + n)) ∂μ
      ≤ ∫ x, (Work.EKLContract.Hfam
            (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
            (Work.EKLContract.joinSets T Q m)
          + Work.EKLContract.Hfam
            (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
            (Work.EKLContract.joinSets T Q n)) ∂μ :=
        integral_mono_ae (integrable_Hfam_fiber μ T hT Q (m + n))
          ((integrable_Hfam_fiber μ T hT Q m).add (integrable_Hfam_fiber μ T hT Q n)) hle
    _ = ∫ x, Work.EKLContract.Hfam
            (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
            (Work.EKLContract.joinSets T Q m) ∂μ
          + ∫ x, Work.EKLContract.Hfam
            (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
            (Work.EKLContract.joinSets T Q n) ∂μ :=
        integral_add (integrable_Hfam_fiber μ T hT Q m) (integrable_Hfam_fiber μ T hT Q n)

/-! ## Almost-everywhere convergence of the fibre entropy averages -/

theorem tendsto_hPart_fiber_ae {X : Type} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (Q : Work.EKLContract.FinPart X) :
    ∀ᵐ x ∂μ, Filter.Tendsto
      (fun N : ℕ => Work.EKLContract.Hfam
          (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
          (Work.EKLContract.joinSets T Q N) / (N : ℝ))
      Filter.atTop (nhds (Work.EKLContract.hPart
          (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) T Q)) := by
  filter_upwards [fiber_inv μ T hT hmp] with x hx
  haveI : IsProbabilityMeasure
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
    IsMarkovKernel.isProbabilityMeasure x
  exact Work.EKLComp.tendsto_hPart
    (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) hx Q

/-! ## The main identity -/

theorem hPartCond_eq {X : Type} [mX : MeasurableSpace X] [StandardBorelSpace X]
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (Q : Work.EKLContract.FinPart X) :
    Work.EKLComp.hPartCond μ T Q (MeasurableSpace.invariants T)
      = ∫ x, Work.EKLContract.hPart
          (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) T Q ∂μ := by
  have hsub := subadditive_HcondFam_join μ T hT hmp Q
  have hnonneg : ∀ n, 0 ≤ Work.EKLComp.HcondFam μ
      (Work.EKLContract.joinSets T Q n) (MeasurableSpace.invariants T) := by
    intro n
    rw [HcondFam_join_eq_integral μ T hT Q n]
    refine integral_nonneg (fun x => ?_)
    haveI : IsProbabilityMeasure
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
      IsMarkovKernel.isProbabilityMeasure x
    exact Work.EKLComp.Core.Hfam_nonneg
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
      (Work.EKLContract.joinSets T Q n)
  have hLHS : Work.EKLComp.hPartCond μ T Q (MeasurableSpace.invariants T)
      = Subadditive.lim hsub := by
    show (⨅ N : ℕ, Work.EKLComp.HcondFam μ (Work.EKLContract.joinSets T Q (N + 1))
        (MeasurableSpace.invariants T) / ((N : ℝ) + 1)) = Subadditive.lim hsub
    exact ciInf_succ_div_eq_lim hsub hnonneg
  have hIntEq : ∀ N : ℕ, ∫ x, Work.EKLContract.Hfam
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
        (Work.EKLContract.joinSets T Q N) / (N : ℝ) ∂μ
      = Work.EKLComp.HcondFam μ (Work.EKLContract.joinSets T Q N)
          (MeasurableSpace.invariants T) / (N : ℝ) := by
    intro N
    rw [MeasureTheory.integral_div, ← HcondFam_join_eq_integral μ T hT Q N]
  have hbddSeq : BddBelow (Set.range fun n : ℕ =>
      Work.EKLComp.HcondFam μ (Work.EKLContract.joinSets T Q n)
        (MeasurableSpace.invariants T) / (n : ℝ)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    exact div_nonneg (hnonneg n) (Nat.cast_nonneg n)
  have hlim2 : Filter.Tendsto
      (fun N : ℕ => ∫ x, Work.EKLContract.Hfam
          (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
          (Work.EKLContract.joinSets T Q N) / (N : ℝ) ∂μ)
      Filter.atTop (nhds (Subadditive.lim hsub)) := by
    refine (hsub.tendsto_lim hbddSeq).congr' (Eventually.of_forall (fun N => (hIntEq N).symm))
  have hbdd : ∀ N : ℕ, ∀ᵐ x ∂μ, ‖Work.EKLContract.Hfam
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
        (Work.EKLContract.joinSets T Q N) / (N : ℝ)‖ ≤ Real.log (Q.n : ℝ) := by
    intro N
    filter_upwards with x
    haveI : IsProbabilityMeasure
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
      IsMarkovKernel.isProbabilityMeasure x
    have hnn : 0 ≤ Work.EKLContract.Hfam
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
        (Work.EKLContract.joinSets T Q N) :=
      Work.EKLComp.Core.Hfam_nonneg
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
        (Work.EKLContract.joinSets T Q N)
    rw [Real.norm_of_nonneg (div_nonneg hnn (Nat.cast_nonneg N))]
    rcases eq_or_ne N 0 with hN0 | hNn
    · subst hN0
      rw [Nat.cast_zero, div_zero]
      rcases Nat.eq_zero_or_pos Q.n with hQ | hQ
      · rw [hQ]; simp
      · exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q.n by omega))
    · have hle := Work.EKLComp.Core.Hfam_le_log_card
          (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
          (Work.EKLComp.Core.joinSets_isMPart hT Q N)
      have hcard : Fintype.card (Fin N → Fin Q.n) = Q.n ^ N := by
        rw [Fintype.card_fun]
        simp
      rw [hcard, Nat.cast_pow, Real.log_pow] at hle
      rw [div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hNn)]
      calc Work.EKLContract.Hfam
              (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
              (Work.EKLContract.joinSets T Q N)
          ≤ (N : ℝ) * Real.log (Q.n : ℝ) := hle
        _ = Real.log (Q.n : ℝ) * (N : ℝ) := by ring
  have hconv := tendsto_hPart_fiber_ae μ T hT hmp Q
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun N x => Work.EKLContract.Hfam
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x)
        (Work.EKLContract.joinSets T Q N) / (N : ℝ))
    (f := fun x => Work.EKLContract.hPart
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) T Q)
    (fun _ : X => Real.log (Q.n : ℝ))
    (fun N => ((measurable_Hfam_fiber μ T hT Q N).div_const (N : ℝ)).aestronglyMeasurable)
    (integrable_const (Real.log (Q.n : ℝ)))
    hbdd
    hconv
  rw [hLHS]
  exact (tendsto_nhds_unique hdct hlim2).symm

end

end Work.EKLEntJacobs
