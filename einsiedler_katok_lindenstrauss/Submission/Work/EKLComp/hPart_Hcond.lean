import Mathlib
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.Hpart.Hfam_join_chain
import Submission.Work.EKLComp.Hpart.Hfam_joinSets_succ_fam
import Submission.Work.EKLComp.Hpart.Hcond_mono_alg
import Submission.Work.EKLComp.Hpart.iSup_comap_joinSets
import Submission.Work.EKLComp.Hpart.partSigma_joinSets
import Submission.Work.EKLComp.Hpart.tendsto_Hcond_iSup

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2000000

namespace Work.EKLComp

open Work.EKLContract
open Work.EKLComp.Core
open Work.EKLComp.Hpart

namespace HpcAux

variable {X : Type} [mX : MeasurableSpace X]

theorem preimage_isMPart {ι : Type*} [Fintype ι] {A : ι → Set X} (h : IsMPart A)
    (f : X → X) (hf : Measurable f) : IsMPart (fun i => f ⁻¹' A i) := by
  refine ⟨fun i => (h.measurable i).preimage hf, fun i j hij => ?_, ?_⟩
  · exact (h.disjoint hij).preimage f
  · rw [← Set.preimage_iUnion, h.cover, Set.preimage_univ]

theorem generateFrom_joinSets_le (T : X → X) (hT : Measurable T) (P : FinPart X) (N : ℕ) :
    MeasurableSpace.generateFrom (Set.range (joinSets T P N)) ≤ mX := by
  refine MeasurableSpace.generateFrom_le fun s hs => ?_
  obtain ⟨w, rfl⟩ := hs
  exact joinSets_measurable hT P N w

theorem Hfam_joinSets_zero (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (P : FinPart X) : Hfam μ (joinSets T P 0) = 0 := by
  rw [Hfam]
  simp [joinSets_zero]

theorem Hfam_shift (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (hT : Measurable T)
    (hmp : MeasurePreserving T μ μ) (P : FinPart X) (N : ℕ) :
    Hfam μ (fun w : Fin N → Fin P.n => T ⁻¹' joinSets T P N w) = Hfam μ (joinSets T P N) := by
  rw [Hfam, Hfam]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [MeasurePreserving.measure_preimage hmp (joinSets_measurable hT P N w).nullMeasurableSet]

theorem chainStep (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (hT : Measurable T)
    (hmp : MeasurePreserving T μ μ) (P : FinPart X) (N : ℕ) :
    Hfam μ (joinSets T P (N + 1)) = Hfam μ (joinSets T P N) +
      @Hcond X mX μ P (MeasurableSpace.comap T
        (MeasurableSpace.generateFrom (Set.range (joinSets T P N)))) := by
  have hb : IsMPart (fun w : Fin N → Fin P.n => T ⁻¹' joinSets T P N w) :=
    preimage_isMPart (joinSets_isMPart hT P N) T hT
  have hgen : MeasurableSpace.generateFrom
      (Set.range (fun w : Fin N → Fin P.n => T ⁻¹' joinSets T P N w)) =
      MeasurableSpace.comap T (MeasurableSpace.generateFrom (Set.range (joinSets T P N))) := by
    rw [MeasurableSpace.comap_generateFrom]
    congr 1
    exact Set.range_comp (fun s => T ⁻¹' s) (joinSets T P N)
  have h1 := Hfam_join_chain μ P
    (B := fun w : Fin N → Fin P.n => T ⁻¹' joinSets T P N w) hb
  rw [Hfam_joinSets_succ_fam μ T P N, Hfam_shift μ T hT hmp P N, hgen] at h1
  exact h1

theorem Hfam_eq_sum (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (hT : Measurable T)
    (hmp : MeasurePreserving T μ μ) (P : FinPart X) (N : ℕ) :
    Hfam μ (joinSets T P N) = Finset.sum (Finset.range N) (fun L =>
      @Hcond X mX μ P (MeasurableSpace.comap T
        (MeasurableSpace.generateFrom (Set.range (joinSets T P L))))) := by
  induction N with
  | zero => simpa using Hfam_joinSets_zero μ T P
  | succ N ih =>
      rw [chainStep μ T hT hmp P N, ih, Finset.sum_range_succ]

theorem hPart_eq_iInf (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (hT : Measurable T)
    (hmp : MeasurePreserving T μ μ) (P : FinPart X) :
    hPart μ T P = ⨅ N : ℕ, (Finset.sum (Finset.range (N + 1)) (fun L =>
      @Hcond X mX μ P (MeasurableSpace.comap T
        (MeasurableSpace.generateFrom (Set.range (joinSets T P L)))))) / ((N : ℝ) + 1) := by
  simp only [hPart]
  refine iInf_congr fun N => ?_
  rw [Hfam_eq_sum μ T hT hmp P (N + 1)]

/-- The infimum of the Cesàro averages of a sequence which is bounded below by `L` and converges
to `L` is `L`. -/
theorem cesaro_ciInf_eq {e : ℕ → ℝ} {L : ℝ} (hge : ∀ n, L ≤ e n)
    (ht : Tendsto e atTop (nhds L)) :
    (⨅ n : ℕ, (Finset.sum (Finset.range (n + 1)) e) / ((n : ℝ) + 1)) = L := by
  have havg_ge : ∀ n, L ≤ (Finset.sum (Finset.range (n + 1)) e) / ((n : ℝ) + 1) := by
    intro n
    rw [le_div_iff₀ (by positivity)]
    calc L * ((n : ℝ) + 1) = Finset.sum (Finset.range (n + 1)) (fun _ => L) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ Finset.sum (Finset.range (n + 1)) e := Finset.sum_le_sum fun k _ => hge k
  refine le_antisymm ?_ (le_ciInf havg_ge)
  have hbdd : BddBelow (Set.range fun n : ℕ =>
      (Finset.sum (Finset.range (n + 1)) e) / ((n : ℝ) + 1)) :=
    ⟨L, by rintro y ⟨n, rfl⟩; exact havg_ge n⟩
  have hces : Tendsto (fun n : ℕ =>
      (Finset.sum (Finset.range (n + 1)) e) / ((n : ℝ) + 1)) atTop (nhds L) := by
    have h := ht.cesaro
    refine (h.comp (Filter.tendsto_add_atTop_nat 1)).congr' ?_
    filter_upwards with n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    rw [inv_mul_eq_div]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hev := hces.eventually (isOpen_Iio.mem_nhds (by linarith : L < L + ε))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  exact le_trans (ciInf_le hbdd N) (le_of_lt (hN N le_rfl))

end HpcAux

theorem hPart_Hcond {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T : X → X) (hT : Measurable T) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (P : Work.EKLContract.FinPart X) :
    Work.EKLContract.hPart μ T P =
      Work.EKLContract.Hcond μ P (⨆ n : ℕ, MeasurableSpace.comap (T^[n+1]) (Work.EKLContract.partSigma P)) := by
  have hσmono : Monotone (fun L : ℕ =>
      MeasurableSpace.generateFrom (Set.range (joinSets T P L))) := by
    intro L L' hLL'
    show MeasurableSpace.generateFrom (Set.range (joinSets T P L)) ≤
      MeasurableSpace.generateFrom (Set.range (joinSets T P L'))
    rw [partSigma_joinSets T P L, partSigma_joinSets T P L']
    refine iSup_le fun k => ?_
    exact le_iSup_of_le (Fin.castLE hLL' k) (by simp)
  have hmono : Monotone (fun L : ℕ => MeasurableSpace.comap T
      (MeasurableSpace.generateFrom (Set.range (joinSets T P L)))) :=
    fun L L' hLL' => MeasurableSpace.comap_mono (hσmono hLL')
  have hle : ∀ L : ℕ, MeasurableSpace.comap T
      (MeasurableSpace.generateFrom (Set.range (joinSets T P L))) ≤ mX :=
    fun L => le_trans (MeasurableSpace.comap_mono
      (HpcAux.generateFrom_joinSets_le T hT P L)) (Measurable.comap_le hT)
  have hge : ∀ L : ℕ, @Hcond X mX μ P
      (⨆ n : ℕ, MeasurableSpace.comap (T^[n+1]) (partSigma P)) ≤
      @Hcond X mX μ P (MeasurableSpace.comap T
        (MeasurableSpace.generateFrom (Set.range (joinSets T P L)))) := by
    intro L
    refine Hcond_mono_alg μ P ?_
    rw [← iSup_comap_joinSets T hT P]
    exact le_iSup (fun L : ℕ => MeasurableSpace.comap T
      (MeasurableSpace.generateFrom (Set.range (joinSets T P L)))) L
  have htend : Tendsto (fun L : ℕ => @Hcond X mX μ P (MeasurableSpace.comap T
      (MeasurableSpace.generateFrom (Set.range (joinSets T P L))))) atTop
      (nhds (@Hcond X mX μ P (⨆ n : ℕ,
        MeasurableSpace.comap (T^[n+1]) (partSigma P)))) := by
    have h := tendsto_Hcond_iSup μ P (fun L : ℕ => MeasurableSpace.comap T
      (MeasurableSpace.generateFrom (Set.range (joinSets T P L)))) hmono hle
    rwa [iSup_comap_joinSets T hT P] at h
  rw [HpcAux.hPart_eq_iInf μ T hT hmp P]
  exact HpcAux.cesaro_ciInf_eq hge htend

end Work.EKLComp
