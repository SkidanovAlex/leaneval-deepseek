import Mathlib
import Submission.Work.EKLComp.USCBasic
import Submission.Work.EKLComp.exists_small_part
import Submission.Work.EKLComp.exists_part_seq
import Submission.Work.EKLComp.Crat_dense
import Submission.Work.EKLComp.ent_generating
import Submission.Work.EKLComp.hPart_Hcond
import Submission.Work.EKLComp.HPE2
import Submission.Work.EKLComp.HPE3
import Submission.Work.EKLComp.Hcond
import Submission.Work.EKLComp.uniform_inj_of_isCompact
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLComp.Core
import Submission.Work.EKLComp.Entropy
import Submission.Work.EKLComp.exists_level_null
import Submission.Work.EKLComp.HcondFam_join
import Submission.Work.EKLComp.prop92defs
import Submission.Work.EKLComp.hPart_exists_refining
import Submission.Work.EKLComp.measure_iInter_eq_of_forall_eq_univ
import Submission.Work.EKLComp.EntGenSmall
import Submission.Work.EKLComp.prop92win.hPart_winPart
import Submission.Work.EKLComp.prop92win.hcond_orbit_eq_zero_hK

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

noncomputable section

namespace Work.EKLComp

open Work.EKLContract

set_option maxHeartbeats 2000000

/-- `shiftZ t 1` is the map `x ↦ aDiag t • x`. -/
theorem shiftZ_one_eq (t : Fin 3 → ℝ) : shiftZ t 1 = fun x : X3 => aDiag t • x := by
  funext x
  simp [shiftZ, aZ_one]

/-- **Step A of EKL Prop 9.2.** For a partition `Q` with `ν`-null frontiers,
`hPart ν T Q ≤ hPart ν T P`. -/
theorem hPart_le_of_atomSmall (t : Fin 3 → ℝ) (ht : ∃ i j : Fin 3, t i ≠ t j) {K : Set X3}
    (hK : IsCompact K) (hbi : shiftZ t 1 '' K = K)
    {ν : Measure X3} [IsProbabilityMeasure ν] (hmp : MeasurePreserving (shiftZ t 1) ν ν)
    (hKν : ν K = 1) {P : FinPart X3} {δ r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1/2)
    (hinj : ∀ x ∈ K, ∀ g h : SL3, g ∈ V r → h ∈ V r → g • x = h • x → g = h)
    (hδr : δ ≤ r) (hδexp : δ ≤ r * Real.exp (-(tsum t)) / 2) (hδ0 : 0 < δ)
    (hsmall : AtomSmall K δ P) (Q : FinPart X3) (hQ : ∀ i, ν (frontier (Q.parts i)) = 0) :
    hPart ν (shiftZ t 1) Q ≤ hPart ν (shiftZ t 1) P := by
  have hfwd : ∀ x ∈ K, shiftZ t 1 x ∈ K := fun x hx => by
    have h : shiftZ t 1 x ∈ shiftZ t 1 '' K := ⟨x, hx, rfl⟩
    rwa [hbi] at h
  have hbwd : ∀ x ∈ K, shiftZ t (-1) x ∈ K := by
    intro x hx
    have hcomp : shiftZ t 1 (shiftZ t (-1) x) = x := by
      show aZ t 1 • (aZ t (-1) • x) = x
      rw [← mul_smul, ← aZ_add]
      rw [show (1:ℤ) + (-1) = 0 from by norm_num, aZ_zero, one_smul]
    have hmem : shiftZ t 1 (shiftZ t (-1) x) ∈ shiftZ t 1 '' K := by
      rw [hcomp, hbi]; exact hx
    obtain ⟨z, hz, hzy⟩ := hmem
    have hzx : z = shiftZ t (-1) x := (bijective_shiftZ t 1).1 hzy
    rwa [← hzx]
  have hstep1 : Hcond ν Q (orbitSigma t P ⊔ pastSig t Q) = 0 :=
    hcond_orbit_eq_zero_hK t ht hK hfwd hbwd hmp hKν hr0 hr1 hinj hδr hδexp hδ0 hsmall Q hQ
  have hchain : ∀ m : ℕ, hPart ν (shiftZ t 1) Q
      ≤ hPart ν (shiftZ t 1) P + Hcond ν Q (Cwin t P Q m) := by
    intro m
    have hR : hPart ν (shiftZ t 1) (joinPart__USCBasic (winPart t P m) Q)
        = Hcond ν (joinPart__USCBasic (winPart t P m) Q) (pastSig t (joinPart__USCBasic (winPart t P m) Q)) :=
      hPart_eq_Hcond_pastSig (ν := ν) t hmp _
    have hpart_le : partSigma (winPart t P m) ≤ partSigma (joinPart__USCBasic (winPart t P m) Q) := by
      rw [partSigma_joinPart]; exact le_sup_left
    have hpast_le : pastSig t (winPart t P m) ≤ pastSig t (joinPart__USCBasic (winPart t P m) Q) := by
      unfold pastSig
      refine iSup_le fun n => ?_
      exact le_trans (MeasurableSpace.comap_mono hpart_le)
        (le_iSup (fun n' : ℕ => MeasurableSpace.comap ((shiftZ t 1)^[n'+1])
          (partSigma (joinPart__USCBasic (winPart t P m) Q))) n)
    calc hPart ν (shiftZ t 1) Q
        ≤ hPart ν (shiftZ t 1) (joinPart__USCBasic (winPart t P m) Q) :=
          hPart_le_of_refines ν (measurable_shiftZ t 1) (Refines_joinPart_right _ _)
      _ = Hcond ν (joinPart__USCBasic (winPart t P m) Q) (pastSig t (joinPart__USCBasic (winPart t P m) Q)) := hR
      _ = Hcond ν (winPart t P m) (pastSig t (joinPart__USCBasic (winPart t P m) Q))
            + Hcond ν Q (pastSig t (joinPart__USCBasic (winPart t P m) Q) ⊔ partSigma (winPart t P m)) :=
          Hcond_joinPart ν (winPart t P m) Q _
      _ ≤ Hcond ν (winPart t P m) (pastSig t (winPart t P m))
            + Hcond ν Q (Cwin t P Q m) :=
          add_le_add (Hpart.Hcond_mono_alg ν (winPart t P m) hpast_le) le_rfl
      _ = hPart ν (shiftZ t 1) (winPart t P m) + Hcond ν Q (Cwin t P Q m) := by
          rw [← hPart_eq_Hcond_pastSig (ν := ν) t hmp (winPart t P m)]
      _ = hPart ν (shiftZ t 1) P + Hcond ν Q (Cwin t P Q m) := by
          rw [prop92win.hPart_winPart t hmp P m]
  have hL : Hcond ν Q (⨆ m, Cwin t P Q m) ≤ 0 :=
    le_trans (Hpart.Hcond_mono_alg ν Q (le_iSup_Cwin t P Q)) (le_of_eq hstep1)
  have htend : Tendsto (fun m => Hcond ν Q (Cwin t P Q m)) atTop
      (nhds (Hcond ν Q (⨆ m, Cwin t P Q m))) :=
    Hpart.tendsto_Hcond_iSup ν Q _ (Cwin_mono t P Q) (Cwin_le t P Q)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hε' : Hcond ν Q (⨆ m, Cwin t P Q m) < ε := lt_of_le_of_lt hL hε
  have hev := htend.eventually (isOpen_Iio.mem_nhds hε')
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hNc := hchain N
  linarith [hN N le_rfl]

/-- **EKL Prop 9.2 for a bi-invariant compact set.** -/
theorem prop92_binvariant (t : Fin 3 → ℝ) (ht : ∃ i j : Fin 3, t i ≠ t j) {K : Set X3}
    (hK : IsCompact K) (hbi : shiftZ t 1 '' K = K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P : FinPart X3, AtomSmall K δ P →
      ∀ ν : Measure X3, IsProbabilityMeasure ν → ν K = 1 →
        MeasurePreserving (shiftZ t 1) ν ν →
        ent ν (shiftZ t 1) = ENNReal.ofReal (hPart ν (shiftZ t 1) P) := by
  obtain ⟨η₀, hη₀pos, hη₀⟩ := uniform_inj_of_isCompact K hK
  set r : ℝ := min η₀ (1/2) with hrdef
  have hr0 : 0 < r := lt_min hη₀pos (by norm_num)
  have hr1 : r ≤ 1/2 := min_le_right _ _
  have hrinj : ∀ x ∈ K, ∀ g h : SL3, g ∈ V r → h ∈ V r → g • x = h • x → g = h := by
    intro x hx g h hg hh
    have hle : r ≤ η₀ := min_le_left _ _
    exact hη₀ x hx g h (V_mono hle hg) (V_mono hle hh)
  set δ : ℝ := min r (r * Real.exp (-(tsum t)) / 2) with hδdef
  have hδ0 : 0 < δ := lt_min hr0 (by positivity)
  have hδr : δ ≤ r := min_le_left _ _
  have hδexp : δ ≤ r * Real.exp (-(tsum t)) / 2 := min_le_right _ _
  refine ⟨δ, hδ0, ?_⟩
  intro P hsmall ν hνprob hKν hmp
  haveI := hνprob
  refine le_antisymm ?_ (le_iSup (fun Q : FinPart X3 =>
    ENNReal.ofReal (hPart ν (shiftZ t 1) Q)) P)
  refine iSup_le fun Q => ?_
  obtain ⟨Qs, hmono, hfront, hgen⟩ := exists_part_seq ν
  have hbound : ∀ m : ℕ, hPart ν (shiftZ t 1) Q ≤ hPart ν (shiftZ t 1) P + CHp ν (Qs m) Q := by
    intro m
    refine le_trans (hPart_le_hPart_add_CHp ν hmp (Qs m) Q) ?_
    exact add_le_add (hPart_le_of_atomSmall t ht hK hbi hmp hKν hr0 hr1 hrinj hδr hδexp
      hδ0 hsmall (Qs m) (hfront m)) le_rfl
  refine ENNReal.ofReal_le_ofReal ?_
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨M, hM⟩ := CHp_small ν Qs hmono hgen Q ε hε
  have := hbound M
  linarith


/-- **The reduction to a bi-invariant compact set, and the main theorem.** -/
theorem prop92 (t : Fin 3 → ℝ) (ht : ∃ i j : Fin 3, t i ≠ t j) (K : Set Work.EKLContract.X3)
    (hK : IsCompact K) (hfwd : ∀ x ∈ K, Work.EKLContract.aDiag t • x ∈ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P : Work.EKLContract.FinPart Work.EKLContract.X3,
      Work.EKLComp.AtomSmall K δ P →
      ∀ ν : MeasureTheory.Measure Work.EKLContract.X3, MeasureTheory.IsProbabilityMeasure ν →
        ν K = 1 → MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ν ν →
        Work.EKLContract.ent ν (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)
          = ENNReal.ofReal (Work.EKLContract.hPart ν (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) P) := by
  classical
  have hshift : ∀ n : ℕ, shiftZ t n = fun x : X3 => aZ t (n : ℤ) • x := fun _ => rfl
  have hc : ∀ n : ℕ, Continuous ((shiftZ t 1)^[n]) := by
    intro n
    induction n with
    | zero => exact continuous_id
    | succ n ih =>
      rw [Function.iterate_succ']
      exact (continuous_const_smul (aZ t 1)).comp ih
  have hfwd' : ∀ x ∈ K, shiftZ t 1 x ∈ K := fun x hx => by
    simpa [shiftZ, aZ_one] using hfwd x hx
  set K' : Set X3 := ⋂ n : ℕ, (shiftZ t 1)^[n] '' K with hK'def
  have hmeasK : MeasurableSet K := hK.isClosed.measurableSet
  have hsub : ∀ n : ℕ, (shiftZ t 1)^[n] '' K ⊆ K := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ', Set.image_comp]
      refine Set.Subset.trans (Set.image_mono ih) ?_
      rintro y ⟨z, hz, rfl⟩
      simpa [shiftZ, aZ_one] using hfwd' z hz
  have hK'sub : K' ⊆ K := fun x hx => by
    have h := Set.mem_iInter.mp hx 0
    simpa using h
  have hK'closed : IsClosed K' := by
    rw [hK'def]
    exact isClosed_iInter fun n => (hK.image (hc n)).isClosed
  have hK'cpt : IsCompact K' := hK.of_isClosed_subset hK'closed hK'sub
  have hK'eq : shiftZ t 1 '' K' = K' := by
    have hstep : ∀ n : ℕ, shiftZ t 1 '' ((shiftZ t 1)^[n] '' K) = (shiftZ t 1)^[n+1] '' K := by
      intro n
      rw [← Set.image_comp, ← Function.iterate_succ']
    have hshift : (⋂ n : ℕ, (shiftZ t 1)^[n+1] '' K) = (⋂ n : ℕ, (shiftZ t 1)^[n] '' K) := by
      refine le_antisymm ?_ ?_
      · intro x hx
        refine Set.mem_iInter.mpr fun n => ?_
        cases n with
        | zero => simpa using hsub 1 (Set.mem_iInter.mp hx 0)
        | succ m => exact Set.mem_iInter.mp hx m
      · intro x hx
        refine Set.mem_iInter.mpr fun n => Set.mem_iInter.mp hx (n + 1)
    calc shiftZ t 1 '' K'
        = shiftZ t 1 '' (⋂ n : ℕ, (shiftZ t 1)^[n] '' K) := by rw [hK'def]
      _ = ⋂ n : ℕ, shiftZ t 1 '' ((shiftZ t 1)^[n] '' K) :=
            Set.image_iInter (bijective_shiftZ t 1) _
      _ = ⋂ n : ℕ, (shiftZ t 1)^[n+1] '' K := by simp_rw [hstep]
      _ = ⋂ n : ℕ, (shiftZ t 1)^[n] '' K := hshift
      _ = K' := by rw [hK'def]
  obtain ⟨δ, hδ0, hδ⟩ := prop92_binvariant t ht hK'cpt hK'eq
  refine ⟨δ, hδ0, ?_⟩
  intro P hsmall ν hνprob hKν hmp
  haveI := hνprob
  have hmp' : MeasurePreserving (shiftZ t 1) ν ν := by
    simpa only [shiftZ_one_eq t] using hmp
  have hν : ν K' = 1 := by
    rw [hK'def]
    have hmeas : ∀ n : ℕ, MeasurableSet ((shiftZ t 1)^[n] '' K) :=
      fun n => (hK.image (hc n)).isClosed.measurableSet
    have hc' : ∀ n : ℕ, ν ((shiftZ t 1)^[n] '' K) = ν Set.univ := by
      intro n
      have hinj : Function.Injective ((shiftZ t 1)^[n]) := (bijective_shiftZ t 1).1.iterate n
      calc ν ((shiftZ t 1)^[n] '' K)
          = ν ((shiftZ t 1)^[n] ⁻¹' ((shiftZ t 1)^[n] '' K)) :=
            (MeasurePreserving.measure_preimage (hmp'.iterate n) (hmeas n).nullMeasurableSet).symm
        _ = ν K := by rw [Set.preimage_image_eq K hinj]
        _ = ν Set.univ := by rw [measure_univ]; exact hKν
    have := measure_iInter_eq_of_forall_eq_univ hmeas (measure_ne_top ν _) hc'
    simpa [measure_univ] using this
  have hsmall' : AtomSmall K' δ P := by
    intro i x hx hxi y hy hyi
    exact hsmall i x (hK'sub hx) hxi y (hK'sub hy) hyi
  have hres := hδ P hsmall' ν hνprob hν hmp'
  simpa [shiftZ_one_eq t] using hres

end Work.EKLComp
