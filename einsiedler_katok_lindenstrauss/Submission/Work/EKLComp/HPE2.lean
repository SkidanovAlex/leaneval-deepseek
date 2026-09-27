import Submission.Work.EKLComp.HPE
import Submission.Work.EKLComp.HPE3
import Submission.Work.EKLComp.HcondFam_tendsto

/-!
# C3 (E5) — the conditional-entropy formula `h_μ(T,P) = H_μ(P | ⋁_{n≥1} T^{-n} P)`
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

set_option maxHeartbeats 2000000

namespace Work.EKLComp.Core

open Work.EKLContract

variable {X : Type} [mX : MeasurableSpace X]

/-- The σ-algebra `⋁_{n≥1} T^{-n}(σ P)`. -/
def mInf (T : X → X) (P : FinPart X) : MeasurableSpace X :=
  ⨆ n : ℕ, MeasurableSpace.comap (T^[n+1]) (partSigma P)

theorem JN_mono (T : X → X) (P : FinPart X) : Monotone (JN T P) := by
  intro N M hNM
  refine iSup_le fun k => ?_
  exact le_iSup (fun j : Fin M => MeasurableSpace.comap (T^[(j:ℕ)+1]) (partSigma P))
    ⟨k, by omega⟩

theorem JN_le (T : X → X) (hT : Measurable T) (P : FinPart X) (N : ℕ) : JN T P N ≤ mX := by
  have hP : IsMPart P.parts := ⟨P.measurable, P.disjoint, P.cover⟩
  refine iSup_le fun k => ?_
  refine MeasurableSpace.comap_le_iff_le_map.mpr ?_
  intro S hS
  exact MeasurableSet.preimage ((MeasurableSpace.le_def.mp (partSigmaFam_le hP)) S hS)
    (hT.iterate ((k:ℕ)+1))

theorem a0_eq_zero (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (P : FinPart X) :
    Hfam μ (joinSets T P 0) = 0 := by
  have h : ∀ w : Fin 0 → Fin P.n, Real.negMulLog (μ (joinSets T P 0 w)).toReal = 0 := by
    intro w
    simp [joinSets]
  simp [Hfam, h]

theorem Hfam_joinSets_succ (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (P : FinPart X) (N : ℕ) :
    Hfam μ (joinSets T P (N+1)) = Hfam μ (joinSets T P N) + HcondFam X μ P.parts (JN T P N) := by
  have hT : Measurable T := hmp.measurable
  have hA : IsMPart (fun v : Fin N → Fin P.n => T ⁻¹' joinSets T P N v) := by
    refine ⟨fun v => ?_, ?_, ?_⟩
    · exact MeasurableSet.preimage (joinSets_measurable hT P N v) hT
    · intro u v huv
      refine Set.disjoint_left.mpr fun x hx hy => ?_
      exact Set.disjoint_left.mp (joinSets_disjoint T P N huv) hx hy
    · ext x
      constructor
      · intro _; exact Set.mem_univ x
      · intro _
        have h : T x ∈ (⋃ v, joinSets T P N v) := by rw [joinSets_iUnion]; trivial
        obtain ⟨v, hv⟩ := Set.mem_iUnion.mp h
        exact Set.mem_iUnion.mpr ⟨v, hv⟩
  have hB : IsMPart P.parts := ⟨P.measurable, P.disjoint, P.cover⟩
  have hstep : Hfam μ (joinSets T P (N+1)) =
      Hfam μ (fun q : (Fin N → Fin P.n) × Fin P.n =>
        (fun v : Fin N → Fin P.n => T ⁻¹' joinSets T P N v) q.1 ∩ P.parts q.2) := by
    rw [← Hfam_equiv μ ((Equiv.prodComm (Fin N → Fin P.n) (Fin P.n)).trans
      (Fin.consEquiv (fun _ : Fin (N+1) => Fin P.n))) (joinSets T P (N+1))]
    refine Finset.sum_congr rfl fun q _ => ?_
    dsimp only
    have hq : ((Equiv.prodComm (Fin N → Fin P.n) (Fin P.n)).trans
        (Fin.consEquiv (fun _ : Fin (N+1) => Fin P.n))) q = Fin.cons q.2 q.1 := by
      simp [Equiv.trans_apply, Equiv.prodComm_apply, Fin.consEquiv]
    rw [hq, joinSets_cons]
  rw [hstep,
    HcondFam_join' μ (fun v : Fin N → Fin P.n => T ⁻¹' joinSets T P N v) P.parts hA hB,
    Hfam_shift μ hmp P N, partSigmaFam_shift T P N]

theorem hPart_eq_Hcond (μ : Measure X) [IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasurePreserving T μ μ) (P : FinPart X) :
    hPart μ T P = Hcond μ P (mInf T P) := by
  have hT : Measurable T := hmp.measurable
  have hmi : (⨆ n : ℕ, JN T P n) = mInf T P := by
    rw [mInf]; exact iSup_JN T P
  -- (i) the recursion a(N+1) = a N + c N, hence a(N+1) = Σ_{k≤N} c k
  have hrec : ∀ N : ℕ, Hfam μ (joinSets T P (N+1)) =
      Hfam μ (joinSets T P N) + HcondFam X μ P.parts (JN T P N) :=
    fun N => Hfam_joinSets_succ μ hmp P N
  have hsum : ∀ N : ℕ, Hfam μ (joinSets T P N) =
      ∑ k ∈ Finset.range N, HcondFam X μ P.parts (JN T P k) := by
    intro N
    induction N with
    | zero => simpa using a0_eq_zero μ T P
    | succ N ih =>
      rw [hrec N, ih, Finset.sum_range_succ]
  -- (ii) the increments converge to the conditional entropy
  have hc : Tendsto (fun N : ℕ => HcondFam X μ P.parts (JN T P N)) atTop
      (𝓝 (Hcond μ P (mInf T P))) := by
    have h1 := HcondFam_tendsto μ P.parts (JN T P) (JN_mono T P) (fun n => JN_le T hT P n)
    have h2 : HcondFam X μ P.parts (⨆ n : ℕ, JN T P n) = Hcond μ P (mInf T P) := by
      rw [hmi, HcondFam_eq_Hcond]
    rwa [h2] at h1
  -- (iii) Cesàro
  have hces : Tendsto (fun N : ℕ =>
      ((N : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (N+1), HcondFam X μ P.parts (JN T P k)) atTop
      (𝓝 (Hcond μ P (mInf T P))) := by
    have h1 : Tendsto (fun n : ℕ =>
        (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, HcondFam X μ P.parts (JN T P k)) atTop
        (𝓝 (Hcond μ P (mInf T P))) := hc.cesaro
    have h2 := h1.comp (tendsto_add_atTop_nat 1)
    refine h2.congr' ?_
    filter_upwards with N
    simp only [Function.comp_apply]
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hcast]
  -- (iv) Fekete: hPart is the limit of the averages
  have hsub : Subadditive (fun N => Hfam μ (joinSets T P N)) :=
    fun m n => Hfam_joinSets_add_le μ hmp P m n
  have hbdd : BddBelow (Set.range fun n : ℕ => Hfam μ (joinSets T P n) / n) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n, rfl⟩
    rcases eq_or_ne n 0 with h | h
    · simp [h]
    · exact div_nonneg (Hfam_nonneg μ _) (Nat.cast_nonneg n)
  have hlim : Tendsto (fun N : ℕ => Hfam μ (joinSets T P (N+1)) / ((N : ℝ) + 1)) atTop
      (𝓝 (hPart μ T P)) := by
    have h1 := hsub.tendsto_lim hbdd
    have h2 := h1.comp (tendsto_add_atTop_nat 1)
    rw [hPart_eq_lim μ hmp P hsub]
    refine h2.congr' ?_
    filter_upwards with N
    simp only [Function.comp_apply]
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hcast]
  -- (v) identify the two limits
  have hlim' : Tendsto (fun N : ℕ =>
      ((N : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (N+1), HcondFam X μ P.parts (JN T P k)) atTop
      (𝓝 (hPart μ T P)) := by
    refine hlim.congr' ?_
    filter_upwards with N
    rw [hsum (N+1), div_eq_inv_mul]
  exact tendsto_nhds_unique hlim' hces

end Work.EKLComp.Core
