import Mathlib
import Submission.Work.Whitney.NowhereZeroDefs
import Submission.Work.Whitney.NowhereZeroChart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Work.TangentClasses Work.Thom
open scoped Topology

namespace Work.Whitney
namespace NZ

variable {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
  {ι : Type} [Fintype ι] {m : ℕ}
variable {V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι}
variable {σ : C(B, ↥(zeroComplement (realification V)))}

theorem sum_ofReal {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∑ a ∈ s, ((f a : ℝ) : ℂ)) = ((∑ a ∈ s, f a : ℝ) : ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; norm_num
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
      exact (map_add (algebraMap ℝ ℂ) _ _).symm

/-- The cover on which the `a.2`-th chart coordinate of the section is invertible. -/
def splitCover (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (σ : C(B, ↥(zeroComplement (realification V)))) (a : ι × Fin (m+1)) : Set B :=
  V.baseSet a.1 ∩ (fun b => (zCoord a.1 (σ b)) a.2) ⁻¹' {c : ℂ | c ≠ 0}

theorem isOpen_splitCover (hσ : IsSection σ) (a : ι × Fin (m+1)) : IsOpen (splitCover V σ a) := by
  have hcont : ContinuousOn (fun b : B => (zCoord a.1 (σ b)) a.2) (V.baseSet a.1) :=
    (evalCLM a.2).continuous.comp_continuousOn (continuousOn_zCoord_sec hσ a.1)
  have ht : IsOpen ({c : ℂ | c ≠ 0}) := by
    rw [show {c : ℂ | c ≠ 0} = {0}ᶜ from rfl]
    exact isClosed_singleton.isOpen_compl
  exact ContinuousOn.isOpen_inter_preimage hcont (V.isOpen_baseSet a.1) ht

theorem cover_splitCover (hσ : IsSection σ) :
    (Set.univ : Set B) ⊆ ⋃ a, splitCover V σ a := by
  intro b _
  refine Set.mem_iUnion.mpr ⟨(V.indexAt b, tqCoord V (σ b)), V.mem_baseSet_at b, ?_⟩
  show (zCoord (V.indexAt b) (σ b)) (tqCoord V (σ b)) ≠ 0
  rw [zCoord_secVec hσ b]
  exact secVec_secIdx_ne_zero hσ b

/-- The local splitting functional on the piece `a`: the `a.2`-th chart coordinate of `w`,
normalised by the `a.2`-th chart coordinate of the section. -/
noncomputable def localFun (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (σ : C(B, ↥(zeroComplement (realification V)))) (a : ι × Fin (m+1)) (b : B) :
    EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] ℂ :=
  ((zCoord a.1 (σ b)) a.2)⁻¹ • ((evalCLM a.2).comp (V.coordChange (V.indexAt b) a.1 b))

theorem localFun_secVec (hσ : IsSection σ) (a : ι × Fin (m+1)) (b : B)
    (hb : b ∈ splitCover V σ a) : localFun V σ a b (secVec V σ b) = 1 := by
  have hz : (V.coordChange (V.indexAt b) a.1 b) (secVec V σ b) = zCoord a.1 (σ b) :=
    (localTriv_secVec hσ a.1 b).symm
  simp only [localFun, smul_apply, ContinuousLinearMap.comp_apply, hz, smul_eq_mul]
  exact inv_mul_cancel₀ hb.2

/-- The chart expression of `localFun`, in a form whose continuity is manifest. -/
noncomputable def niceFun (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m+1))) ι)
    (σ : C(B, ↥(zeroComplement (realification V)))) (i : ι) (a : ι × Fin (m+1)) (b : B) :
    EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] ℂ :=
  ((zCoord a.1 (σ b)) a.2)⁻¹ • ((evalCLM a.2).comp (V.coordChange i a.1 b))

theorem localFun_comp_eq_niceFun (hσ : IsSection σ) (i : ι) (a : ι × Fin (m+1)) (b : B)
    (hb : b ∈ V.baseSet i ∩ splitCover V σ a) :
    (localFun V σ a b).comp (V.coordChange i (V.indexAt b) b) = niceFun V σ i a b := by
  have hb1 : b ∈ V.baseSet a.1 := hb.2.1
  have hcomp : (V.coordChange (V.indexAt b) a.1 b).comp (V.coordChange i (V.indexAt b) b)
      = V.coordChange i a.1 b := by
    refine ContinuousLinearMap.ext fun w => ?_
    rw [ContinuousLinearMap.comp_apply]
    exact V.coordChange_comp i (V.indexAt b) a.1 b
      ⟨⟨hb.1, V.mem_baseSet_at b⟩, hb1⟩ w
  simp only [localFun, niceFun, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_assoc,
    hcomp]

theorem continuousOn_niceFun (hσ : IsSection σ) (i : ι) (a : ι × Fin (m+1)) :
    ContinuousOn (fun b : B => niceFun V σ i a b) (V.baseSet i ∩ splitCover V σ a) := by
  have hsub1 : V.baseSet i ∩ splitCover V σ a ⊆ V.baseSet a.1 := fun b hb => hb.2.1
  have hscal : ContinuousOn (fun b : B => ((zCoord a.1 (σ b)) a.2)⁻¹)
      (V.baseSet i ∩ splitCover V σ a) := by
    refine ContinuousOn.inv₀ (((evalCLM a.2).continuous.comp_continuousOn
      (continuousOn_zCoord_sec hσ a.1)).mono hsub1) ?_
    intro b hb
    exact hb.2.2
  have hclm : ContinuousOn (fun b : B => (evalCLM a.2).comp (V.coordChange i a.1 b))
      (V.baseSet i ∩ splitCover V σ a) :=
    ContinuousOn.clm_comp continuousOn_const ((V.continuousOn_coordChange i a.1).mono
      (fun b hb => ⟨hb.1, hb.2.1⟩))
  exact hscal.smul hclm

section Existence

variable (ρ : PartitionOfUnity (ι × Fin (m+1)) B Set.univ)

theorem continuousOn_term (hσ : IsSection σ) (hρ : ρ.IsSubordinate (splitCover V σ))
    (i : ι) (a : ι × Fin (m+1)) :
    ContinuousOn (fun z : B => ρ a z • niceFun V σ i a z) (V.baseSet i) := by
  intro z hz
  by_cases hza : z ∈ splitCover V σ a
  · have hopen : IsOpen (V.baseSet i ∩ splitCover V σ a) :=
      (V.isOpen_baseSet i).inter (isOpen_splitCover hσ a)
    have hmem : z ∈ V.baseSet i ∩ splitCover V σ a := ⟨hz, hza⟩
    have hc1 : ContinuousAt (fun z : B => niceFun V σ i a z) z :=
      (continuousOn_niceFun hσ i a).continuousAt (hopen.mem_nhds hmem)
    have hc2 : ContinuousAt (fun z : B => ρ a z) z := (ρ a).continuous.continuousAt
    exact (hc2.smul hc1).continuousWithinAt
  · have hznot : z ∉ tsupport (⇑(ρ a)) := fun h => hza (hρ a h)
    have hopen : IsOpen (tsupport (⇑(ρ a)))ᶜ := isClosed_closure.isOpen_compl
    have heq : (fun _ : B => (0 : EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] ℂ)) =ᶠ[𝓝 z]
        fun z => ρ a z • niceFun V σ i a z := by
      filter_upwards [hopen.mem_nhds hznot] with c hc
      have h0 : ρ a c = 0 := by
        by_contra hc0
        exact hc (subset_closure (Function.mem_support.mpr hc0))
      rw [h0]
      exact (zero_smul ℝ (niceFun V σ i a c)).symm
    exact (continuousAt_const.congr heq).continuousWithinAt

theorem finsum_localFun_secVec (hσ : IsSection σ) (hρ : ρ.IsSubordinate (splitCover V σ))
    (b : B) :
    (∑ᶠ a, ρ a b • localFun V σ a b) (secVec V σ b) = 1 := by
  have step1 : (∑ᶠ a, ρ a b • localFun V σ a b) (secVec V σ b)
      = ∑ a : ι × Fin (m+1), ρ a b • (localFun V σ a b (secVec V σ b)) := by
    rw [finsum_eq_sum_of_support_subset (fun a => ρ a b • localFun V σ a b)
      (s := Finset.univ) (fun a _ => Finset.mem_univ a), _root_.sum_apply]
    exact Finset.sum_congr rfl (fun a _ => by rw [smul_apply])
  rw [step1]
  have step2 : ∀ a : ι × Fin (m+1),
      ρ a b • (localFun V σ a b (secVec V σ b)) = ((ρ a b : ℝ) : ℂ) := by
    intro a
    by_cases h : ρ a b = 0
    · rw [h, zero_smul]
      simp
    · rw [localFun_secVec hσ a b (hρ a (subset_closure (Function.mem_support.mpr h)))]
      simp
  rw [Finset.sum_congr rfl (fun a _ => step2 a)]
  rw [sum_ofReal Finset.univ (fun a => ρ a b)]
  rw [← finsum_eq_sum_of_support_subset (fun a => ρ a b) (s := Finset.univ)
    (fun a _ => Finset.mem_univ a)]
  rw [ρ.sum_eq_one (Set.mem_univ b)]
  norm_num

theorem continuousOn_finsum_localFun_comp (hσ : IsSection σ)
    (hρ : ρ.IsSubordinate (splitCover V σ)) (i : ι) :
    ContinuousOn (fun b => (∑ᶠ a, ρ a b • localFun V σ a b).comp
      (V.coordChange i (V.indexAt b) b)) (V.baseSet i) := by
  intro y hy
  obtain ⟨t, ht⟩ := ρ.exists_finset_nhds y
  have hsumcont : ContinuousOn (fun z : B => ∑ a ∈ t, ρ a z • niceFun V σ i a z)
      (V.baseSet i) :=
    continuousOn_finsetSum t (fun a _ => continuousOn_term ρ hσ hρ i a)
  have hF : ∀ z ∈ V.baseSet i, Function.support (fun a => ρ a z) ⊆ t →
      (∑ᶠ a, ρ a z • localFun V σ a z).comp (V.coordChange i (V.indexAt z) z)
        = ∑ a ∈ t, ρ a z • niceFun V σ i a z := by
    intro z hz hsupp
    refine ContinuousLinearMap.ext fun v => ?_
    have hterm : ∀ a ∈ t,
        (ρ a z • localFun V σ a z) ((V.coordChange i (V.indexAt z) z) v)
          = ρ a z • (niceFun V σ i a z v) := by
      intro a _
      rw [smul_apply]
      by_cases h0 : ρ a z = 0
      · rw [h0]
        simp
      · have hc : (localFun V σ a z) ((V.coordChange i (V.indexAt z) z) v)
            = (niceFun V σ i a z) v := by
          rw [show (localFun V σ a z) ((V.coordChange i (V.indexAt z) z) v)
              = ((localFun V σ a z).comp (V.coordChange i (V.indexAt z) z)) v from rfl,
            localFun_comp_eq_niceFun hσ i a z ⟨hz,
              hρ a (subset_closure (Function.mem_support.mpr h0))⟩]
        rw [hc]
    have hL : ((∑ᶠ a, ρ a z • localFun V σ a z).comp
          (V.coordChange i (V.indexAt z) z)) v
        = ∑ a ∈ t, ρ a z • (niceFun V σ i a z v) := by
      rw [ContinuousLinearMap.comp_apply, finsum_eq_sum_of_support_subset
        (fun a => ρ a z • localFun V σ a z)
        (s := Finset.univ) (fun a _ => Finset.mem_univ a), _root_.sum_apply]
      rw [← Finset.sum_subset (Finset.subset_univ t) (fun a _ ha => by
        have h0 : ρ a z = 0 := by
          by_contra hc
          exact ha (hsupp (Function.mem_support.mpr hc))
        simp [h0])]
      exact Finset.sum_congr rfl hterm
    have hR : ((∑ a ∈ t, ρ a z • niceFun V σ i a z) :
          EuclideanSpace ℂ (Fin (m+1)) →L[ℂ] ℂ) v
        = ∑ a ∈ t, ρ a z • (niceFun V σ i a z v) := by
      rw [_root_.sum_apply]
      exact Finset.sum_congr rfl (fun a _ => by rw [smul_apply])
    rw [hL, hR]
  have hev : (fun z => (∑ᶠ a, ρ a z • localFun V σ a z).comp (V.coordChange i (V.indexAt z) z))
      =ᶠ[𝓝[V.baseSet i] y] (fun z => ∑ a ∈ t, ρ a z • niceFun V σ i a z) := by
    filter_upwards [ht.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzs
    exact hF z hzs hz.2
  exact (hsumcont.continuousWithinAt hy).congr_of_eventuallyEq_of_mem hev hy

end Existence

theorem exists_splittingFunctional {B : Type} [TopologicalSpace B] [ParacompactSpace B]
    [T2Space B] {ι : Type} [Fintype ι] {m : ℕ}
    (V : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (m + 1))) ι)
    (σ : C(B, ↥(zeroComplement (realification V))))
    (hσ : IsSection σ) :
    ∃ ℓ : B → (EuclideanSpace ℂ (Fin (m + 1)) →L[ℂ] ℂ),
      (∀ b, ℓ b (secVec V σ b) = 1) ∧
      (∀ i : ι, ContinuousOn (fun b : B => (ℓ b).comp (V.coordChange i (V.indexAt b) b))
        (V.baseSet i)) := by
  classical
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate (s := Set.univ) isClosed_univ
    (splitCover V σ) (isOpen_splitCover hσ) (cover_splitCover hσ)
  exact ⟨fun b => ∑ᶠ a, ρ a b • localFun V σ a b,
    fun b => finsum_localFun_secVec ρ hσ hρ b,
    fun i => continuousOn_finsum_localFun_comp ρ hσ hρ i⟩

end NZ
end Work.Whitney
