import Mathlib
import Submission.Work.Thom.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Whitney

open Bundle Work.TangentClasses

open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type}

/-! ## A fibrewise norm on the total space of a real bundle

The gluing-data model `RealBundle B F ι = VectorBundleCore ℝ B F ι` fixes no metric on the fibres.
To run the "radial" argument (clamping the fibre coordinate towards a shell) we need *some*
continuous fibrewise norm.  Over a paracompact base one exists: glue the chartwise norms with a
partition of unity subordinate to the (finite) chart cover.

The key point that makes the continuity proof work is that the partition of unity is subordinate to
the chart cover, i.e. `tsupport (φ i) ⊆ Z.baseSet i`: outside the support of `φ i` the chart `i` is
not used at all, and the "junk" values of Mathlib's `localTriv i` (which is defined via `indexAt`
and only continuous on its source) are killed by the factor `φ i`. -/

/-- The fibrewise norm on the total space of `Z` obtained from a family of functions `φ i` on the
base: the sum of the chartwise norms weighted by the `φ i`. -/
def fibNorm [Fintype ι] (Z : VectorBundleCore ℝ B F ι) (φ : ι → C(B, ℝ))
    (p : Z.TotalSpace) : ℝ :=
  ∑ i, φ i p.1 * ‖(Z.localTriv i p).2‖

/-- The `i`-th chartwise norm term is continuous as soon as the weight `φ i` is supported in the
chart `Z.baseSet i`. -/
theorem continuous_fibTerm (Z : VectorBundleCore ℝ B F ι) (φ : ι → C(B, ℝ))
    (hφ : ∀ i, tsupport (φ i) ⊆ Z.baseSet i) (i : ι) :
    Continuous (fun p : Z.TotalSpace => φ i p.1 * ‖(Z.localTriv i p).2‖) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  by_cases h : p₀.1 ∈ Z.baseSet i
  · have hsrc : p₀ ∈ (Z.localTriv i).source := by
      rw [VectorBundleCore.mem_localTriv_source]; exact h
    have hcont : ContinuousOn (fun p : Z.TotalSpace => φ i p.1 * ‖(Z.localTriv i p).2‖)
        (Z.localTriv i).source := by
      refine ContinuousOn.mul ?_ ?_
      · exact ((φ i).continuous.comp Z.continuous_proj).continuousOn
      · have : ContinuousOn (fun p : Z.TotalSpace => (Z.localTriv i p).2)
            (Z.localTriv i).source :=
          continuous_snd.comp_continuousOn (Z.localTriv i).continuousOn_toFun
        simpa using this.norm
    exact hcont.continuousAt ((Z.localTriv i).open_source.mem_nhds hsrc)
  · have hcl : p₀.1 ∉ tsupport (φ i) := fun hx => h (hφ i hx)
    have hU : Z.proj ⁻¹' (tsupport (φ i))ᶜ ∈ 𝓝 p₀ :=
      ((isClosed_tsupport (φ i)).isOpen_compl.preimage Z.continuous_proj).mem_nhds hcl
    refine (((continuous_const : Continuous fun _ : Z.TotalSpace => (0 : ℝ)).continuousAt)).congr_of_eventuallyEq ?_
    filter_upwards [hU] with p hp
    have hzero : φ i p.1 = 0 :=
      Function.support_subset_iff'.mp subset_closure p.1 hp
    simp [hzero]

/-- **The fibrewise norm is continuous** (for a partition of unity subordinate to the chart
cover). -/
theorem continuous_fibNorm [Fintype ι] (Z : VectorBundleCore ℝ B F ι) (φ : ι → C(B, ℝ))
    (hφ : ∀ i, tsupport (φ i) ⊆ Z.baseSet i) : Continuous (fibNorm Z φ) := by
  change Continuous fun p : Z.TotalSpace => ∑ i, φ i p.1 * ‖(Z.localTriv i p).2‖
  exact continuous_finsetSum _ fun i _ => continuous_fibTerm Z φ hφ i

/-- The chartwise norm of the `i`-th chart is strictly positive on the punctured total space,
whenever the weight is. -/
theorem coordChange_eq_zero_iff (Z : VectorBundleCore ℝ B F ι) {x : B} {i : ι}
    (hx : x ∈ Z.baseSet i) (v : F) :
    (Z.coordChange (Z.indexAt x) i x) v = 0 ↔ v = 0 := by
  have hx1 : x ∈ Z.baseSet (Z.indexAt x) := Z.mem_baseSet_at x
  have hx' : x ∈ Z.baseSet (Z.indexAt x) ∩ Z.baseSet i ∩ Z.baseSet (Z.indexAt x) :=
    ⟨⟨hx1, hx⟩, hx1⟩
  constructor
  · intro hv
    have h := Z.coordChange_comp (Z.indexAt x) i (Z.indexAt x) x hx' v
    rw [hv, map_zero] at h
    rw [Z.coordChange_self (Z.indexAt x) x hx1 v] at h
    exact h.symm
  · intro hv
    rw [hv, map_zero]

theorem coordChange_injective_of_mem (Z : VectorBundleCore ℝ B F ι) {x : B} {i : ι}
    (hx : x ∈ Z.baseSet i) : Function.Injective (Z.coordChange (Z.indexAt x) i x) := by
  intro v w hvw
  have hzero : (Z.coordChange (Z.indexAt x) i x) (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have h := (coordChange_eq_zero_iff Z hx (v - w)).mp hzero
  exact sub_eq_zero.mp h

/-- The second component of the `i`-th chart trivialization of `p` is the `i`-chart coordinate of
its fibre vector. -/
theorem fibNorm_aux (Z : VectorBundleCore ℝ B F ι) (i : ι) (p : Z.TotalSpace) :
    (Z.localTriv i p).2 = (Z.coordChange (Z.indexAt p.1) i p.1) p.2 := by
  simpa using congrArg Prod.snd (VectorBundleCore.localTriv_apply Z (i := i) p)

/-- **Positivity** of the fibrewise norm on the punctured total space. -/
theorem fibNorm_pos [Fintype ι] (Z : VectorBundleCore ℝ B F ι)
    {φ : PartitionOfUnity ι B Set.univ} (hφ : φ.IsSubordinate Z.baseSet) (p : Z.TotalSpace)
    (hp : p ∈ Work.Thom.zeroComplement Z) : 0 < fibNorm Z (fun i => φ i) p := by
  rw [Work.Thom.mem_zeroComplement] at hp
  have hsum : (∑ i, φ i p.1) = 1 := by
    rw [← finsum_eq_sum_of_fintype]
    exact φ.sum_eq_one (Set.mem_univ p.1)
  have hne : ∃ i, 0 < φ i p.1 := by
    by_contra hcon
    simp only [not_exists, not_lt] at hcon
    have hzero : (∑ i, φ i p.1) = 0 :=
      Finset.sum_eq_zero fun i _ => le_antisymm (hcon i) (φ.nonneg i p.1)
    rw [hsum] at hzero
    exact one_ne_zero hzero
  obtain ⟨i, hi⟩ := hne
  have hsupp : p.1 ∈ Function.support (φ i) := Function.mem_support.mpr (ne_of_gt hi)
  have hmem : p.1 ∈ Z.baseSet i := hφ i (subset_closure hsupp)
  have hpos : 0 < φ i p.1 * ‖(Z.localTriv i p).2‖ := by
    refine mul_pos hi (norm_pos_iff.mpr ?_)
    intro hzero
    have h2 : (Z.localTriv i p).2 = (Z.coordChange (Z.indexAt p.1) i p.1) p.2 :=
      fibNorm_aux Z i p
    rw [h2] at hzero
    exact hp ((coordChange_eq_zero_iff Z hmem p.2).mp hzero)
  rw [fibNorm]
  exact Finset.sum_pos' (fun i _ => mul_nonneg (φ.nonneg i p.1) (norm_nonneg _))
    ⟨i, Finset.mem_univ i, hpos⟩

/-- **Positive homogeneity** of the fibrewise norm. -/
theorem fibNorm_smul [Fintype ι] (Z : VectorBundleCore ℝ B F ι) (φ : ι → C(B, ℝ)) (x : B)
    {c : ℝ} (hc : 0 ≤ c) (v : F) :
    fibNorm Z φ (⟨x, c • v⟩ : Z.TotalSpace) = c * fibNorm Z φ (⟨x, v⟩ : Z.TotalSpace) := by
  rw [fibNorm, fibNorm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fibNorm_aux Z i (⟨x, c • v⟩ : Z.TotalSpace), fibNorm_aux Z i (⟨x, v⟩ : Z.TotalSpace), map_smul,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  ring

/-- **A partition of unity subordinate to the chart cover of a real bundle.** -/
theorem exists_partitionOfUnity_subordinate [Fintype ι] [ParacompactSpace B] [T2Space B]
    (Z : VectorBundleCore ℝ B F ι) :
    ∃ φ : PartitionOfUnity ι B Set.univ, φ.IsSubordinate Z.baseSet := by
  haveI : NormalSpace B := NormalSpace.of_paracompactSpace_r1Space
  obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate (s := Set.univ) isClosed_univ
    Z.baseSet (fun i => Z.isOpen_baseSet i)
    (by rintro x -; exact Set.mem_iUnion.mpr ⟨Z.indexAt x, Z.mem_baseSet_at x⟩)
  exact ⟨φ, hφ⟩

end

end Work.Whitney
