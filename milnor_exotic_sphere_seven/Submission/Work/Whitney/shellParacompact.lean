import Mathlib
import Submission.Work.Whitney.puncturedNorm
import Submission.Work.Whitney.chartNormDefs
import Submission.Work.Whitney.chartNormBound
import Submission.Work.LerayHirsch.paracompactSpace_projSpace

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.emptyLine false

/-!
# The dyadic norm shells in the punctured total space are paracompact

This module proves `Work.Whitney.shellParacompact`: for a real vector bundle `Z` over a paracompact
Hausdorff base, a partition of unity `φ` subordinate to the chart cover and a dyadic level `k`, the
shell `{2^k ≤ ν ≤ 2^(k+1)}` of the punctured total space (`ν = fibNorm Z φ`) is paracompact.

The proof adapts `Work.LerayHirsch.paracompactSpace_of_compact_fibres`: the projection of the shell
to the base has compact fibres (in the chart at `b` the fibre over `b` is the compact annulus
`shellSlice`), and satisfies the tube property (`exists_nhds_shell_subset`).  The compactness of the
slices and the tube property both rest on `Work.Whitney.chartNormBound`, the local lower bound for
the chartwise norm.  The result is then transferred from the flattened shell `shellSet` to the
subtype of the punctured total space by the homeomorphism `shellHomeo`.
-/

namespace Work.Whitney

open Bundle Work.TangentClasses Filter Set
open scoped Topology

noncomputable section

variable {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ι : Type} [Fintype ι]

/-- **The slice of the shell over a point of a chart is compact.** -/
theorem isCompact_shellSlice [ProperSpace F] (Z : VectorBundleCore ℝ B F ι)
    {φ : PartitionOfUnity ι B Set.univ}
    (hφ : φ.IsSubordinate Z.baseSet) (i : ι) {b : B} (hb : b ∈ Z.baseSet i) (k : ℤ) :
    IsCompact (shellSlice Z φ k i b) := by
  obtain ⟨W, hW, δ, hδpos, hδ⟩ := chartNormBound Z hφ i hb
  have hbW : b ∈ W := mem_of_mem_nhds hW
  have hcont : Continuous fun v : F => chartNorm Z φ i (b, v) :=
    (continuousOn_chartNorm Z φ i hφ).comp_continuous
      (continuous_const.prodMk continuous_id) fun v => ⟨hb, mem_univ v⟩
  have hclosed : IsClosed (shellSlice Z φ k i b) := by
    rw [shellSlice]
    exact isClosed_Icc.preimage hcont
  have hbound : shellSlice Z φ k i b ⊆ Metric.closedBall (0 : F) ((2:ℝ)^(k+1)/δ) := by
    intro v hv
    rw [mem_shellSlice] at hv
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, le_div_iff₀ hδpos, mul_comm]
    exact le_trans (hδ b hbW v) hv.2
  exact IsCompact.of_isClosed_subset
    (isCompact_closedBall (0 : F) ((2:ℝ)^(k+1)/δ)) hclosed hbound

/-- **The fibre of the shell over a point of the base is compact.** -/
theorem compactSpace_shellFibre [ProperSpace F] (Z : VectorBundleCore ℝ B F ι)
    {φ : PartitionOfUnity ι B Set.univ} (hφ : φ.IsSubordinate Z.baseSet) (k : ℤ) (b : B) :
    CompactSpace {p : ↥(shellSet Z φ k) // Z.proj (p.1 : Z.TotalSpace) = b} := by
  set i : ι := Z.indexAt b with hi
  have hb : b ∈ Z.baseSet i := Z.mem_baseSet_at b
  have hK : IsCompact (shellSlice Z φ k i b) := isCompact_shellSlice Z hφ i hb k
  haveI hKc : CompactSpace ↥(shellSlice Z φ k i b) := isCompact_iff_compactSpace.mp hK
  set G : F → Z.TotalSpace :=
    fun v => (Z.localTriv i).toOpenPartialHomeomorph.symm (b, v) with hG
  have hGcont : Continuous G := by
    rw [hG]
    refine (Z.localTriv i).continuousOn_invFun.comp_continuous
      (continuous_const.prodMk continuous_id) fun v => ?_
    rw [VectorBundleCore.mem_localTriv_target]
    simpa using hb
  have hGproj : ∀ v : F, Z.proj (G v) = b := fun v =>
    Bundle.Trivialization.proj_symm_apply' (Z.localTriv i) hb
  have hGnorm : ∀ v : F, chartNorm Z φ i (b, v) = fibNorm Z (fun j => φ j) (G v) :=
    fun v => chartNorm_eq_symm Z φ i (b, v)
  have hmem : ∀ v : ↥(shellSlice Z φ k i b), G (v : F) ∈ shellSet Z φ k := by
    intro v
    have hv1 : (2:ℝ)^k ≤ chartNorm Z φ i (b, (v:F)) := shellSlice_lower Z φ k i b (v:=((v:F))) v.2
    have hv2 : chartNorm Z φ i (b, (v:F)) ≤ (2:ℝ)^(k+1) := shellSlice_upper Z φ k i b (v:=((v:F))) v.2
    have hpos : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) k
    refine (mem_shellSet Z φ k (G (v:F))).mpr ⟨?_, ?_, ?_⟩
    · intro h0
      have h1 : fibNorm Z (fun j => φ j) (G (v:F)) = 0 :=
        fibNorm_eq_zero_of_snd_eq_zero Z φ h0
      rw [← hGnorm (v:F)] at h1
      linarith
    · rw [← hGnorm (v:F)]; exact hv1
    · rw [← hGnorm (v:F)]; exact hv2
  have hprojmem : ∀ v : ↥(shellSlice Z φ k i b),
      Z.proj ((⟨G (v:F), hmem v⟩ : ↥(shellSet Z φ k)) : Z.TotalSpace) = b :=
    fun v => hGproj (v:F)
  let Φ : ↥(shellSlice Z φ k i b) →
      {p : ↥(shellSet Z φ k) // Z.proj (p.1 : Z.TotalSpace) = b} :=
    fun v => ⟨⟨G (v:F), hmem v⟩, hprojmem v⟩
  have hΦcont : Continuous Φ :=
    Continuous.subtype_mk
      (Continuous.subtype_mk (hGcont.comp continuous_subtype_val) hmem) hprojmem
  have hsurj : Function.Surjective Φ := by
    rintro ⟨p, hq2⟩
    have hp1 : ((p : Z.TotalSpace)).1 = b := hq2
    have hpbase : ((p : Z.TotalSpace)).1 ∈ Z.baseSet i := by rw [hp1]; exact hb
    have hpsrc : (p : Z.TotalSpace) ∈ (Z.localTriv i).source := by
      rw [VectorBundleCore.mem_localTriv_source]; exact hpbase
    have hnormu : fibNorm Z (fun j => φ j) (p : Z.TotalSpace) ≤ (2:ℝ)^(k+1) :=
      shellSet_upper Z φ k p
    have hnorml : (2:ℝ)^k ≤ fibNorm Z (fun j => φ j) (p : Z.TotalSpace) :=
      shellSet_lower Z φ k p
    have hvmem : (Z.localTriv i (p : Z.TotalSpace)).2 ∈ shellSlice Z φ k i b := by
      rw [mem_shellSlice]
      have hcn := chartNorm_apply_localTriv Z φ i (p : Z.TotalSpace) hpbase
      rw [hp1] at hcn
      rw [hcn]
      exact ⟨hnorml, hnormu⟩
    refine ⟨⟨(Z.localTriv i (p : Z.TotalSpace)).2, hvmem⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show G ((Z.localTriv i (p : Z.TotalSpace)).2) = (p : Z.TotalSpace)
    have h1 : (b, (Z.localTriv i (p : Z.TotalSpace)).2) = Z.localTriv i (p : Z.TotalSpace) := by
      rw [← Bundle.Trivialization.mk_proj_snd (Z.localTriv i) hpsrc]
      refine Prod.ext ?_ rfl
      exact hq2.symm
    simp only [hG]
    rw [h1]
    exact Bundle.Trivialization.symm_apply_apply (Z.localTriv i) hpsrc
  have himg := (isCompact_univ (X := ↥(shellSlice Z φ k i b))).image hΦcont
  rw [Set.image_univ, Set.range_eq_univ.mpr hsurj] at himg
  exact isCompact_univ_iff.mp himg

/-- **The tube property of the shell.**  Every open set of the shell containing the whole fibre
over `b` contains a whole tube over a neighbourhood of `b`. -/
theorem exists_nhds_shell_subset [ProperSpace F] (Z : VectorBundleCore ℝ B F ι)
    {φ : PartitionOfUnity ι B Set.univ} (hφ : φ.IsSubordinate Z.baseSet) (k : ℤ) (b : B)
    (O : Set ↥(shellSet Z φ k)) (hO : IsOpen O)
    (hfib : {p : ↥(shellSet Z φ k) | Z.proj (p.1 : Z.TotalSpace) = b} ⊆ O) :
    ∃ W ∈ nhds b, ∀ p : ↥(shellSet Z φ k), Z.proj (p.1 : Z.TotalSpace) ∈ W → p ∈ O := by
  obtain ⟨W₁, hW₁, δ, hδpos, hδ⟩ := chartNormBound Z hφ (Z.indexAt b) (Z.mem_baseSet_at b)
  set i : ι := Z.indexAt b with hi
  have hb : b ∈ Z.baseSet i := Z.mem_baseSet_at b
  -- the open set of the total space corresponding to `O`
  obtain ⟨U, hUopen, hUeq⟩ := isOpen_induced_iff.mp hO
  -- every point of the shell over `b` lies in `U`
  have hfibU : ∀ p : Z.TotalSpace, p ∈ shellSet Z φ k → p.1 = b → p ∈ U := by
    intro p hp hpb
    have hmem : (⟨p, hp⟩ : ↥(shellSet Z φ k)) ∈ O :=
      hfib (by show Z.proj p = b; exact hpb)
    rwa [← hUeq] at hmem
  -- the compact slice and the tube lemma in the product `B × F`
  have hK : IsCompact (shellSlice Z φ k i b) := isCompact_shellSlice Z hφ i hb k
  set N : Set (B × F) :=
    (Z.baseSet i ×ˢ (univ : Set F)) ∩
      (fun y : B × F => (Z.localTriv i).toOpenPartialHomeomorph.symm y) ⁻¹' U with hN
  have hNmem : ∀ y : B × F, y ∈ N ↔ y.1 ∈ Z.baseSet i ∧
      (Z.localTriv i).toOpenPartialHomeomorph.symm y ∈ U := by
    intro y
    simp only [hN, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, Set.mem_preimage]
    tauto
  have hNopen : IsOpen N := by
    rw [hN]
    have hbase : (Z.localTriv i).baseSet = Z.baseSet i :=
      (VectorBundleCore.baseSet_at Z i).symm
    have htarget : (Z.localTriv i).target = Z.baseSet i ×ˢ (univ : Set F) := by
      rw [Bundle.Trivialization.target_eq, hbase]
    rw [← htarget]
    exact ContinuousOn.isOpen_inter_preimage (Z.localTriv i).continuousOn_invFun
      (Z.localTriv i).open_target hUopen
  have hchart_symm : ∀ v : F, fibNorm Z (fun j => φ j)
      ((Z.localTriv i).toOpenPartialHomeomorph.symm (b, v)) = chartNorm Z φ i (b, v) :=
    fun v => (chartNorm_eq_symm Z φ i (b, v)).symm
  have hsub : ({b} : Set B) ×ˢ shellSlice Z φ k i b ⊆ N := by
    rintro ⟨x, v⟩ ⟨hxb, hv⟩
    have hxb' : x = b := hxb
    rw [hxb']
    rw [hNmem]
    refine ⟨hb, ?_⟩
    refine hfibU _ ?_ (Bundle.Trivialization.proj_symm_apply' (Z.localTriv i) hb)
    have hv1 : (2:ℝ)^k ≤ chartNorm Z φ i (b, v) := shellSlice_lower Z φ k i b hv
    have hv2 : chartNorm Z φ i (b, v) ≤ (2:ℝ)^(k+1) := shellSlice_upper Z φ k i b hv
    refine (mem_shellSet Z φ k _).mpr ⟨?_, ?_, ?_⟩
    · intro h0
      have h1 : fibNorm Z (fun j => φ j)
          ((Z.localTriv i).toOpenPartialHomeomorph.symm (b, v)) = 0 :=
        fibNorm_eq_zero_of_snd_eq_zero Z φ h0
      rw [hchart_symm v] at h1
      have hpos : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) k
      linarith
    · rw [hchart_symm v]; exact hv1
    · rw [hchart_symm v]; exact hv2
  obtain ⟨u, U₀, huopen, hU₀open, hbu, hKU₀, huU₀N⟩ :=
    generalized_tube_lemma isCompact_singleton hK hNopen hsub
  -- the shell band and its complement
  set n' : Set (B × F) := (Z.baseSet i ×ˢ (univ : Set F)) ∩
      (chartNorm Z φ i) ⁻¹' (Set.Icc ((2:ℝ)^k) ((2:ℝ)^(k+1)))ᶜ with hn'
  have hn'mem : ∀ y : B × F, y ∈ n' ↔ y.1 ∈ Z.baseSet i ∧
      chartNorm Z φ i y ∉ Set.Icc ((2:ℝ)^k) ((2:ℝ)^(k+1)) := by
    intro y
    simp only [hn', Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, Set.mem_preimage,
      Set.mem_compl_iff]
    tauto
  have hn'open : IsOpen n' := by
    rw [hn']
    exact ContinuousOn.isOpen_inter_preimage (continuousOn_chartNorm Z φ i hφ)
      ((Z.isOpen_baseSet i).prod isOpen_univ) isClosed_Icc.isOpen_compl
  -- the set of far-away vectors outside `U₀`
  set R : ℝ := (2:ℝ)^(k+1)/δ with hR
  set C : Set F := Metric.closedBall (0 : F) R \ U₀ with hC
  have hCclosed : IsClosed C := by
    rw [hC]
    exact Metric.isClosed_closedBall.inter hU₀open.isClosed_compl
  have hCcompact : IsCompact C :=
    (isCompact_closedBall (0 : F) R).of_isClosed_subset hCclosed Set.sdiff_subset
  have hsub2 : ({b} : Set B) ×ˢ C ⊆ n' := by
    rintro ⟨x, v⟩ ⟨hxb, hv⟩
    have hxb' : x = b := hxb
    rw [hxb']
    rw [hn'mem]
    refine ⟨hb, ?_⟩
    intro hcon
    rw [Set.mem_Icc] at hcon
    exact hv.2 (hKU₀ ((mem_shellSlice Z φ k i b v).mpr hcon))
  obtain ⟨u₂, v₂, hu₂open, hv₂open, hbu₂, hCv₂, hu₂v₂⟩ :=
    generalized_tube_lemma isCompact_singleton hCcompact hn'open hsub2
  refine ⟨u ∩ u₂ ∩ W₁ ∩ Z.baseSet i, ?_, ?_⟩
  · refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem ?_ ?_) hW₁)
      ((Z.isOpen_baseSet i).mem_nhds hb)
    · exact huopen.mem_nhds (hbu rfl)
    · exact hu₂open.mem_nhds (hbu₂ rfl)
  · intro p hpW
    rw [Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_inter_iff] at hpW
    obtain ⟨⟨⟨hpu, hpu₂⟩, hpW₁⟩, hpbase⟩ := hpW
    have hqshell : (p : Z.TotalSpace) ∈ shellSet Z φ k := p.2
    have hql : (2:ℝ)^k ≤ fibNorm Z (fun j => φ j) (p : Z.TotalSpace) :=
      ((mem_shellSet Z φ k _).mp hqshell).2.1
    have hqu : fibNorm Z (fun j => φ j) (p : Z.TotalSpace) ≤ (2:ℝ)^(k+1) :=
      ((mem_shellSet Z φ k _).mp hqshell).2.2
    have hqbase : (p : Z.TotalSpace).1 ∈ Z.baseSet i := hpbase
    have hqsrc : (p : Z.TotalSpace) ∈ (Z.localTriv i).source := by
      rw [VectorBundleCore.mem_localTriv_source]; exact hqbase
    set v : F := (Z.localTriv i (p : Z.TotalSpace)).2 with hv
    have hcn : chartNorm Z φ i ((p : Z.TotalSpace).1, v) =
        fibNorm Z (fun j => φ j) (p : Z.TotalSpace) :=
      chartNorm_apply_localTriv Z φ i (p : Z.TotalSpace) hqbase
    have hbnd : δ * ‖v‖ ≤ (2:ℝ)^(k+1) := by
      have h := hδ (p : Z.TotalSpace).1 hpW₁ v
      rw [hcn] at h
      exact le_trans h hqu
    have hvball : v ∈ Metric.closedBall (0 : F) R := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, hR, le_div_iff₀ hδpos, mul_comm]
      exact hbnd
    have hvU₀ : v ∈ U₀ := by
      by_contra hvnot
      have hvC : v ∈ C := ⟨hvball, hvnot⟩
      have hmem : ((p : Z.TotalSpace).1, v) ∈ n' := hu₂v₂ ⟨hpu₂, hCv₂ hvC⟩
      have hcontra : chartNorm Z φ i ((p : Z.TotalSpace).1, v) ∉
          Set.Icc ((2:ℝ)^k) ((2:ℝ)^(k+1)) := ((hn'mem _).mp hmem).2
      rw [hcn] at hcontra
      exact hcontra (Set.mem_Icc.mpr ⟨hql, hqu⟩)
    have hqU : (p : Z.TotalSpace) ∈ U := by
      have hmem : ((p : Z.TotalSpace).1, v) ∈ N := huU₀N ⟨hpu, hvU₀⟩
      have hmemU : (Z.localTriv i).toOpenPartialHomeomorph.symm
          ((p : Z.TotalSpace).1, v) ∈ U := ((hNmem _).mp hmem).2
      have hsymm : (Z.localTriv i).toOpenPartialHomeomorph.symm
          ((p : Z.TotalSpace).1, v) = (p : Z.TotalSpace) := by
        rw [hv]
        exact Bundle.Trivialization.symm_apply_apply (Z.localTriv i) hqsrc
      rwa [hsymm] at hmemU
    rw [← hUeq]
    exact hqU

/-- **The shell of the punctured total space, flattened into the total space, is paracompact.** -/
theorem paracompactSpace_shellSet {B : Type} [TopologicalSpace B] [ParacompactSpace B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
    {ι : Type} [Fintype ι] (Z : VectorBundleCore ℝ B F ι)
    {φ : PartitionOfUnity ι B Set.univ} (hφ : φ.IsSubordinate Z.baseSet) (k : ℤ) :
    ParacompactSpace ↥(shellSet Z φ k) := by
  refine Work.LerayHirsch.paracompactSpace_of_compact_fibres
    ⟨fun p : ↥(shellSet Z φ k) => Z.proj (p.1 : Z.TotalSpace),
      Z.continuous_proj.comp continuous_subtype_val⟩ ?_ ?_
  · intro b
    exact compactSpace_shellFibre Z hφ k b
  · intro b O hO hbO
    exact exists_nhds_shell_subset Z hφ k b O hO hbO

/-- The canonical homeomorphism between the flattened shell and the shell inside the punctured
total space. -/
def shellHomeo (Z : VectorBundleCore ℝ B F ι) (φ : PartitionOfUnity ι B Set.univ) (k : ℤ) :
    {x : ↥(Work.Thom.zeroComplement Z) // (2 : ℝ) ^ k ≤ fibNorm Z (fun i => φ i) x.1 ∧
        fibNorm Z (fun i => φ i) x.1 ≤ (2 : ℝ) ^ (k + 1)} ≃ₜ ↥(shellSet Z φ k) where
  toFun x := ⟨(x.1 : Z.TotalSpace), ⟨x.1.2, x.2⟩⟩
  invFun p := ⟨⟨(p : Z.TotalSpace), p.2.1⟩, p.2.2⟩
  left_inv x := rfl
  right_inv p := rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) fun x => ⟨x.1.2, x.2⟩
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val fun p => p.2.1) fun p => p.2.2

/-- **The dyadic norm shells in the punctured total space are paracompact.**

Here `fibNorm Z φ` is the continuous strictly positive positively homogeneous fibrewise norm of
`Submission.Work.Whitney.puncturedNorm` (built from a partition of unity `φ` subordinate to the chart
cover), and the claim is that each dyadic shell is a paracompact subspace.

Route: adapt `Work.LerayHirsch.paracompactSpace_of_compact_fibres`.  The projection to the base has
compact fibres: the fibre over `b` is the annulus of the fibrewise norm over `b` with a strictly
positive lower bound, hence closed and bounded in `F`.  The tube property is proved in the chart
`Z.indexAt b`, where the fibre over `b` becomes `{b} × K` with `K` compact and the given open set
becomes open; compactness of `K` produces a product neighbourhood `W × U`, and shrinking `W` so that
every fibre over `x ∈ W` lies in `U` (fibrewise norms converge uniformly on compact sets, using the
continuity of the norm in the chart coordinates and homogeneity `fibNorm_smul`) gives a base
neighbourhood.  Do NOT use `Work.Whitney.puncturedParacompact` (still a sorry): that would be
circular. -/
theorem shellParacompact {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type} [Fintype ι] (Z : VectorBundleCore ℝ B F ι)
    {φ : PartitionOfUnity ι B Set.univ} (hφ : φ.IsSubordinate Z.baseSet) (k : ℤ) :
    ParacompactSpace {x : ↥(Work.Thom.zeroComplement Z) //
      (2 : ℝ) ^ k ≤ fibNorm Z (fun i => φ i) x.1 ∧
        fibNorm Z (fun i => φ i) x.1 ≤ (2 : ℝ) ^ (k + 1)} := by
  haveI : ParacompactSpace ↥(shellSet Z φ k) := paracompactSpace_shellSet Z hφ k
  exact (Homeomorph.paracompactSpace_iff (shellHomeo Z φ k)).mpr inferInstance

end

end Work.Whitney
