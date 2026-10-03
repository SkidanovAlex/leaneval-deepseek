import Mathlib
import Submission.Work.BasinSC.defs
import Submission.Work.BasinSC.cover_basic

/-!
# The Riemann–Hurwitz-lite step: no critical point

If `p : V' → V` is proper and holomorphic with nowhere vanishing derivative on the connected plane
domain `V'` and the target `V` is simply connected, then `p` restricts to a covering map of `V`;
since a connected covering of a simply connected, locally path connected space is a homeomorphism,
`V'` is simply connected.
-/

open Set Metric Filter Topology

namespace Work.BasinSC

/-- **A proper holomorphic map without critical points onto a simply connected domain has simply
connected source.** -/
theorem simplyConnected_of_proper_holomorphic_no_crit
    {V V' : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty) (hVsc : SimplyConnectedSpace ↥V)
    (hV'o : IsOpen V') (hV'c : IsConnected V') {p : ℂ → ℂ} (hp : DifferentiableOn ℂ p V')
    (hmaps : Set.MapsTo p V' V)
    (hprop : ∀ K ⊆ V, IsCompact K → IsCompact (V' ∩ p ⁻¹' K))
    (hncrit : ∀ z ∈ V', deriv p z ≠ 0) :
    SimplyConnectedSpace ↥V' := by
  classical
  have hVne' : Nonempty ↥V := ⟨⟨hVne.choose, hVne.choose_spec⟩⟩
  have hV'ne : Nonempty ↥V' := ⟨⟨hV'c.nonempty.choose, hV'c.nonempty.choose_spec⟩⟩
  letI := hVne'
  let q : ↥V' → ↥V := fun z => ⟨p z, hmaps z.2⟩
  have hqcont : Continuous q := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    have hcomp : (Subtype.val ∘ q) = V'.domRestrict p := rfl
    rw [hcomp]
    exact hp.continuousOn.domRestrict
  have hqproper : IsProperMap q := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hqcont, fun K hK => ?_⟩
    have hK' : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
    have hK'V : Subtype.val '' K ⊆ V := by rintro y ⟨x, hxK, rfl⟩; exact x.2
    have h1 : IsCompact (V' ∩ p ⁻¹' (Subtype.val '' K)) := hprop _ hK'V hK'
    have h2 : q ⁻¹' K = Subtype.val ⁻¹' (V' ∩ p ⁻¹' (Subtype.val '' K)) := by
      ext z
      constructor
      · intro hz
        exact ⟨z.2, ⟨q z, hz, rfl⟩⟩
      · rintro ⟨_, hzp⟩
        obtain ⟨y, hyK, hyw⟩ := hzp
        have hzy : q z = y := Subtype.ext hyw.symm
        simpa [Set.mem_preimage, hzy] using hyK
    rw [h2]
    exact ((Topology.IsInducing.subtypeVal).isCompact_preimage_iff
      (by intro x hx; exact ⟨⟨x, hx.1⟩, rfl⟩)).2 h1
  have hqclosed : IsClosedMap q := hqproper.isClosedMap
  have hlocV : IsLocalHomeomorphOn (Subtype.val : ↥V → ℂ) Set.univ :=
    hVo.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
  have hlocV' : IsLocalHomeomorphOn (Subtype.val : ↥V' → ℂ) Set.univ :=
    hV'o.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
  have hlocp : IsLocalHomeomorphOn p V' := by
    refine IsLocalHomeomorphOn.mk p V' fun z hz => ?_
    have hana : AnalyticAt ℂ p z := hp.analyticAt (hV'o.mem_nhds hz)
    have hsf := (hana.hasStrictDerivAt).hasStrictFDerivAt_equiv (hncrit z hz)
    exact ⟨hsf.toOpenPartialHomeomorph, hsf.mem_toOpenPartialHomeomorph_source,
      fun w _ => rfl⟩
  have hloccomp : IsLocalHomeomorphOn (fun z : ↥V' => p z) Set.univ :=
    hlocp.comp hlocV' (by intro z _; exact z.2)
  have hloc : IsLocalHomeomorphOn q Set.univ := by
    refine IsLocalHomeomorphOn.of_comp_left (f := q) (g := (Subtype.val : ↥V → ℂ))
      (s := Set.univ) ?_ ?_ ?_
    · have h1 : (Subtype.val ∘ q) = fun z : ↥V' => p z := rfl
      rw [h1]; exact hloccomp
    · exact hlocV.mono (subset_univ _)
    · intro z _
      exact hqcont.continuousAt
  have hfin : ∀ v ∈ (Set.univ : Set ↥V), (q ⁻¹' {v}).Finite := by
    intro v _
    have hK : IsCompact (q ⁻¹' {v}) := hqproper.isCompact_preimage isCompact_singleton
    have hdisc : IsDiscrete (q ⁻¹' {v}) := by
      rw [isDiscrete_iff_forall_mem_exists_isOpen]
      intro z hz
      obtain ⟨e, hze, heq⟩ := hloc z (Set.mem_univ _)
      refine ⟨e.source, e.open_source, ?_⟩
      ext z'
      constructor
      · rintro ⟨hz'src, hz'fib⟩
        have h4 : e z' = e z := by
          rw [← congr_fun heq z', ← congr_fun heq z]
          rw [Set.mem_preimage, Set.mem_singleton_iff] at hz hz'fib
          rw [hz'fib, hz]
        exact e.injOn hz'src hze h4
      · rintro rfl
        exact ⟨hze, hz⟩
    exact hK.finite hdisc
  have hcovOn : IsCoveringMapOn q Set.univ :=
    IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn hqclosed hfin
      (by rwa [Set.preimage_univ])
  have hcov : IsCoveringMap q := isCoveringMap_iff_isCoveringMapOn_univ.mpr hcovOn
  haveI : LocallyPathConnectedSpace ↥V := hVo.locallyPathConnectedSpace
  haveI : LocallyPathConnectedSpace ↥V' := hV'o.locallyPathConnectedSpace
  haveI : ConnectedSpace ↥V' := isConnected_iff_connectedSpace.mp hV'c
  haveI : PathConnectedSpace ↥V' := PathConnectedSpace.of_locallyPathConnectedSpace
  exact simplyConnectedSpace_of_isCoveringMap hcov

end Work.BasinSC
