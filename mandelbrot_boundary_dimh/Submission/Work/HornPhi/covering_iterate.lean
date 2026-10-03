import Mathlib
import Submission.Work.Interfaces.HornParts

namespace Work.HornPhi

open Set Topology

/-- **`f^N` is a covering map over a set on which it has no critical value.**

`B ⊆ ℂ` is open, `W ⊆ B` is open and contained in `B`, `f^N` is differentiable on `B`, has
nonvanishing derivative at every point of `B` mapping into `W`, and `B ∩ (f^N)⁻¹K` is compact for
every compact `K ⊆ B`.  Then `f^N : B → ℂ` is a covering map over `W`. -/
theorem covering_iterate {f : ℂ → ℂ} {B W : Set ℂ} {N : ℕ}
    (hB : IsOpen B) (hW : IsOpen W) (hWB : W ⊆ B)
    (hdiff : ∀ z ∈ B, DifferentiableAt ℂ (f^[N]) z)
    (hloc : ∀ z ∈ B, (f^[N]) z ∈ W → deriv (f^[N]) z ≠ 0)
    (hproper : ∀ L : Set ℂ, L ⊆ B → IsCompact L → IsCompact (B ∩ (f^[N]) ⁻¹' L)) :
    IsCoveringMapOn (fun z : {z : ℂ // z ∈ B} => (f^[N]) z) W := by
  classical
  let g : {z : ℂ // z ∈ B} → ℂ := fun z => (f^[N]) z
  have hcontg : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (hdiff z.1 z.2).continuousAt.comp continuous_subtype_val.continuousAt
  have hEopen : IsOpen (g ⁻¹' W) := hW.preimage hcontg
  -- local homeomorphism
  have hlocg : IsLocalHomeomorph (fun x : ↥(g ⁻¹' W) => g x.1) := by
    refine IsLocalHomeomorph.mk _ fun x => ?_
    have hzB : (x.1 : ℂ) ∈ B := x.1.2
    have hzW : (f^[N]) (x.1 : ℂ) ∈ W := x.2
    have hsd : HasStrictDerivAt (f^[N]) (deriv (f^[N]) (x.1 : ℂ)) (x.1 : ℂ) := by
      have hd : DifferentiableOn ℂ (f^[N]) B := fun w hw => (hdiff w hw).differentiableWithinAt
      exact (hd.analyticAt (hB.mem_nhds hzB)).hasStrictDerivAt
    have hne : deriv (f^[N]) (x.1 : ℂ) ≠ 0 := hloc _ hzB hzW
    let φ : OpenPartialHomeomorph ℂ ℂ := (hsd.hasStrictFDerivAt_equiv hne).toOpenPartialHomeomorph (f^[N])
    have hφsrc : (x.1 : ℂ) ∈ φ.source :=
      (hsd.hasStrictFDerivAt_equiv hne).mem_toOpenPartialHomeomorph_source
    let eB : OpenPartialHomeomorph {z : ℂ // z ∈ B} ℂ := φ.subtypeRestr (s := ⟨B, hB⟩) ⟨x.1⟩
    have hxB : x.1 ∈ eB.source := by
      rw [OpenPartialHomeomorph.subtypeRestr_source]; exact hφsrc
    have hxE : x ∈ (eB.subtypeRestr (s := ⟨g ⁻¹' W, hEopen⟩) ⟨x⟩).source := by
      rw [OpenPartialHomeomorph.subtypeRestr_source]; exact hxB
    refine ⟨eB.subtypeRestr (s := ⟨g ⁻¹' W, hEopen⟩) ⟨x⟩, hxE, ?_⟩
    intro y hy
    exact rfl
  -- continuity of the subtype-target map
  have hcontH : Continuous (Set.restrictPreimage W g) := by
    have h1 : Continuous (fun x : ↥(g ⁻¹' W) => g x.1) := hcontg.comp continuous_subtype_val
    have h2 : Continuous (fun x : ↥(g ⁻¹' W) => (⟨g x.1, x.2⟩ : ↥W)) :=
      Continuous.subtype_mk h1 (fun x => x.2)
    convert h2 using 1
    ext x
    exact rfl
  haveI : CompactlyCoherentSpace ↥W := by
    haveI : LocallyCompactSpace ↥W := hW.locallyCompactSpace
    infer_instance
  -- properness
  have hproperH : IsProperMap (Set.restrictPreimage W g) := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hcontH, ?_⟩
    intro K hK
    have hKc : IsCompact (Subtype.val '' K : Set ℂ) := hK.image continuous_subtype_val
    have hKcB : (Subtype.val '' K : Set ℂ) ⊆ B := by
      rintro y ⟨k, -, rfl⟩; exact hWB k.2
    have hcomp : IsCompact (B ∩ (f^[N]) ⁻¹' (Subtype.val '' K : Set ℂ)) := hproper _ hKcB hKc
    have heq : (Subtype.val '' (Subtype.val '' ((Set.restrictPreimage W g) ⁻¹' K)) : Set ℂ)
        = B ∩ (f^[N]) ⁻¹' (Subtype.val '' K : Set ℂ) := by
      ext y
      constructor
      · rintro ⟨z, ⟨w, hw, hwz⟩, hzy⟩
        refine ⟨hzy ▸ z.2, Set.restrictPreimage W g w, hw, ?_⟩
        show g (w : {z : ℂ // z ∈ B}) = (f^[N]) y
        rw [← hzy, ← hwz]
      · rintro ⟨hyB, ⟨k, hkK, hk⟩⟩
        have hmem : g ⟨y, hyB⟩ ∈ W := by
          show (f^[N]) y ∈ W
          rw [← hk]; exact k.2
        refine ⟨⟨y, hyB⟩, ⟨⟨⟨y, hyB⟩, hmem⟩, ?_, rfl⟩, rfl⟩
        have hx : Set.restrictPreimage W g ⟨⟨y, hyB⟩, hmem⟩ = k := by
          apply Subtype.ext
          show g ⟨y, hyB⟩ = (k : ℂ)
          rw [hk]
        show Set.restrictPreimage W g ⟨⟨y, hyB⟩, hmem⟩ ∈ K
        rw [hx]; exact hkK
    rw [Subtype.isCompact_iff, Subtype.isCompact_iff, heq]
    exact hcomp
  -- local homeomorphism of the subtype-target map
  have hlocH : IsLocalHomeomorph (Set.restrictPreimage W g) := by
    have hcomp : IsLocalHomeomorph ((fun y : ↥W => (y : ℂ)) ∘ Set.restrictPreimage W g) := by
      have heq2 : ((fun y : ↥W => (y : ℂ)) ∘ Set.restrictPreimage W g)
          = (fun x : ↥(g ⁻¹' W) => g x.1) := funext fun x => rfl
      rw [heq2]; exact hlocg
    have hJ : IsLocalHomeomorph (fun y : ↥W => (y : ℂ)) :=
      Topology.IsOpenEmbedding.isLocalHomeomorph (hW.isOpenEmbedding_subtypeVal)
    exact IsLocalHomeomorph.of_comp hcomp hJ hcontH
  have hCover : IsCoveringMap (Set.restrictPreimage W g) := by
    rw [isCoveringMap_iff_isCoveringMapOn_univ]
    refine IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn hproperH.isClosedMap ?_ ?_
    · intro y hy
      have hcp : IsCompact ((Set.restrictPreimage W g) ⁻¹' {y}) :=
        hproperH.isCompact_preimage isCompact_singleton
      have hsub : ((Set.restrictPreimage W g) '' ((Set.restrictPreimage W g) ⁻¹' {y})).Subsingleton
          := by
        rintro a ⟨u, hu, rfl⟩ b ⟨v, hv, rfl⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hu hv
        rw [hu, hv]
      haveI : Subsingleton ↥((Set.restrictPreimage W g) '' ((Set.restrictPreimage W g) ⁻¹' {y})) :=
        Set.Subsingleton.coe_sort hsub
      have hdisc : DiscreteTopology ↥((Set.restrictPreimage W g) ⁻¹' {y}) :=
        IsLocalHomeomorphOn.discreteTopology_of_image hlocH.isLocalHomeomorphOn
      exact hcp.finite DiscreteTopology.isDiscrete
    · have h1 : IsLocalHomeomorphOn (Set.restrictPreimage W g) Set.univ :=
        (isLocalHomeomorph_iff_isLocalHomeomorphOn_univ (f := Set.restrictPreimage W g)).mp hlocH
      simpa [Set.preimage_univ] using h1
  exact IsCoveringMapOn.of_isCoveringMap_restrictPreimage W hW hEopen hCover

end Work.HornPhi
