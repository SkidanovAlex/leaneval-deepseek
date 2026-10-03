import Mathlib

namespace Work.Horn

/-- A proper local homeomorphism of a locally compact Hausdorff space is a covering map.

Indeed, properness makes `F` a closed map with compact fibers
(`isProperMap_iff_isCompact_preimage`); the local homeomorphism property makes every fiber
discrete, so a compact fiber is finite (`IsCompact.finite`).  Mathlib's
`IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn` then produces the even covering property.
(Note that Mathlib's `IsCoveringMap` does not require surjectivity, so no surjectivity of `F`
is needed.) -/
theorem isCoveringMap_of_isProperMap_of_isLocalHomeomorphOn {X : Type*} [TopologicalSpace X]
    [T2Space X] [LocallyCompactSpace X] {F : X → X}
    (hpre : ∀ K : Set X, IsCompact K → IsCompact (F ⁻¹' K))
    (hlo : IsLocalHomeomorphOn F Set.univ) : IsCoveringMap F := by
  -- A local homeomorphism is continuous, hence `F` is proper with compact fibres.
  have hcont : Continuous F :=
    continuous_iff_continuousAt.mpr fun x => hlo.continuousAt (Set.mem_univ x)
  have hproper : IsProperMap F :=
    (isProperMap_iff_isCompact_preimage (f := F)).2 ⟨hcont, fun K hK => hpre K hK⟩
  -- The fibres are compact (properness) and discrete (local homeomorphism), hence finite.
  have hfin : ∀ x ∈ (Set.univ : Set X), (F ⁻¹' {x}).Finite := by
    intro x _
    refine (hproper.isCompact_preimage isCompact_singleton).finite ?_
    refine IsDiscrete.of_openPartialHomeomorph F subset_rfl ?_
    intro e _
    obtain ⟨φ, hφ, hEq⟩ := hlo e (Set.mem_univ e)
    exact ⟨φ, hφ, hEq.symm⟩
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  exact IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn hproper.isClosedMap hfin hlo

theorem isCoveringMap_subtypeMap {f : ℂ → ℂ} {B : Set ℂ} (hB : IsOpen B) (hmap : Set.MapsTo f B B)
    (hprop : ∀ L ⊆ B, IsCompact L → IsCompact (B ∩ f ⁻¹' L))
    (hlo : IsLocalHomeomorphOn (fun x : B => (⟨f x.1, hmap x.2⟩ : B)) Set.univ) :
    IsCoveringMap (fun x : B => (⟨f x.1, hmap x.2⟩ : B)) := by
  have : LocallyCompactSpace B := hB.locallyCompactSpace
  refine isCoveringMap_of_isProperMap_of_isLocalHomeomorphOn ?_ hlo
  -- Translate the hypothesis `hprop` (compactness in `ℂ` of `B ∩ f ⁻¹' L`) into the statement
  -- that the map `F = Subtype.map f hmap` has compact preimages of compacta.
  intro K hK
  have hK' : IsCompact ((Subtype.val : B → ℂ) '' K) := Subtype.isCompact_iff.mp hK
  have hsub : ((Subtype.val : B → ℂ) '' K) ⊆ B := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hcomp := hprop _ hsub hK'
  have heq : (Subtype.val : B → ℂ) '' ((fun x : B => (⟨f x.1, hmap x.2⟩ : B)) ⁻¹' K)
      = B ∩ f ⁻¹' ((Subtype.val : B → ℂ) '' K) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, ⟨⟨f y.1, hmap y.2⟩, hy, rfl⟩⟩
    · rintro ⟨hzB, hz⟩
      obtain ⟨y, hyK, hyz⟩ := hz
      refine ⟨⟨z, hzB⟩, ?_, rfl⟩
      show (⟨f z, hmap hzB⟩ : B) ∈ K
      have h1 : (⟨f z, hmap hzB⟩ : B) = y := Subtype.ext hyz.symm
      rw [h1]
      exact hyK
  rw [Subtype.isCompact_iff, heq]
  exact hcomp

end Work.Horn
