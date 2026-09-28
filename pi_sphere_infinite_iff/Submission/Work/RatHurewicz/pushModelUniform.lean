import Mathlib
import Submission.Work.RatHurewicz.skelPushDefs
import Submission.Work.RatHurewicz.pushDefs
import Submission.Work.RatHurewicz.pushMap
import Submission.Work.RatHurewicz.pushModel
import Submission.Work.RatHurewicz.cellFacts
import Submission.Work.RatHurewicz.cellShape
import Submission.Work.RatHurewicz.isClosed_rawWeight_le
import Submission.Work.RatHurewicz.uniformFaceDefs

/-!
# The uniform push of the `k`-cells of the model, on its domain of continuity

This module proves `Work.RatHurewicz.pushModelUniform`: the uniform (cell-independent) push of the
`k`-skeleton off its `k`-cells, descended to the model and restricted to the `k`-skeleton with the
images of the centroids of its `(k+1)`-faces removed, is continuous, is the identity on the
`(k-1)`-skeleton, and lands in the `(k-1)`-skeleton at time `1`.

The proof has two halves.

* *The raw push is continuous on the raw push domain* (`continuous_pushRaw_domain`).  The raw push
  is the identity off the open `(k+1)`-cells and, on such a cell, pushes radially away from the
  centroid of the cell.  The raw push domain is covered by finitely many closed pieces — the arcs,
  and the closed faces spanned by the `(k+1)`-element vertex sets in each copy — and on each pushPiece
  the push is given by the *fixed-face* formula `SkelPush.facePt` of
  `Submission/Work/RatHurewicz/uniformFaceDefs.lean`, which is continuous wherever its denominator
  `SkelPush.faceDen` does not vanish; the remaining points are exactly the images of the centroids,
  which are excluded from the domain.

* *The descent to the model* (`isQuotientMap_pushDomain`, then the target theorem).  The
  restriction `qY` of `Quotient.mk''` to the push domain is a quotient map: it is the restriction of
  the quotient map `{a | rawWeight D a ≤ k+1} → skel D k` (a closed saturated subset of `Raw D`,
  for which the restriction of a quotient map is a quotient map again) to the preimage of the *open*
  subset `pushDomainModel D k ⊆ skel D k`.  The latter is open because it is the complement of the
  finite set `isCentroidModel D k`: the preimage of a centroid is a finite set of centroids, since
  the shape of a raw point is invariant under the gluing relation and determines the point on a
  fixed support in a fixed copy (`finite_preimage_isCentroidModel`).  The descended homotopy is then
  obtained from `Topology.IsQuotientMap.continuous_lift_prod_right`.
-/

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

theorem suppOf_centroidPt (S : Finset (Fin (n + 2))) (hS : S.Nonempty) :
    suppOf (centroidPt S hS) = S := by
  ext k
  rw [mem_suppOf, centroidPt_apply]
  constructor
  · intro h
    by_contra hk
    rw [if_neg hk] at h
    exact h rfl
  · intro hk
    rw [if_pos hk]
    have hpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
    positivity

theorem shapeOf_centroidPt_snd (S : Finset (Fin (n + 2))) (hS : S.Nonempty) {r : ℕ} {v : ℝ}
    (h : (r, v) ∈ shapeOf (centroidPt S hS)) : v = ((S.card : ℝ))⁻¹ := by
  rw [shapeOf, Finset.mem_image] at h
  obtain ⟨k, hk, hkv⟩ := h
  have h2 : (centroidPt S hS : Fin (n + 2) → ℝ) k = ((S.card : ℝ))⁻¹ := by
    rw [centroidPt_apply, if_pos (by rwa [suppOf_centroidPt S hS] at hk)]
  have hkv' : (centroidPt S hS : Fin (n + 2) → ℝ) k = v := congrArg Prod.snd hkv
  rw [← hkv']
  exact h2

theorem one_ne_inv_card_of_two_le (S : Finset (Fin (n + 2))) (hS : S.Nonempty)
    (h2 : 2 ≤ S.card) : ((S.card : ℝ))⁻¹ ≠ 1 := by
  intro h
  have hpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have h1 : (S.card : ℝ) = 1 := by
    rw [← inv_inv (S.card : ℝ), h, inv_one]
  have : S.card = 1 := by exact_mod_cast h1
  omega

theorem shapeOf_centroidPt_ne_singleton (S : Finset (Fin (n + 2))) (hS : S.Nonempty)
    (h2 : 2 ≤ S.card) : shapeOf (centroidPt S hS) ≠ {(0, 1)} := by
  intro h
  have hmem : (0, 1) ∈ shapeOf (centroidPt S hS) := by
    rw [h]; exact Finset.mem_singleton_self _
  exact one_ne_inv_card_of_two_le S hS h2 (shapeOf_centroidPt_snd S hS hmem).symm

/-! ## The class of a centroid point is contained in the finite set of centroids -/

/-- The finitely many centroid points of the `(k+1)`-faces of the model, as points of `Raw D`. -/
def centroidMap (D : MData X n x₀) (k : ℕ) :
    (Σ _ : D.Idx, {T : Finset (Fin (n + 2)) // T.card = k + 1}) → Raw D :=
  fun p => Sum.inl ⟨p.1, centroidPt p.2.1
    (Finset.card_pos.mp (by rw [p.2.2]; omega))⟩

theorem centroidMap_apply (D : MData X n x₀) (k : ℕ)
    (p : Σ _ : D.Idx, {T : Finset (Fin (n + 2)) // T.card = k + 1}) :
    centroidMap D k p = Sum.inl ⟨p.1, centroidPt p.2.1
      (Finset.card_pos.mp (by rw [p.2.2]; omega))⟩ := rfl

theorem finite_range_centroidMap (D : MData X n x₀) (k : ℕ) :
    (Set.range (centroidMap D k)).Finite := by
  haveI : Finite (Σ _ : D.Idx, {T : Finset (Fin (n + 2)) // T.card = k + 1}) := inferInstance
  rw [← Set.image_univ]
  exact Set.finite_univ.image (centroidMap D k)

theorem centroidPt_congr (S : Finset (Fin (n + 2))) (hS hS' : S.Nonempty) :
    centroidPt S hS = centroidPt S hS' :=
  Subtype.ext rfl

/-- **The preimage of the set of centroids of the `(k+1)`-faces is finite.** -/
theorem finite_preimage_isCentroidModel (D : MData X n x₀) (k : ℕ) (hk : 2 ≤ k) :
    (Quotient.mk'' ⁻¹' Set.ofPred (fun z : Model D => SkelPush.isCentroidModel D k z)).Finite := by
  classical
  refine (finite_range_centroidMap D k).subset ?_
  intro a ha
  obtain ⟨i, S, hS, hcard, haS⟩ := ha
  have hrel : Relation.EqvGen (modelRel D) a
      (Sum.inl (⟨i, centroidPt S hS⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))) := by
    apply Quotient.exact (s := Relation.EqvGen.setoid (modelRel D))
    show Quotient.mk'' a = Quotient.mk'' (Sum.inl (⟨i, centroidPt S hS⟩ :
      Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2))))
    rw [haS]
    rfl
  have hshape := shapeAt_eqvGen D hrel
  have hwt : rawWeight D a = k + 1 := by
    have h2 := SkelPush.rawWeight_eqvGen' hrel
    rw [h2, rawWeight_inl]
    have h3 : ptSupport (centroidPt S hS) = S := by
      rw [← suppOf_eq_ptSupport]
      exact suppOf_centroidPt S hS
    rw [h3, hcard]
  rcases a with ⟨j, x⟩ | ⟨j, t⟩
  · have hshape' : shapeOf x = shapeOf (centroidPt S hS) := by
      simpa using hshape
    have hcardx : (ptSupport x).card = k + 1 := by
      have h3 := hwt
      rw [rawWeight_inl] at h3
      exact h3
    have hval : ∀ i ∈ ptSupport x, (x : Fin (n + 2) → ℝ) i = ((k : ℝ) + 1)⁻¹ := by
      intro i hi
      have hmem : (rankIn (ptSupport x) i, (x : Fin (n + 2) → ℝ) i)
          ∈ shapeOf (centroidPt S hS) := by
        rw [← hshape']
        refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
        rwa [suppOf_eq_ptSupport]
      have h1 := shapeOf_centroidPt_snd S hS hmem
      rw [h1, hcard]
      push_cast
      ring
    have hne : (ptSupport x).Nonempty := Finset.card_pos.mp (by rw [hcardx]; omega)
    have hfun : (x : Fin (n + 2) → ℝ)
        = ((centroidPt (ptSupport x) hne : stdSimplex ℝ (Fin (n + 2))) :
            Fin (n + 2) → ℝ) := by
      funext i
      by_cases hi : i ∈ ptSupport x
      · rw [centroidPt_apply_mem hne hi]
        rw [hval i hi, hcardx]
        push_cast
        ring
      · rw [centroidPt_apply_notMem hne hi]
        exact (by simpa [mem_ptSupport] using hi : (x : Fin (n + 2) → ℝ) i = 0)
    have hx : x = centroidPt (ptSupport x) hne := Subtype.ext hfun
    refine ⟨⟨j, ⟨ptSupport x, hcardx⟩⟩, ?_⟩
    rw [centroidMap_apply]
    refine congrArg Sum.inl ?_
    refine congrArg (fun y => (⟨j, y⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))) ?_
    exact (centroidPt_congr (ptSupport x) _ hne).trans hx.symm
  · exfalso
    have hsing : shapeOf (centroidPt S hS) = {(0, 1)} := by
      simpa using hshape.symm
    exact shapeOf_centroidPt_ne_singleton S hS (by omega) hsing


theorem isQuotientMap_skel (D : MData X n x₀) (k : ℕ) :
    Topology.IsQuotientMap (fun a : {a : Raw D // rawWeight D a ≤ k + 1} =>
      (⟨Quotient.mk'' a.1, (SkelPush.mem_skel_mk D k a.1).mpr a.2⟩ :
        {z : Model D // z ∈ skel D k})) := by
  classical
  have hf : Topology.IsQuotientMap (Quotient.mk'' : Raw D → Model D) := isQuotientMap_quotient_mk'
  have hqcont : Continuous (fun a : {a : Raw D // rawWeight D a ≤ k + 1} =>
      (⟨Quotient.mk'' a.1, (SkelPush.mem_skel_mk D k a.1).mpr a.2⟩ :
        {z : Model D // z ∈ skel D k})) :=
    (hf.continuous.comp continuous_subtype_val).subtype_mk _
  have hAclosed : IsClosed (setOf fun a : Raw D => rawWeight D a ≤ k + 1) := by
    have h := isClosed_rawWeight_le D (k + 1)
    rwa [show setOf (fun a : Raw D => rawWeight D a ≤ k + 1) = rawWeight D ⁻¹' Set.Iic (k + 1)
      from rfl]
  refine ⟨?_, ?_⟩
  · refine Topology.IsCoinducing.of_isClosed_preimage_iff_isClosed ?_
    intro s
    constructor
    · intro hs
      set S : Set (Model D) := Subtype.val '' s with hSdef
      have hseq : s = Subtype.val ⁻¹' S := by
        ext w
        constructor
        · intro hw; exact ⟨w, hw, rfl⟩
        · rintro ⟨w', hw', hww'⟩
          have : w' = w := Subtype.ext hww'
          rwa [this] at hw'
      have hs' : IsClosed ((Subtype.val : {a : Raw D // rawWeight D a ≤ k + 1} → Raw D) ⁻¹'
          (Quotient.mk'' ⁻¹' S)) := by
        have h1 : (fun a : {a : Raw D // rawWeight D a ≤ k + 1} =>
              (⟨Quotient.mk'' a.1, (SkelPush.mem_skel_mk D k a.1).mpr a.2⟩ :
                {z : Model D // z ∈ skel D k})) ⁻¹' s
            = (Subtype.val : {a : Raw D // rawWeight D a ≤ k + 1} → Raw D) ⁻¹'
                (Quotient.mk'' ⁻¹' S) := by
          rw [hseq]
          rfl
        rw [← h1]
        exact hs
      obtain ⟨K, hK, hKeq⟩ := isClosed_induced_iff.mp hs'
      have himage : Quotient.mk'' ⁻¹' S
          = K ∩ setOf (fun a : Raw D => rawWeight D a ≤ k + 1) := by
        ext a
        constructor
        · intro ha
          have hwt : rawWeight D a ≤ k + 1 := (SkelPush.mem_skel_mk D k a).mp (by
            obtain ⟨w, hw, hwa⟩ := ha
            rw [← hwa]
            exact w.2)
          exact ⟨(Set.ext_iff.mp hKeq ⟨a, hwt⟩).mpr ha, hwt⟩
        · rintro ⟨haK, hwt⟩
          exact (Set.ext_iff.mp hKeq ⟨a, hwt⟩).mp haK
      have hSclosed : IsClosed S := by
        rw [← hf.isCoinducing.isClosed_preimage]
        rw [himage]
        exact hK.inter hAclosed
      rw [hseq]
      exact IsClosed.preimage continuous_subtype_val hSclosed
    · intro hs
      exact IsClosed.preimage hqcont hs
  · intro z
    obtain ⟨a, ha, hw⟩ := (mem_skel_iff (D := D)).mp z.2
    exact ⟨⟨a, hw⟩, Subtype.ext ha⟩

/-- **The push domain of the model is a quotient of its preimage in the raw space.**
The map is the restriction of `Quotient.mk''`, and it is the composite of the quotient map on the
weight-`≤ k+1` part with the restriction to the open subset `pushDomainModel D k`. -/
theorem isQuotientMap_pushDomain (D : MData X n x₀) (k : ℕ) (hk : 2 ≤ k) :
    Topology.IsQuotientMap (fun a : {a : Raw D // SkelPush.pushDomain D k a} =>
      (⟨Quotient.mk'' a.1, a.2⟩ : {z : Model D // SkelPush.pushDomainModel D k z})) := by
  classical
  have hf : Topology.IsQuotientMap (Quotient.mk'' : Raw D → Model D) := isQuotientMap_quotient_mk'
  have hq₁ := isQuotientMap_skel D k
  have hqcont : Continuous (fun a : {a : Raw D // SkelPush.pushDomain D k a} =>
      (⟨Quotient.mk'' a.1, a.2⟩ : {z : Model D // SkelPush.pushDomainModel D k z})) :=
    (hf.continuous.comp continuous_subtype_val).subtype_mk _
  have hKclosed : IsClosed
      (Quotient.mk'' ⁻¹' setOf (fun z : Model D => SkelPush.isCentroidModel D k z)) :=
    (finite_preimage_isCentroidModel D k hk).isClosed
  have hYA : setOf (fun a : Raw D => SkelPush.pushDomain D k a)
      = setOf (fun a : Raw D => rawWeight D a ≤ k + 1) ∩
        (Quotient.mk'' ⁻¹' setOf (fun z : Model D => SkelPush.isCentroidModel D k z))ᶜ := by
    ext a
    change SkelPush.pushDomain D k a ↔
      (rawWeight D a ≤ k + 1 ∧ ¬ SkelPush.isCentroidModel D k (Quotient.mk'' a))
    exact SkelPush.pushDomain_iff D k a
  refine ⟨?_, ?_⟩
  · refine Topology.IsCoinducing.of_isOpen_preimage_iff_isOpen ?_
    intro s
    constructor
    · intro hs
      set S : Set (Model D) := Subtype.val '' s with hSdef
      obtain ⟨V, hVopen, hVeq⟩ := isOpen_induced_iff.mp hs
      -- the raw preimage of `S` inside the model is `Y ∩ V`
      have hmain : Quotient.mk'' ⁻¹' S
          = setOf (fun a : Raw D => SkelPush.pushDomain D k a) ∩ V := by
        ext a
        constructor
        · intro ha
          obtain ⟨w, hw, hwa⟩ := ha
          have hdom : SkelPush.pushDomain D k a := by
            rw [SkelPush.pushDomain_iff]
            exact ⟨by rw [← SkelPush.mem_skel_mk D k a, ← hwa]; exact w.2.1,
              by rw [← hwa]; exact w.2.2⟩
          refine ⟨hdom, ?_⟩
          have hy : (⟨a, hdom⟩ : {a : Raw D // SkelPush.pushDomain D k a}) ∈
              (fun a : {a : Raw D // SkelPush.pushDomain D k a} =>
                (⟨Quotient.mk'' a.1, a.2⟩ :
                  {z : Model D // SkelPush.pushDomainModel D k z})) ⁻¹' s := by
            show (⟨Quotient.mk'' a, hdom⟩ :
              {z : Model D // SkelPush.pushDomainModel D k z}) ∈ s
            rw [show (⟨Quotient.mk'' a, hdom⟩ :
              {z : Model D // SkelPush.pushDomainModel D k z}) = w from
                Subtype.ext hwa.symm]
            exact hw
          rwa [← hVeq] at hy
        · rintro ⟨hdom, haV⟩
          refine ⟨(⟨Quotient.mk'' a, hdom⟩ :
            {z : Model D // SkelPush.pushDomainModel D k z}), ?_, rfl⟩
          have hy : (⟨a, hdom⟩ : {a : Raw D // SkelPush.pushDomain D k a}) ∈
              (fun a : {a : Raw D // SkelPush.pushDomain D k a} =>
                (⟨Quotient.mk'' a.1, a.2⟩ :
                  {z : Model D // SkelPush.pushDomainModel D k z})) ⁻¹' s := by
            rw [← hVeq]
            exact haV
          exact hy
      -- the set `{a : A | mk a ∈ S}` is open in the weight part
      have hopenA : IsOpen
          ((Subtype.val : {a : Raw D // rawWeight D a ≤ k + 1} → Raw D) ⁻¹'
            (Quotient.mk'' ⁻¹' S)) := by
        refine ⟨V ∩ (Quotient.mk'' ⁻¹' setOf
              (fun z : Model D => SkelPush.isCentroidModel D k z))ᶜ,
          hVopen.inter hKclosed.isOpen_compl, ?_⟩
        ext aa
        have h1 : Quotient.mk'' (aa : Raw D) ∈ S ↔
            (aa : Raw D) ∈ setOf (fun a : Raw D => SkelPush.pushDomain D k a) ∧
              (aa : Raw D) ∈ V := by
          rw [← Set.mem_preimage]
          exact (Set.ext_iff.mp hmain (aa : Raw D)).trans (Set.mem_inter_iff _ _ _)
        have h2 : (aa : Raw D) ∈ setOf (fun a : Raw D => SkelPush.pushDomain D k a) ↔
            Quotient.mk'' (aa : Raw D) ∉
              setOf (fun z : Model D => SkelPush.isCentroidModel D k z) := by
          rw [hYA]
          constructor
          · rintro ⟨-, hnc⟩; exact hnc
          · intro hnc; exact ⟨aa.2, hnc⟩
        simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_compl_iff]
        rw [h1, h2]
        exact and_comm
      have hq₁S : IsOpen
          ((fun a : {a : Raw D // rawWeight D a ≤ k + 1} =>
              (⟨Quotient.mk'' a.1, (SkelPush.mem_skel_mk D k a.1).mpr a.2⟩ :
                {z : Model D // z ∈ skel D k})) ⁻¹' (Subtype.val ⁻¹' S)) := by
        show IsOpen ((Subtype.val : {a : Raw D // rawWeight D a ≤ k + 1} → Raw D) ⁻¹'
          (Quotient.mk'' ⁻¹' S))
        exact hopenA
      have hSopen : IsOpen ((Subtype.val : {z : Model D // z ∈ skel D k} → Model D) ⁻¹' S) :=
        hq₁.isCoinducing.isOpen_preimage.mp hq₁S
      obtain ⟨W, hWopen, hWeq⟩ := isOpen_induced_iff.mp hSopen
      have hse : s = Subtype.val ⁻¹' W := by
        ext z
        constructor
        · intro hz
          have hzS : (⟨(z : Model D), z.2.1⟩ : {w : Model D // w ∈ skel D k}) ∈
              Subtype.val ⁻¹' W := by
            rw [hWeq]
            exact ⟨z, hz, rfl⟩
          exact hzS
        · intro hzW
          have hzS : (z : Model D) ∈ S := by
            have h1 : (⟨(z : Model D), z.2.1⟩ : {w : Model D // w ∈ skel D k}) ∈
                Subtype.val ⁻¹' W := hzW
            rw [hWeq] at h1
            exact h1
          obtain ⟨w, hw, hwz⟩ := hzS
          have hwz' : w = z := Subtype.ext hwz
          rwa [hwz'] at hw
      rw [hse]
      exact IsOpen.preimage continuous_subtype_val hWopen
    · intro hs
      exact IsOpen.preimage hqcont hs
  · intro z
    obtain ⟨a, ha, hw⟩ := (mem_skel_iff (D := D)).mp z.2.1
    have hdom : SkelPush.pushDomain D k a := by
      rw [SkelPush.pushDomain_iff]
      exact ⟨hw, by rw [ha]; exact z.2.2⟩
    exact ⟨⟨a, hdom⟩, Subtype.ext ha⟩

theorem continuous_of_finite_isClosed_cover {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {ι : Type*} [Finite ι] {U : ι → Set α} (hU : ∀ i, IsClosed (U i))
    (hcov : ∀ x, ∃ i, x ∈ U i) {f : α → β}
    (hf : ∀ i, Continuous fun x : ↥(U i) => f x) : Continuous f := by
  rw [continuous_iff_isClosed]
  intro C hC
  have hpre : f ⁻¹' C = ⋃ i, (Subtype.val '' ((fun x : ↥(U i) => f x) ⁻¹' C)) := by
    ext x
    rw [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := hcov x
      exact ⟨i, ⟨x, hi⟩, hx, rfl⟩
    · rintro ⟨i, y, hy, hyx⟩
      rw [← hyx]
      exact hy
  rw [hpre]
  refine isClosed_iUnion_of_finite fun i => ?_
  exact (hU i).isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp
    (IsClosed.preimage (hf i) hC)

/-! ## Continuity of the face formula -/

theorem continuous_faceVec_subtype (k : ℕ) (S : Finset (Fin (n + 2))) (hS : S.Nonempty) :
    Continuous (fun p : unitInterval × {x : stdSimplex ℝ (Fin (n + 2)) //
        SkelPush.faceDen k S hS x ≠ 0} => SkelPush.faceVec k S hS p.1 p.2.1) := by
  refine continuous_pi fun j => ?_
  rw [show (fun p : unitInterval × {x : stdSimplex ℝ (Fin (n + 2)) //
        SkelPush.faceDen k S hS x ≠ 0} => SkelPush.faceVec k S hS p.1 p.2.1 j)
      = fun p => (1 - (p.1 : ℝ)) * (p.2.1 : Fin (n + 2) → ℝ) j
        + (p.1 : ℝ) * (if j ∈ S then ((p.2.1 : Fin (n + 2) → ℝ) j
            - SkelPush.faceMin S hS p.2.1) / SkelPush.faceDen k S hS p.2.1 else 0) from by
    funext p; rw [SkelPush.faceVec_apply]]
  have hxv : Continuous fun p : unitInterval × {x : stdSimplex ℝ (Fin (n + 2)) //
      SkelPush.faceDen k S hS x ≠ 0} => p.2.1 := continuous_subtype_val.comp continuous_snd
  have hx : Continuous fun p : unitInterval × {x : stdSimplex ℝ (Fin (n + 2)) //
      SkelPush.faceDen k S hS x ≠ 0} => (p.2.1 : Fin (n + 2) → ℝ) j :=
    (continuous_apply j).comp ((continuous_subtype_val).comp hxv)
  have hu : Continuous fun p : unitInterval × {x : stdSimplex ℝ (Fin (n + 2)) //
      SkelPush.faceDen k S hS x ≠ 0} => (p.1 : ℝ) :=
    (continuous_subtype_val).comp continuous_fst
  have hfm : Continuous fun p : unitInterval × {x : stdSimplex ℝ (Fin (n + 2)) //
      SkelPush.faceDen k S hS x ≠ 0} => SkelPush.faceMin S hS p.2.1 :=
    (SkelPush.continuous_faceMin S hS).comp hxv
  have hfd : Continuous fun p : unitInterval × {x : stdSimplex ℝ (Fin (n + 2)) //
      SkelPush.faceDen k S hS x ≠ 0} => SkelPush.faceDen k S hS p.2.1 :=
    (SkelPush.continuous_faceDen k S hS).comp hxv
  refine Continuous.add ?_ ?_
  · exact (continuous_const.sub hu).mul hx
  · refine Continuous.mul hu ?_
    by_cases hj : j ∈ S
    · simp only [if_pos hj]
      exact Continuous.div (hx.sub hfm) hfd (fun p => p.2.2)
    · simp only [if_neg hj]
      exact continuous_const

/-! ## The raw push on a closed face -/

theorem pushRaw_eq_facePt {D : MData X n x₀} {k : ℕ} {i : D.Idx}
    {S : Finset (Fin (n + 2))} (hcard : S.card = k + 1) (hS : S.Nonempty)
    {x : stdSimplex ℝ (Fin (n + 2))} (hx : x ∈ SkelPush.faceSet S)
    (hwt : (supp x).card ≤ k + 1) (hden : SkelPush.faceDen k S hS x ≠ 0) (u : unitInterval) :
    pushRaw D k u (Sum.inl ⟨i, x⟩)
      = Sum.inl ⟨i, SkelPush.facePt k S hS u x hcard hx hden⟩ := by
  by_cases hw : (supp x).card = k + 1
  · have hsupp : supp x = S :=
      Finset.eq_of_subset_of_card_le (SkelPush.mem_faceSet.mp hx) (by rw [hcard, hw])
    have hden' : 1 - ((k : ℝ) + 1) * suppMin x ≠ 0 := by
      rw [← SkelPush.faceMin_eq_suppMin hS hcard hx hw, ← SkelPush.faceDen_eq]
      exact hden
    have hpt : pushPt k u x hw hden' = SkelPush.facePt k S hS u x hcard hx hden := by
      apply Subtype.ext
      funext j
      show ((1 - (u : ℝ)) • (x : Fin (n + 2) → ℝ)
          + (u : ℝ) • (collapseFun k x) : Fin (n + 2) → ℝ) j = SkelPush.faceVec k S hS u x j
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        SkelPush.faceVec_apply, collapseFun]
      by_cases hj : j ∈ S
      · have hj' : j ∈ supp x := by rw [hsupp]; exact hj
        simp only [if_pos hj, if_pos hj', SkelPush.faceMin_eq_suppMin hS hcard hx hw,
          SkelPush.faceDen_eq]
      · have hj' : j ∉ supp x := by rw [hsupp]; exact hj
        simp only [if_neg hj, if_neg hj']
    rw [pushRaw_inl_push D k u i x hw hden', hpt]
  · have hwt' : (supp x).card ≤ k := by omega
    rw [pushRaw_inl_eq_self D k u i x (by intro hcon; exact hw hcon.1)]
    rw [SkelPush.facePt_eq_self_of_faceMin_zero k S hS hcard hx
      (SkelPush.faceMin_eq_zero_of_card_lt hS hcard hx hwt') hden u]

/-! ## Closedness of the pieces of the cover -/

theorem isClosed_inrCopy (D : MData X n x₀) (i : D.Idx) :
    IsClosed (setOf fun a : Raw D => ∃ t : unitInterval, a = Sum.inr ⟨i, t⟩) := by
  rw [isClosed_sum_iff]
  constructor
  · have h : Sum.inl ⁻¹' (setOf fun a : Raw D => ∃ t : unitInterval, a = Sum.inr ⟨i, t⟩)
        = (∅ : Set (Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2)))) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨t, ht⟩
      exact Sum.inl_ne_inr ht
    rw [h]; exact isClosed_empty
  · rw [isClosed_sigma_iff]
    intro j
    by_cases hj : j = i
    · have h : Sigma.mk j ⁻¹' (Sum.inr ⁻¹'
          (setOf fun a : Raw D => ∃ t : unitInterval, a = Sum.inr ⟨i, t⟩)) = Set.univ := by
        rw [hj]
        ext t
        exact ⟨fun _ => trivial, fun _ => ⟨t, rfl⟩⟩
      rw [h]; exact isClosed_univ
    · have h : Sigma.mk j ⁻¹' (Sum.inr ⁻¹'
          (setOf fun a : Raw D => ∃ t : unitInterval, a = Sum.inr ⟨i, t⟩)) = ∅ := by
        ext t
        constructor
        · rintro ⟨t', ht'⟩
          exact absurd (congrArg Sigma.fst (Sum.inr.inj ht')) hj
        · intro h; exact absurd h (Set.notMem_empty t)
      rw [h]; exact isClosed_empty

theorem isClosed_inlFace (D : MData X n x₀) (i : D.Idx) (T : Set (stdSimplex ℝ (Fin (n + 2))))
    (hT : IsClosed T) :
    IsClosed (setOf fun a : Raw D => ∃ x : stdSimplex ℝ (Fin (n + 2)), a = Sum.inl ⟨i, x⟩ ∧ x ∈ T) := by
  rw [isClosed_sum_iff]
  constructor
  · have h : Sum.inl ⁻¹' (setOf fun a : Raw D =>
        ∃ x : stdSimplex ℝ (Fin (n + 2)), a = Sum.inl ⟨i, x⟩ ∧ x ∈ T)
        = Set.image (fun y : stdSimplex ℝ (Fin (n + 2)) =>
            (⟨i, y⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))) T := by
      ext y
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_image]
      exact ⟨fun ⟨x, h, hx⟩ => ⟨x, hx, (Sum.inl.inj h).symm⟩,
        fun ⟨x, hx, h⟩ => ⟨x, congrArg Sum.inl h.symm, hx⟩⟩
    rw [h, isClosed_sigma_iff]
    intro j
    by_cases hj : j = i
    · have h2 : Sigma.mk j ⁻¹' (Set.image (fun y : stdSimplex ℝ (Fin (n + 2)) =>
            (⟨i, y⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))) T) = T := by
        rw [hj]
        ext x
        simp only [Set.mem_preimage, Set.mem_image]
        constructor
        · rintro ⟨x', hx', h⟩
          have hinj := Sigma.mk.inj_iff.mp h
          have hxx : x' = x := eq_of_heq hinj.2
          rw [← hxx]; exact hx'
        · intro hx; exact ⟨x, hx, rfl⟩
      rw [h2]; exact hT
    · have h2 : Sigma.mk j ⁻¹' (Set.image (fun y : stdSimplex ℝ (Fin (n + 2)) =>
            (⟨i, y⟩ : Σ _ : D.Idx, stdSimplex ℝ (Fin (n + 2)))) T) = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false, iff_false]
        rintro ⟨x', hx', h⟩
        exact absurd (Sigma.mk.inj_iff.mp h).1 (fun hij => hj hij.symm)
      rw [h2]; exact isClosed_empty
  · have h : Sum.inr ⁻¹' (setOf fun a : Raw D =>
        ∃ x : stdSimplex ℝ (Fin (n + 2)), a = Sum.inl ⟨i, x⟩ ∧ x ∈ T) = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨x, h, hx⟩
      exact Sum.inr_ne_inl h
    rw [h]; exact isClosed_empty
/-! ## `faceDen = 0` characterises the centroid of the face -/

theorem isCentroidPt_of_faceDen_eq_zero {k : ℕ} {S : Finset (Fin (n + 2))} (hcard : S.card = k + 1)
    (hS : S.Nonempty) {x : stdSimplex ℝ (Fin (n + 2))} (hx : x ∈ SkelPush.faceSet S)
    (hw : (supp x).card = k + 1) (hzero : SkelPush.faceDen k S hS x = 0) :
    SkelPush.IsCentroidPt x := by
  have hmem : supp x ⊆ S := SkelPush.mem_faceSet.mp hx
  have hsupp : supp x = S := Finset.eq_of_subset_of_card_le hmem (by rw [hcard, hw])
  have hmin : suppMin x = ((k : ℝ) + 1)⁻¹ := by
    have h1 : ((k : ℝ) + 1) * SkelPush.faceMin S hS x = 1 := by
      have := hzero
      rw [SkelPush.faceDen_eq] at this
      linarith
    have hkpos : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [← SkelPush.faceMin_eq_suppMin hS hcard hx hw]
    calc SkelPush.faceMin S hS x
        = ((k : ℝ) + 1)⁻¹ * (((k : ℝ) + 1) * SkelPush.faceMin S hS x) := by
          rw [← mul_assoc, inv_mul_cancel₀ hkpos, one_mul]
      _ = ((k : ℝ) + 1)⁻¹ := by rw [h1, mul_one]
  have hval : ∀ i ∈ supp x, (x : Fin (n + 2) → ℝ) i = ((k : ℝ) + 1)⁻¹ := by
    intro i hi
    have hsum : ∑ j ∈ supp x, ((x : Fin (n + 2) → ℝ) j - suppMin x) = 0 := by
      rw [Finset.sum_sub_distrib, sum_supp, Finset.sum_const, nsmul_eq_mul,
        show ((supp x).card : ℝ) = (k : ℝ) + 1 by rw [hw]; push_cast; ring, hmin]
      field_simp
      ring
    have hterm : (x : Fin (n + 2) → ℝ) i - suppMin x = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => sub_nonneg.mpr (suppMin_le x hj))).mp
        hsum i hi
    linarith [sub_eq_zero.mp hterm]
  have hne : (ptSupport x).Nonempty := by
    rw [ptSupport_eq_supp]; exact Finset.card_pos.mp (by rw [hw]; omega)
  refine ⟨hne, ?_⟩
  have hfun : (x : Fin (n + 2) → ℝ)
      = ((centroidPt (ptSupport x) hne : stdSimplex ℝ (Fin (n + 2))) : Fin (n + 2) → ℝ) := by
    funext i
    by_cases hi : i ∈ ptSupport x
    · rw [centroidPt_apply_mem hne hi]
      have hi' : i ∈ supp x := by rwa [ptSupport_eq_supp x] at hi
      rw [hval i hi']
      congr 1
      rw [ptSupport_eq_supp x, hw]
      push_cast
      ring
    · rw [centroidPt_apply_notMem hne hi]
      exact (by simpa [mem_ptSupport] using hi : (x : Fin (n + 2) → ℝ) i = 0)
  exact Subtype.ext hfun

/-! ## The closed pieces covering the raw push domain -/

/-- The pieces of the closed cover of the raw push domain: the arcs (indexed by a copy) and, for a
copy `i` and a vertex set `S` of cardinality `k+1`, the points of the face spanned by `S` in the
`i`-th copy. -/
def pushPiece (D : MData X n x₀) (k : ℕ) :
    (D.Idx ⊕ (D.Idx × {S : Finset (Fin (n + 2)) // S.card = k + 1})) →
      Set (unitInterval × {a : Raw D // SkelPush.pushDomain D k a})
  | Sum.inl i => setOf fun p => ∃ t : unitInterval, p.2.1 = Sum.inr ⟨i, t⟩
  | Sum.inr ⟨i, S⟩ => setOf fun p => ∃ x : stdSimplex ℝ (Fin (n + 2)),
      p.2.1 = Sum.inl ⟨i, x⟩ ∧ x ∈ SkelPush.faceSet S.1

@[simp] theorem mem_piece_inl (D : MData X n x₀) (k : ℕ) (i : D.Idx)
    (p : unitInterval × {a : Raw D // SkelPush.pushDomain D k a}) :
    p ∈ pushPiece (D := D) k (Sum.inl i) ↔ ∃ t : unitInterval, p.2.1 = Sum.inr ⟨i, t⟩ := Iff.rfl

@[simp] theorem mem_piece_inr (D : MData X n x₀) (k : ℕ) (i : D.Idx)
    (S : {S : Finset (Fin (n + 2)) // S.card = k + 1})
    (p : unitInterval × {a : Raw D // SkelPush.pushDomain D k a}) :
    p ∈ pushPiece (D := D) k (Sum.inr ⟨i, S⟩) ↔ ∃ x : stdSimplex ℝ (Fin (n + 2)),
      p.2.1 = Sum.inl ⟨i, x⟩ ∧ x ∈ SkelPush.faceSet S.1 := Iff.rfl

/-! ## Continuity of the raw push on its domain -/

set_option maxHeartbeats 1600000 in
/-- **The raw push is continuous on the raw push domain.**  The domain is covered by the closed
pieces consisting of the arcs and, for every copy and every `(k+1)`-element vertex set `S`, of the
face spanned by `S`; on each such pushPiece the push is given by the face formula `facePt`. -/
theorem continuous_pushRaw_domain (D : MData X n x₀) (k : ℕ) :
    Continuous (fun p : unitInterval × {a : Raw D // SkelPush.pushDomain D k a} =>
      pushRaw D k p.1 p.2.1) := by
  classical
  by_cases hk' : k + 1 ≤ n + 2
  · refine continuous_of_finite_isClosed_cover (U := fun o => pushPiece (D := D) k o) ?_ ?_ ?_
    · intro o
      rcases o with i | ⟨i, S⟩
      · exact (isClosed_inrCopy D i).preimage (Continuous.subtype_val continuous_snd)
      · exact (isClosed_inlFace D i (SkelPush.faceSet S.1)
          (SkelPush.isClosed_faceSet S.1)).preimage (Continuous.subtype_val continuous_snd)
    · intro p
      rcases hp : p.2.1 with ⟨i, x⟩ | ⟨i, t⟩
      · by_cases hw : (supp x).card = k + 1
        · exact ⟨Sum.inr ⟨i, ⟨supp x, hw⟩⟩, x, hp, SkelPush.mem_faceSet.mpr subset_rfl⟩
        · have hwt : (supp x).card ≤ k + 1 := by
            have h := p.2.2
            rw [hp, SkelPush.pushDomain_iff] at h
            have h2 : (ptSupport x).card ≤ k + 1 := by simpa [rawWeight_inl] using h.1
            rwa [ptSupport_eq_supp x] at h2
          obtain ⟨S, hsub, hcard⟩ := Finset.exists_superset_card_eq (s := supp x) hwt
            (by simpa using hk')
          exact ⟨Sum.inr ⟨i, ⟨S, hcard⟩⟩, x, hp, SkelPush.mem_faceSet.mpr hsub⟩
      · exact ⟨Sum.inl i, t, hp⟩
    · intro o
      rcases o with i | ⟨i, S⟩
      · have h1 : (fun p : ↥(pushPiece (D := D) k (Sum.inl i)) => pushRaw D k p.1.1 p.1.2.1)
            = fun p => p.1.2.1 := by
          funext p
          obtain ⟨t, ht⟩ := p.2
          rw [ht]
          rfl
        rw [h1]
        exact (Continuous.subtype_val continuous_snd).comp continuous_subtype_val
      · have hcard : S.1.card = k + 1 := S.2
        have hSne : S.1.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
        have hxmem : ∀ p : ↥(pushPiece (D := D) k (Sum.inr ⟨i, S⟩)),
            SkelPush.rawSimplex D p.1.2.1 ∈ SkelPush.faceSet S.1 := by
          intro p
          obtain ⟨x, hp, hx⟩ := p.2
          rw [show SkelPush.rawSimplex D p.1.2.1 = x from by rw [hp, SkelPush.rawSimplex_inl]]
          exact hx
        have hwt : ∀ p : ↥(pushPiece (D := D) k (Sum.inr ⟨i, S⟩)),
            (supp (SkelPush.rawSimplex D p.1.2.1)).card ≤ k + 1 := by
          intro p
          obtain ⟨x, hp, hx⟩ := p.2
          have h := p.1.2.2
          rw [hp, SkelPush.pushDomain_iff] at h
          have h2 : (ptSupport x).card ≤ k + 1 := by simpa [rawWeight_inl] using h.1
          rw [show SkelPush.rawSimplex D p.1.2.1 = x from by rw [hp, SkelPush.rawSimplex_inl]]
          rwa [ptSupport_eq_supp x] at h2
        have hden : ∀ p : ↥(pushPiece (D := D) k (Sum.inr ⟨i, S⟩)),
            SkelPush.faceDen k S.1 hSne (SkelPush.rawSimplex D p.1.2.1) ≠ 0 := by
          intro p
          have hmem := hxmem p
          have hwtp := hwt p
          by_cases hw : (supp (SkelPush.rawSimplex D p.1.2.1)).card = k + 1
          · intro hzero
            obtain ⟨x, hp, hx⟩ := p.2
            have hxs : SkelPush.rawSimplex D p.1.2.1 = x := by rw [hp, SkelPush.rawSimplex_inl]
            have hpt : SkelPush.IsCentroidPt x := by
              have h0 := isCentroidPt_of_faceDen_eq_zero (k := k) hcard hSne hmem hw hzero
              rwa [hxs] at h0
            have hcardx : (ptSupport x).card = k + 1 := by
              have h2 : (supp x).card = k + 1 := by rwa [hxs] at hw
              rwa [ptSupport_eq_supp x]
            have hcentroid : SkelPush.isCentroidModel D k (Quotient.mk'' p.1.2.1) := by
              have hc := SkelPush.isCentroidModel_of_isCentroidPt (D := D) (i := i) hpt hcardx
              rwa [← hp] at hc
            have hdom := p.1.2.2
            rw [SkelPush.pushDomain_iff] at hdom
            exact hdom.2 hcentroid
          · rw [SkelPush.faceDen_eq,
              SkelPush.faceMin_eq_zero_of_card_lt hSne hcard hmem (by omega)]
            norm_num
        have hform : Continuous fun p : ↥(pushPiece (D := D) k (Sum.inr ⟨i, S⟩)) =>
            SkelPush.facePt k S.1 hSne p.1.1 (SkelPush.rawSimplex D p.1.2.1) hcard
              (hxmem p) (hden p) := by
          have hXc : Continuous fun p : ↥(pushPiece (D := D) k (Sum.inr ⟨i, S⟩)) =>
              SkelPush.rawSimplex D p.1.2.1 :=
            ((SkelPush.continuous_rawSimplex D).comp
              (Continuous.subtype_val continuous_snd)).comp continuous_subtype_val
          have hsub : Continuous fun p : ↥(pushPiece (D := D) k (Sum.inr ⟨i, S⟩)) =>
              (⟨SkelPush.rawSimplex D p.1.2.1, hden p⟩ :
                {x : stdSimplex ℝ (Fin (n + 2)) // SkelPush.faceDen k S.1 hSne x ≠ 0}) :=
            Continuous.subtype_mk hXc (fun p => hden p)
          have hunit : Continuous fun p : ↥(pushPiece (D := D) k (Sum.inr ⟨i, S⟩)) => p.1.1 :=
            continuous_fst.comp continuous_subtype_val
          exact Continuous.subtype_mk
            ((continuous_faceVec_subtype k S.1 hSne).comp (Continuous.prodMk hunit hsub))
            (fun p => ⟨SkelPush.faceVec_nonneg k hSne hcard (hxmem p) (hden p) p.1.1,
              SkelPush.sum_faceVec k hSne hcard (hxmem p) (hden p) p.1.1⟩)
        have hval : (fun p : ↥(pushPiece (D := D) k (Sum.inr ⟨i, S⟩)) => pushRaw D k p.1.1 p.1.2.1)
            = fun p => Sum.inl ⟨i, SkelPush.facePt k S.1 hSne p.1.1
                (SkelPush.rawSimplex D p.1.2.1) hcard (hxmem p) (hden p)⟩ := by
          funext p
          obtain ⟨x, hp, hx⟩ := p.2
          have hxs : SkelPush.rawSimplex D p.1.2.1 = x := by rw [hp, SkelPush.rawSimplex_inl]
          have hdenx : SkelPush.faceDen k S.1 hSne x ≠ 0 := hxs ▸ hden p
          have hpt : SkelPush.facePt k S.1 hSne p.1.1 (SkelPush.rawSimplex D p.1.2.1) hcard
              (hxmem p) (hden p) = SkelPush.facePt k S.1 hSne p.1.1 x hcard hx hdenx := by
            apply Subtype.ext
            show SkelPush.faceVec k S.1 hSne p.1.1 (SkelPush.rawSimplex D p.1.2.1)
              = SkelPush.faceVec k S.1 hSne p.1.1 x
            rw [hxs]
          rw [hpt]
          rw [hp]
          exact pushRaw_eq_facePt hcard hSne hx (hxs ▸ hwt p) hdenx p.1.1
        rw [hval]
        exact continuous_inl.comp (continuous_sigmaMk.comp hform)
  · have hid : ∀ (u : unitInterval) (a : Raw D), pushRaw D k u a = a := by
      intro u a
      rcases a with ⟨i, x⟩ | ⟨i, t⟩
      · rw [pushRaw_inl_eq_self D k u i x]
        rintro ⟨h1, h2⟩
        have h := Finset.card_le_univ (supp x)
        rw [Fintype.card_fin] at h
        omega
      · rfl
    rw [show (fun p : unitInterval × {a : Raw D // SkelPush.pushDomain D k a} =>
        pushRaw D k p.1 p.2.1) = fun p => p.2.1 from funext fun p => hid p.1 p.2.1]
    exact Continuous.subtype_val continuous_snd


/-! ## Elementary properties of the raw push -/

theorem pushRaw_zero (D : MData X n x₀) (k : ℕ) (a : Raw D) : pushRaw D k 0 a = a := by
  rcases a with ⟨i, x⟩ | ⟨i, t⟩
  · by_cases h : (supp x).card = k + 1 ∧ 1 - ((k : ℝ) + 1) * suppMin x ≠ 0
    · rw [pushRaw_inl_push D k 0 i x h.1 h.2, pushPt_zero]
    · rw [pushRaw_inl_eq_self D k 0 i x h]
  · rfl

theorem pushRaw_eq_self_of_weight_le (D : MData X n x₀) (k : ℕ) {a : Raw D}
    (h : rawWeight D a ≤ k) (u : unitInterval) : pushRaw D k u a = a := by
  rcases a with ⟨i, x⟩ | ⟨i, t⟩
  · rw [pushRaw_inl_eq_self D k u i x]
    rintro ⟨h1, h2⟩
    have h2' : (ptSupport x).card ≤ k := by simpa [rawWeight_inl] using h
    rw [ptSupport_eq_supp x] at h2'
    omega
  · rfl

/-- If the denominator of the push vanishes at a point of weight `k+1`, that point is the centroid
of its own support. -/
theorem isCentroidPt_of_pushGuard_false (k : ℕ) {x : stdSimplex ℝ (Fin (n + 2))}
    (hw : (supp x).card = k + 1) (hden : 1 - ((k : ℝ) + 1) * suppMin x = 0) :
    SkelPush.IsCentroidPt x := by
  have hS : (supp x).Nonempty := Finset.card_pos.mp (by rw [hw]; omega)
  have hx : x ∈ SkelPush.faceSet (supp x) := SkelPush.mem_faceSet.mpr subset_rfl
  have hfm : SkelPush.faceMin (supp x) hS x = suppMin x :=
    SkelPush.faceMin_eq_suppMin hS hw hx hw
  have hzero : SkelPush.faceDen k (supp x) hS x = 0 := by
    rw [SkelPush.faceDen_eq, hfm]
    exact hden
  exact isCentroidPt_of_faceDen_eq_zero hw hS hx hw hzero

/-- **At time `1` the raw push lowers the weight of every point of the push domain to at most
`k`.** -/
theorem rawWeight_pushRaw_one_le (D : MData X n x₀) (k : ℕ) (hk : 2 ≤ k) {a : Raw D}
    (ha : SkelPush.pushDomain D k a) : rawWeight D (pushRaw D k 1 a) ≤ k := by
  rcases a with ⟨i, x⟩ | ⟨i, t⟩
  · by_cases h : (supp x).card = k + 1 ∧ 1 - ((k : ℝ) + 1) * suppMin x ≠ 0
    · rw [pushRaw_inl_push D k 1 i x h.1 h.2]
      have hlt := weight_pushPt_one_lt k x h.1 h.2
      rw [rawWeight_inl, ptSupport_eq_supp (pushPt k 1 x h.1 h.2)]
      omega
    · have hcard : (supp x).card ≤ k := by
        have hwt : (supp x).card ≤ k + 1 := by
          have hd := ha
          rw [SkelPush.pushDomain_iff] at hd
          have h2 : (ptSupport x).card ≤ k + 1 := by simpa [rawWeight_inl] using hd.1
          rwa [ptSupport_eq_supp x] at h2
        by_cases heq : (supp x).card = k + 1
        · exfalso
          have hden0 : 1 - ((k : ℝ) + 1) * suppMin x = 0 := by
            by_contra hne
            exact h ⟨heq, hne⟩
          have hpt := isCentroidPt_of_pushGuard_false (k := k) heq hden0
          have hcardpt : (ptSupport x).card = k + 1 := by rwa [ptSupport_eq_supp x]
          have hc2 := SkelPush.isCentroidModel_of_isCentroidPt (D := D) (i := i) hpt hcardpt
          have hd := ha
          rw [SkelPush.pushDomain_iff] at hd
          exact hd.2 hc2
        · omega
      rw [pushRaw_inl_eq_self D k 1 i x h, rawWeight_inl]
      rwa [ptSupport_eq_supp x]
  · rw [pushRaw_inr, rawWeight_inr]
    omega

/-- The restriction of `Quotient.mk''` to the push domain, as a map onto the push domain of the
model. -/
def pushDomainMap (D : MData X n x₀) (k : ℕ) :
    {a : Raw D // SkelPush.pushDomain D k a} →
      {z : Model D // SkelPush.pushDomainModel D k z} :=
  fun a => ⟨Quotient.mk'' a.1, a.2⟩


/-- **The uniform push of the `k`-cells, descended to the model and restricted to the domain on
which it is continuous.**

The raw-level input is `Work.RatHurewicz.pushRawUniform`; the descent of the raw push along the
quotient map `Raw D → Model D` is `Work.RatHurewicz.pushModel`.  What is asked here is the
*continuity* of the descended homotopy on the domain `pushDomainModel D k` (the `k`-skeleton with
the images of the centroids of its `(k+1)`-faces removed), together with its two characteristic
properties.  Route: let `Y := {a : Raw D // pushDomain D k a}`, `Z := {z : Model D //
pushDomainModel D k z}` and `qY : Y → Z` the restriction of `Quotient.mk''`.  If one can show
`Topology.IsQuotientMap qY`, then `Φ` is continuous by
`Topology.IsQuotientMap.continuous_lift_prod_right`.  (Beware: the restriction of a quotient map to a
general saturated subset need not be a quotient map; among the usable sufficient conditions are
`Topology.IsQuotientMap.restrictPreimage_isOpen` with `f := (skel D k).restrictPreimage
Quotient.mk''` — a quotient map because `{a | rawWeight D a ≤ k + 1} = Quotient.mk'' ⁻¹' skel D k` is
closed and saturated in `Raw D` — and the *open* subset `Z ⊆ skel D k`, which is open because it is
the complement of the finite set `isCentroidModel D k`: each of its points has a fixed *shape* in the
sense of `Work.RatHurewicz.shapeOf` (`Submission/Work/RatHurewicz/avoidAux.lean`), which is invariant
under the gluing relation and determines only finitely many points.) -/
theorem pushModelUniform {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}
    (D : Work.RatHurewicz.MData X n x₀) (k : ℕ) (hk : 2 ≤ k) :
    ∃ (Φ : C(unitInterval × {z : Work.RatHurewicz.Model D //
        Work.RatHurewicz.SkelPush.pushDomainModel D k z}, Work.RatHurewicz.Model D)),
      (∀ z, Φ (0, z) = z) ∧
      (∀ (z : {z : Work.RatHurewicz.Model D //
          Work.RatHurewicz.SkelPush.pushDomainModel D k z}),
        (z : Work.RatHurewicz.Model D) ∈ Work.RatHurewicz.skel D (k - 1) →
          ∀ s : unitInterval, Φ (s, z) = z) ∧
      (∀ z, Φ (1, z) ∈ Work.RatHurewicz.skel D (k - 1)) := by
  classical
  have hcont : Continuous (fun p : unitInterval × {a : Raw D // SkelPush.pushDomain D k a} =>
      pushRaw D k p.1 p.2.1) := continuous_pushRaw_domain D k
  let Ψ : C(unitInterval × {a : Raw D // SkelPush.pushDomain D k a}, Raw D) :=
    ⟨fun p => pushRaw D k p.1 p.2.1, hcont⟩
  have hΨ0 : ∀ a, Ψ (0, a) = a := fun a => pushRaw_zero D k a.1
  have hΨid : ∀ a : {a : Raw D // SkelPush.pushDomain D k a},
      rawWeight D a ≤ k → ∀ s : unitInterval, Ψ (s, a) = a :=
    fun a h s => pushRaw_eq_self_of_weight_le D k h s
  have hΨw : ∀ a : {a : Raw D // SkelPush.pushDomain D k a},
      rawWeight D (Ψ (1, a)) ≤ k := fun a => rawWeight_pushRaw_one_le D k hk a.2
  have hΨcompat : ∀ (a b : Raw D) (ha : SkelPush.pushDomain D k a)
      (hb : SkelPush.pushDomain D k b), Relation.EqvGen (modelRel D) a b →
      ∀ s : unitInterval,
        (Quotient.mk'' (Ψ (s, ⟨a, ha⟩)) : Model D) = Quotient.mk'' (Ψ (s, ⟨b, hb⟩)) :=
    fun a b ha hb hrel s => Quotient.sound (pushRaw_eqvGen D k s hrel)
  have hquot : Topology.IsQuotientMap (pushDomainMap D k) := isQuotientMap_pushDomain D k hk
  have hsurj : Function.Surjective (pushDomainMap D k) := hquot.surjective
  let qinv : {z : Model D // SkelPush.pushDomainModel D k z} →
      {a : Raw D // SkelPush.pushDomain D k a} :=
    fun z => Classical.choose (hsurj z)
  let F : unitInterval × {a : Raw D // SkelPush.pushDomain D k a} → Model D :=
    fun p => Quotient.mk'' (Ψ (p.1, p.2))
  have hFcont : Continuous F := continuous_quotient_mk'.comp Ψ.continuous
  have hfib : ∀ (s : unitInterval) (a b : {a : Raw D // SkelPush.pushDomain D k a}),
      pushDomainMap D k a = pushDomainMap D k b → F (s, a) = F (s, b) := by
    intro s a b hab
    exact hΨcompat a.1 b.1 a.2 b.2 (Quotient.exact (congrArg Subtype.val hab)) s
  let Φ : unitInterval × {z : Model D // SkelPush.pushDomainModel D k z} → Model D :=
    fun p => F (p.1, qinv p.2)
  have hqinv : ∀ z : {w : Model D // SkelPush.pushDomainModel D k w},
      pushDomainMap D k (qinv z) = z :=
    fun z => Classical.choose_spec (hsurj z)
  have hΦcomp : Continuous fun p : unitInterval × {a : Raw D // SkelPush.pushDomain D k a} =>
      Φ (p.1, pushDomainMap D k p.2) := by
    have h1 : (fun p : unitInterval × {a : Raw D // SkelPush.pushDomain D k a} =>
        Φ (p.1, pushDomainMap D k p.2)) = F := by
      funext p
      exact hfib p.1 _ p.2 (hqinv (pushDomainMap D k p.2))
    rw [h1]
    exact hFcont
  have hΦcont : Continuous Φ := hquot.continuous_lift_prod_right hΦcomp
  refine ⟨⟨Φ, hΦcont⟩, ?_, ?_, ?_⟩
  · intro z
    show Quotient.mk'' (Ψ (0, qinv z)) = (z : Model D)
    rw [hΨ0]
    exact congrArg Subtype.val (hqinv z)
  · intro z hz s
    have hw : rawWeight D (qinv z).1 ≤ k := by
      obtain ⟨a, ha, hwa⟩ := (mem_skel_iff (D := D)).mp hz
      have h3 : Quotient.mk'' (qinv z).1 = Quotient.mk'' a :=
        (congrArg Subtype.val (hqinv z)).trans ha.symm
      rw [SkelPush.rawWeight_eqvGen' (Quotient.exact h3)]
      omega
    show Quotient.mk'' (Ψ (s, qinv z)) = (z : Model D)
    rw [hΨid _ hw s]
    exact congrArg Subtype.val (hqinv z)
  · intro z
    show Quotient.mk'' (Ψ (1, qinv z)) ∈ skel D (k - 1)
    refine (SkelPush.mem_skel_mk D (k - 1) _).mpr ?_
    have := hΨw (qinv z)
    omega

end

end Work.RatHurewicz
