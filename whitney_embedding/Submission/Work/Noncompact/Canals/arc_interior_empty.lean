import Mathlib

/-!
# The image of a compact arc has empty interior

Two results are proved here.

* `interior_image_arc_empty_euclidean`: for `n ≥ 2`, a compact set `K ⊆ ℝ` whose image under a
  continuous map `γ : ℝ → ℝ^n` is injective on `K` has image with empty interior.
* `Work.Noncompact.Canals.arc_interior_empty`: the same statement for a topological `n`-manifold
  (`n ≥ 2`), obtained from the euclidean statement by a chart reduction.

The euclidean statement is the `n`-dimensional version of
`Work.Whitney.PathTools.interior_image_arc_empty` (the case `n = 2`), whose proof is transcribed
here: inside an alleged ball in the image we draw two arcs meeting exactly in two points, and their
preimages under the embedding `K → ℝ^n` are two connected subsets of `ℝ` whose intersection is a
two point set -- impossible, since connected subsets of `ℝ` are intervals.
-/

open scoped InnerProductSpace
open Set Metric

namespace Work.Noncompact.Canals

/-- If `γ` is continuous and injective on the compact set `K ⊆ ℝ`, then the preimage under `γ` of a
(pre)connected subset of `γ '' K` is (pre)connected.

This is the `IsInducing`/closed–map transfer of connectedness along the topological embedding
`γ|_K`. -/
private lemma preconnected_preimage_of_compact
    {n : ℕ} {γ : ℝ → EuclideanSpace ℝ (Fin n)} {K : Set ℝ} (hK : IsCompact K)
    (hcont : ContinuousOn γ K) (hinj : Set.InjOn γ K)
    {T : Set (EuclideanSpace ℝ (Fin n))} (hT : IsPreconnected T) (hTsub : T ⊆ γ '' K) :
    IsPreconnected (K ∩ γ ⁻¹' T) := by
  have hC : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hcont' : Continuous (K.domRestrict γ) := hcont.domRestrict
  have hinj' : Function.Injective (K.domRestrict γ) := by
    intro x y hxy
    rw [Set.domRestrict_apply, Set.domRestrict_apply] at hxy
    exact Subtype.ext (hinj x.2 y.2 hxy)
  have hrange : Set.range (K.domRestrict γ) = γ '' K := by
    ext z; constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, (Set.domRestrict_apply γ K x).symm⟩
    · rintro ⟨w, hwK, rfl⟩
      exact ⟨⟨w, hwK⟩, Set.domRestrict_apply γ K ⟨w, hwK⟩⟩
  have hpre : IsPreconnected ((K.domRestrict γ) ⁻¹' T) :=
    hT.preimage_of_isClosedMap hinj' hcont'.isClosedMap (by rw [hrange]; exact hTsub)
  have himg : Subtype.val '' ((K.domRestrict γ) ⁻¹' T) = K ∩ γ ⁻¹' T := by
    ext z; constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, by simpa only [Set.mem_preimage, Set.domRestrict_apply] using hx⟩
    · rintro ⟨hzK, hzT⟩
      exact ⟨⟨z, hzK⟩, by simpa only [Set.mem_preimage, Set.domRestrict_apply] using hzT, rfl⟩
  rw [← himg]
  exact Topology.IsInducing.subtypeVal.isPreconnected_image.mpr hpre

/-- **The image of a compact arc in `ℝ^n`, `n ≥ 2`, has empty interior.** -/
theorem interior_image_arc_empty_euclidean {n : ℕ} (hn : 2 ≤ n)
    {γ : ℝ → EuclideanSpace ℝ (Fin n)} {K : Set ℝ} (hK : IsCompact K)
    (hcont : ContinuousOn γ K) (hinj : Set.InjOn γ K) :
    interior (γ '' K) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  rw [mem_interior_iff_mem_nhds] at hy
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hy
  have hn0 : 0 < n := by omega
  set i0 : Fin n := ⟨0, hn0⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  have hi01 : i1 ≠ i0 := by
    intro h
    have := congrArg Fin.val h
    rw [hi0, hi1] at this
    simp at this
  set v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i0 (1:ℝ) with hv
  set w : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i1 (1:ℝ) with hw
  have hon : ∀ i j : Fin n,
      ⟪EuclideanSpace.single i (1:ℝ), EuclideanSpace.single j (1:ℝ)⟫_ℝ = if i = j then 1 else 0 :=
    (orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single)
  have hvv : ⟪v, v⟫_ℝ = 1 := by rw [hv]; exact (hon i0 i0).trans (if_pos rfl)
  have hwv : ⟪w, v⟫_ℝ = 0 := by
    rw [hw, hv, hon i1 i0]
    exact if_neg hi01
  have hww : ⟪w, w⟫_ℝ = 1 := by rw [hw]; exact (hon i1 i1).trans (if_pos rfl)
  have hvnorm : ‖v‖ = 1 := by
    have h2 : ‖v‖^2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hvv
    nlinarith [norm_nonneg v]
  have hwnorm : ‖w‖ = 1 := by
    have h2 : ‖w‖^2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hww
    nlinarith [norm_nonneg w]
  set ρ : ℝ := ε/2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hρlt : ρ < ε := by rw [hρdef]; linarith
  set P1 : EuclideanSpace ℝ (Fin n) := y + ρ • v with hP1def
  set P2 : EuclideanSpace ℝ (Fin n) := y + ρ • w with hP2def
  set P3 : EuclideanSpace ℝ (Fin n) := y - ρ • v with hP3def
  have hP1ball : P1 ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, dist_eq_norm, hP1def]
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le, hvnorm, mul_one]
    exact hρlt
  have hP2ball : P2 ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, dist_eq_norm, hP2def]
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ.le, hwnorm, mul_one]
    exact hρlt
  have hP3ball : P3 ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, dist_eq_norm, hP3def]
    have h : y - ρ • v - y = -(ρ • v) := by abel
    rw [h, norm_neg, norm_smul, Real.norm_of_nonneg hρ.le, hvnorm, mul_one]
    exact hρlt
  obtain ⟨a, haK, haP⟩ := hball hP1ball
  obtain ⟨b, hbK, hbP⟩ := hball hP3ball
  have hvP1 : ⟪v, P1⟫_ℝ = ⟪v, y⟫_ℝ + ρ := by
    rw [hP1def, inner_add_right, inner_smul_right, hvv, mul_one]
  have hvP3 : ⟪v, P3⟫_ℝ = ⟪v, y⟫_ℝ - ρ := by
    rw [hP3def, inner_sub_right, inner_smul_right, hvv, mul_one]
  have hP13 : P1 ≠ P3 := by
    intro h
    rw [h] at hvP1
    linarith
  have hwP1 : ⟪w, P1⟫_ℝ = ⟪w, y⟫_ℝ := by
    rw [hP1def, inner_add_right, inner_smul_right, hwv, mul_zero, add_zero]
  have hwP3 : ⟪w, P3⟫_ℝ = ⟪w, y⟫_ℝ := by
    rw [hP3def, inner_sub_right, inner_smul_right, hwv, mul_zero, sub_zero]
  have hwP2 : ⟪w, P2⟫_ℝ = ⟪w, y⟫_ℝ + ρ := by
    rw [hP2def, inner_add_right, inner_smul_right, hww, mul_one]
  set arc1 : Set (EuclideanSpace ℝ (Fin n)) := segment ℝ P1 P3 with harc1def
  set arc2 : Set (EuclideanSpace ℝ (Fin n)) := segment ℝ P1 P2 ∪ segment ℝ P2 P3 with harc2def
  -- the two arcs meet exactly in the two endpoints
  have harc_inter : arc1 ∩ arc2 = {P1, P3} := by
    rw [harc1def, harc2def]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_union, segment, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨a1, b1, ha1, hb1, hab1, hz1⟩,
        (⟨a2, b2, ha2, hb2, hab2, hz2⟩ | ⟨a2, b2, ha2, hb2, hab2, hz2⟩)⟩
      · have hz1' : ⟪w, z⟫_ℝ = ⟪w, y⟫_ℝ := by
          rw [← hz1, inner_add_right, inner_smul_right, inner_smul_right, hwP1, hwP3,
            ← add_mul, hab1, one_mul]
        have hz2' : ⟪w, z⟫_ℝ = a2 * ⟪w, y⟫_ℝ + b2 * (⟪w, y⟫_ℝ + ρ) := by
          rw [← hz2, inner_add_right, inner_smul_right, inner_smul_right, hwP1, hwP2]
        have hb2ρ : b2 * ρ = 0 := by
          have h1 : a2 * ⟪w, y⟫_ℝ + b2 * (⟪w, y⟫_ℝ + ρ) = ⟪w, y⟫_ℝ := hz2'.symm.trans hz1'
          have h2 : b2 * ρ = a2 * ⟪w, y⟫_ℝ + b2 * (⟪w, y⟫_ℝ + ρ) - ⟪w, y⟫_ℝ
              - (a2 + b2 - 1) * ⟪w, y⟫_ℝ := by ring
          rw [h1, hab2] at h2
          simpa using h2
        have hb2 : b2 = 0 := mul_eq_zero.mp hb2ρ |>.elim id (fun h => absurd h (ne_of_gt hρ))
        have ha2 : a2 = 1 := by linarith
        left
        rw [← hz2, hb2, ha2]; simp
      · have hz1' : ⟪w, z⟫_ℝ = ⟪w, y⟫_ℝ := by
          rw [← hz1, inner_add_right, inner_smul_right, inner_smul_right, hwP1, hwP3,
            ← add_mul, hab1, one_mul]
        have hz2' : ⟪w, z⟫_ℝ = a2 * (⟪w, y⟫_ℝ + ρ) + b2 * ⟪w, y⟫_ℝ := by
          rw [← hz2, inner_add_right, inner_smul_right, inner_smul_right, hwP2, hwP3]
        have ha2ρ : a2 * ρ = 0 := by
          have h1 : a2 * (⟪w, y⟫_ℝ + ρ) + b2 * ⟪w, y⟫_ℝ = ⟪w, y⟫_ℝ := hz2'.symm.trans hz1'
          have h2 : a2 * ρ = a2 * (⟪w, y⟫_ℝ + ρ) + b2 * ⟪w, y⟫_ℝ - ⟪w, y⟫_ℝ
              - (a2 + b2 - 1) * ⟪w, y⟫_ℝ := by ring
          rw [h1, hab2] at h2
          simpa using h2
        have ha2 : a2 = 0 := mul_eq_zero.mp ha2ρ |>.elim id (fun h => absurd h (ne_of_gt hρ))
        have hb2 : b2 = 1 := by linarith
        right
        rw [← hz2, ha2, hb2]; simp
    · intro hz
      rcases hz with hz | hz
      · rw [hz]; exact ⟨left_mem_segment ℝ P1 P3, Or.inl (left_mem_segment ℝ P1 P2)⟩
      · rw [hz]; exact ⟨right_mem_segment ℝ P1 P3, Or.inr (right_mem_segment ℝ P2 P3)⟩
  have harc1_pre : IsPreconnected arc1 := by
    rw [harc1def]; exact (convex_segment P1 P3).isPreconnected
  have harc2_pre : IsPreconnected arc2 := by
    rw [harc2def]
    refine IsPreconnected.union' ⟨P2, right_mem_segment ℝ P1 P2, left_mem_segment ℝ P2 P3⟩ ?_ ?_
    · exact (convex_segment P1 P2).isPreconnected
    · exact (convex_segment P2 P3).isPreconnected
  have harc1_sub : arc1 ⊆ γ '' K := by
    rw [harc1def]
    exact subset_trans ((convex_ball y ε).segment_subset hP1ball hP3ball) hball
  have harc2_sub : arc2 ⊆ γ '' K := by
    rw [harc2def]
    intro z hz
    rcases hz with hz | hz
    · exact hball ((convex_ball y ε).segment_subset hP1ball hP2ball hz)
    · exact hball ((convex_ball y ε).segment_subset hP2ball hP3ball hz)
  have hA : IsPreconnected (K ∩ γ ⁻¹' arc1) :=
    preconnected_preimage_of_compact hK hcont hinj harc1_pre harc1_sub
  have hB : IsPreconnected (K ∩ γ ⁻¹' arc2) :=
    preconnected_preimage_of_compact hK hcont hinj harc2_pre harc2_sub
  have hAord : (K ∩ γ ⁻¹' arc1).OrdConnected := isPreconnected_iff_ordConnected.mp hA
  have hBord : (K ∩ γ ⁻¹' arc2).OrdConnected := isPreconnected_iff_ordConnected.mp hB
  have hint_ord : ((K ∩ γ ⁻¹' arc1) ∩ (K ∩ γ ⁻¹' arc2)).OrdConnected := hAord.inter hBord
  have haA : a ∈ K ∩ γ ⁻¹' arc1 := ⟨haK, by
    simp only [Set.mem_preimage]; rw [haP, harc1def]; exact left_mem_segment ℝ P1 P3⟩
  have haB : a ∈ K ∩ γ ⁻¹' arc2 := ⟨haK, by
    simp only [Set.mem_preimage]; rw [haP, harc2def]; exact Or.inl (left_mem_segment ℝ P1 P2)⟩
  have hbA : b ∈ K ∩ γ ⁻¹' arc1 := ⟨hbK, by
    simp only [Set.mem_preimage]; rw [hbP, harc1def]; exact right_mem_segment ℝ P1 P3⟩
  have hbB : b ∈ K ∩ γ ⁻¹' arc2 := ⟨hbK, by
    simp only [Set.mem_preimage]; rw [hbP, harc2def]; exact Or.inr (right_mem_segment ℝ P2 P3)⟩
  have hane : a ≠ b := by
    intro h
    exact hP13 (by rw [← haP, h, hbP])
  have haI : a ∈ (K ∩ γ ⁻¹' arc1) ∩ (K ∩ γ ⁻¹' arc2) := ⟨haA, haB⟩
  have hbI : b ∈ (K ∩ γ ⁻¹' arc1) ∩ (K ∩ γ ⁻¹' arc2) := ⟨hbA, hbB⟩
  have huicc : Set.uIcc a b ⊆ (K ∩ γ ⁻¹' arc1) ∩ (K ∩ γ ⁻¹' arc2) :=
    hint_ord.uIcc_subset haI hbI
  have hm : (a+b)/2 ∈ Set.uIcc a b := by
    rw [Set.mem_uIcc]
    rcases le_total a b with hab | hba
    · exact Or.inl ⟨by linarith, by linarith⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  have hmI := huicc hm
  have hmarc : γ ((a+b)/2) ∈ arc1 ∩ arc2 := ⟨hmI.1.2, hmI.2.2⟩
  rw [harc_inter] at hmarc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmarc
  rcases hmarc with h | h
  · have h2 : (a+b)/2 = a := hinj hmI.1.1 haK (by rw [h, haP])
    have h3 : b = a := by linarith
    exact hane h3.symm
  · have h2 : (a+b)/2 = b := hinj hmI.1.1 hbK (by rw [h, hbP])
    have h3 : a = b := by linarith
    exact hane h3

/-- **The image of a compact arc has empty interior in an `n`-manifold, `n ≥ 2`.**

For `γ : ℝ → M` continuous and injective on `[0,1]` in a topological `n`-manifold (`n ≥ 2`), the
image `γ '' Icc 0 1` has empty interior.  (Equivalently: an open ball in `ℝ^n`, `n ≥ 2`, cannot be
embedded into `ℝ`, since such a ball minus a point is connected while a subset of `ℝ` minus a point
has at most two connected components.  The `n = 2` case already exists as
`Work.Whitney.PathTools.arc_interior_empty_surface`.) -/
theorem arc_interior_empty {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {γ : ℝ → M} (hγ : Continuous γ) (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1)) :
    interior (γ '' Set.Icc (0:ℝ) 1) = ∅ := by
  classical
  set A : Set M := γ '' Set.Icc (0:ℝ) 1 with hA
  by_contra hne
  have hne' : (interior A).Nonempty := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨p, hpint⟩ := hne'
  -- a chart at `p`
  set e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) p with he
  have hp_src : p ∈ e.source := mem_chart_source _ p
  -- the nonempty open set `C = interior A` and its chart piece `W`
  set C : Set M := interior A with hC
  have hCopen : IsOpen C := isOpen_interior
  have hCA : C ⊆ A := interior_subset
  set W : Set M := C ∩ e.source with hW
  have hWopen : IsOpen W := hCopen.inter e.open_source
  have hpW : p ∈ W := ⟨hpint, hp_src⟩
  have hWe : W ⊆ e.source := inter_subset_right
  have hWA : W ⊆ A := (inter_subset_left).trans hCA
  set U : Set (EuclideanSpace ℝ (Fin n)) := e '' W with hU
  have hUopen : IsOpen U := e.isOpen_image_of_subset_source hWopen hWe
  have hpU : e p ∈ U := ⟨p, hpW, rfl⟩
  have hUtarget : U ⊆ e.target := by
    rw [hU]
    calc e '' W ⊆ e '' e.source := Set.image_mono hWe
      _ = e.target := OpenPartialHomeomorph.image_source_eq_target e
  -- a closed ball inside `U`
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hpU)
  set ε : ℝ := δ / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hball : Metric.closedBall (e p) ε ⊆ U :=
    (Metric.closedBall_subset_ball (show ε < δ by rw [hεdef]; linarith)).trans hδsub
  have hDtarget : Metric.closedBall (e p) ε ⊆ e.target := hball.trans hUtarget
  -- the disc, pulled back to `M`
  set D : Set M := e.symm '' Metric.closedBall (e p) ε with hD
  have hDmem : ∀ x : M, x ∈ D ↔ x ∈ e.source ∧ e x ∈ Metric.closedBall (e p) ε := by
    intro x
    rw [hD]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzsrc : z ∈ e.symm.source := by
        rw [OpenPartialHomeomorph.symm_source]; exact hDtarget hz
      exact ⟨by rw [← OpenPartialHomeomorph.symm_target]; exact e.symm.map_source hzsrc,
        by rw [e.right_inv hzsrc]; exact hz⟩
    · rintro ⟨hxs, hxe⟩
      exact ⟨e x, hxe, e.left_inv hxs⟩
  have hDsub : D ⊆ e.source := fun x hx => ((hDmem x).1 hx).1
  have hDcompact : IsCompact D := by
    rw [hD]
    refine (isCompact_closedBall (e p) ε).image_of_continuousOn ?_
    exact e.symm.continuousOn.mono
      (by rw [OpenPartialHomeomorph.symm_source]; exact hDtarget)
  have hDclosed : IsClosed D := hDcompact.isClosed
  -- every point of the disc lies on the arc
  have hDA : D ⊆ A := by
    intro x hx
    obtain ⟨hxsrc, hxball⟩ := (hDmem x).1 hx
    have hxU : e x ∈ U := hball hxball
    rw [hU] at hxU
    obtain ⟨w, hwW, hwx⟩ := hxU
    have hxw : x = w := e.injOn hxsrc hwW.2 hwx.symm
    rw [hxw]
    exact hWA hwW
  -- the compact set of parameters of arc points mapped into the disc
  set T : Set ℝ := Set.Icc (0:ℝ) 1 ∩ γ ⁻¹' D with hT
  have hTclosed : IsClosed T := by
    rw [hT]; exact isClosed_Icc.inter (hDclosed.preimage hγ)
  have hTcompact : IsCompact T :=
    IsCompact.of_isClosed_subset isCompact_Icc hTclosed (by rw [hT]; exact inter_subset_left)
  have hTsrc : ∀ t ∈ T, γ t ∈ e.source := fun t ht => by
    rw [hT] at ht
    exact ((hDmem (γ t)).1 ht.2).1
  have hTI : ∀ t ∈ T, t ∈ Set.Icc (0:ℝ) 1 := fun t ht => by
    rw [hT] at ht
    exact ht.1
  have hcont : ContinuousOn (fun t => e (γ t)) T :=
    e.continuousOn.comp hγ.continuousOn hTsrc
  have hinjE : Set.InjOn (fun t => e (γ t)) T := by
    intro t₁ ht₁ t₂ ht₂ h
    exact hinj (hTI t₁ ht₁) (hTI t₂ ht₂) (e.injOn (hTsrc t₁ ht₁) (hTsrc t₂ ht₂) h)
  -- the image of that parameter set is exactly the closed ball
  have hImage : (fun t => e (γ t)) '' T = Metric.closedBall (e p) ε := by
    apply subset_antisymm
    · rintro z ⟨t, ht, rfl⟩
      rw [hT] at ht
      exact ((hDmem (γ t)).1 ht.2).2
    · intro z hz
      have hzU : z ∈ U := hball hz
      rw [hU] at hzU
      obtain ⟨w, hwW, hwz⟩ := hzU
      have hwA : w ∈ A := hWA hwW
      rw [hA] at hwA
      obtain ⟨t, htI, htw⟩ := hwA
      refine ⟨t, ?_, ?_⟩
      · rw [hT]
        refine ⟨htI, ?_⟩
        show γ t ∈ D
        rw [htw]
        exact (hDmem w).2 ⟨hwW.2, by rw [hwz]; exact hz⟩
      · show e (γ t) = z
        rw [htw, hwz]
  -- but a closed ball of positive radius has nonempty interior
  have hempty : interior (Metric.closedBall (e p) ε) = ∅ := by
    rw [← hImage]
    exact interior_image_arc_empty_euclidean hn hTcompact hcont hinjE
  have hne'' : (interior (Metric.closedBall (e p) ε)).Nonempty :=
    ⟨e p, Metric.ball_subset_interior_closedBall (Metric.mem_ball_self hε)⟩
  rw [hempty] at hne''
  exact Set.not_nonempty_empty hne''

end Work.Noncompact.Canals
