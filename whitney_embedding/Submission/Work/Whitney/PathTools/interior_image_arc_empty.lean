import Mathlib
import Submission.Work.Whitney.PathTools.joinedIn_compl_of_arc_plane
import Submission.Work.Whitney.PathTools.local_room_image_open_of_injOn

/-!
# The image of a compact subset of `ℝ` under an injective curve has empty interior

For `K ⊆ ℝ` compact and `γ : ℝ → ℝ²` continuous and injective on `K`, the image `γ '' K` has empty
interior.

The proof reduces to the non-existence of a topological disc inside `ℝ`.  If some ball
`ball y ε ⊆ γ '' K`, then with the two orthogonal unit vectors `v = (1,0)`, `w = (0,1)` the four
points `P₁ = y + ρ v`, `P₃ = y - ρ v`, `P₂ = y + ρ w` (`ρ = ε/2`) all lie in the ball, hence in
`γ '' K`.  The two "arcs"

* `arc₁ = segment P₁ P₃` (the straight segment), and
* `arc₂ = segment P₁ P₂ ∪ segment P₂ P₃` (a detour through `P₂`)

are connected and meet exactly in `{P₁, P₃}` (the linear functional `z ↦ ⟪w, z⟫` separates the
straight segment from the detour).  Since `γ` is a homeomorphism onto its image (continuous
injective on the compact `K`), the preimages `K ∩ γ ⁻¹' arc₁` and `K ∩ γ ⁻¹' arc₂` are connected
subsets of `ℝ`, hence intervals (`OrdConnected`); their intersection is at once an interval and the
two point set `{a, b}` where `a`, `b` are the preimages of `P₁`, `P₃` — a contradiction, because a
two point set with two distinct points is not `OrdConnected`.
-/

open scoped InnerProductSpace
open Set

namespace Work.Whitney.PathTools

/-- If `γ` is continuous and injective on the compact set `K ⊆ ℝ` and `T ⊆ γ '' K` is
(pre)connected, then `K ∩ γ ⁻¹' T` is (pre)connected.

This is the `IsInducing`/closed–map transfer of connectedness along the topological embedding
`γ|_K : K → ℝ²`. -/
private lemma preconnected_preimage_of_compact
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {K : Set ℝ} (hK : IsCompact K)
    (hcont : ContinuousOn γ K) (hinj : Set.InjOn γ K)
    {T : Set (EuclideanSpace ℝ (Fin 2))} (hT : IsPreconnected T) (hTsub : T ⊆ γ '' K) :
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

theorem interior_image_arc_empty
    {γ : ℝ → EuclideanSpace ℝ (Fin 2)} {K : Set ℝ} (hK : IsCompact K)
    (hcont : ContinuousOn γ K) (hinj : Set.InjOn γ K) :
    interior (γ '' K) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro y hy
  rw [mem_interior_iff_mem_nhds] at hy
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hy
  set v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (1:ℝ) with hv
  set w : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 (1:ℝ) with hw
  have hon : ∀ i j : Fin 2,
      ⟪EuclideanSpace.single i (1:ℝ), EuclideanSpace.single j (1:ℝ)⟫_ℝ = if i = j then 1 else 0 :=
    (orthonormal_iff_ite.mp EuclideanSpace.orthonormal_single)
  have hvv : ⟪v, v⟫_ℝ = 1 := by rw [hv]; simpa using hon 0 0
  have hwv : ⟪w, v⟫_ℝ = 0 := by rw [hw, hv]; simpa using hon 1 0
  have hww : ⟪w, w⟫_ℝ = 1 := by rw [hw]; simpa using hon 1 1
  have hvnorm : ‖v‖ = 1 := by
    have h2 : ‖v‖^2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hvv
    nlinarith [norm_nonneg v]
  have hwnorm : ‖w‖ = 1 := by
    have h2 : ‖w‖^2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hww
    nlinarith [norm_nonneg w]
  set ρ : ℝ := ε/2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  have hρlt : ρ < ε := by rw [hρdef]; linarith
  set P1 : EuclideanSpace ℝ (Fin 2) := y + ρ • v with hP1def
  set P2 : EuclideanSpace ℝ (Fin 2) := y + ρ • w with hP2def
  set P3 : EuclideanSpace ℝ (Fin 2) := y - ρ • v with hP3def
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
  set arc1 : Set (EuclideanSpace ℝ (Fin 2)) := segment ℝ P1 P3 with harc1def
  set arc2 : Set (EuclideanSpace ℝ (Fin 2)) := segment ℝ P1 P2 ∪ segment ℝ P2 P3 with harc2def
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

end Work.Whitney.PathTools
