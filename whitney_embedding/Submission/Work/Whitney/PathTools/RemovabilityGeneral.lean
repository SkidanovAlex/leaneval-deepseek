import Mathlib
import Submission.Work.Whitney.PathTools.TotallyDisconnectedPlane

/-!
# Zero-dimensional removability in a general inner product space

The planar theorem (`Work.Whitney.PathTools.Grid.compl_totallyDisconnected_plane`) is lifted to an
arbitrary finite dimensional real inner product space `E` of dimension `≥ 2`, by intersecting the
situation with a `2`-plane through the two points: the plane is parametrised by a linear isometry
`Φ : ℝ² → E`, and the preimage of the compact totally disconnected set under `x + Φ` is again
compact and totally disconnected.

Main statements:
* `joinedIn_compl_of_isCompact_isTotallyDisconnected_gen` (`JoinedIn` form),
* `compl_isCompact_isTotallyDisconnected_pathConnected_gen` (`IsPathConnected` form).
-/

namespace Work.Whitney.PathTools

open Set Metric Topology
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Total disconnectedness is preserved by homeomorphisms (direct image). -/
lemma isTotallyDisconnected_image_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) {K : Set X} (hK : IsTotallyDisconnected K) :
    IsTotallyDisconnected (h '' K) := by
  intro S hS hSpre
  have h2 : h ⁻¹' S ⊆ K := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hS hx
    have : x = y := h.injective hxy.symm
    rwa [this]
  have h6 : h '' (h ⁻¹' S) = S := by
    refine Subset.antisymm ?_ ?_
    · rintro z ⟨x, hx, rfl⟩; exact hx
    · intro z hz
      obtain ⟨x, hxK, hxz⟩ := hS hz
      exact ⟨x, by simpa [hxz] using hz, hxz⟩
  have h5 : IsPreconnected (h ⁻¹' S) := by
    have h7 : IsPreconnected (h '' (h ⁻¹' S)) := by rw [h6]; exact hSpre
    exact (Topology.IsInducing.isPreconnected_image (f := ⇑h) (s := h ⁻¹' S) h.isInducing).mp h7
  have hd : (h ⁻¹' S).Subsingleton := hK _ h2 h5
  intro a ha b hb
  obtain ⟨x, hxK, rfl⟩ := hS ha
  obtain ⟨y, hyK, hyb⟩ := hS hb
  have hx' : x ∈ h ⁻¹' S := ha
  have hy' : y ∈ h ⁻¹' S := by simpa [hyb] using hb
  have hxy : x = y := hd hx' hy'
  rw [← hyb, hxy]

/-- Total disconnectedness is preserved by homeomorphisms (inverse image). -/
lemma isTotallyDisconnected_preimage_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) {K : Set Y} (hK : IsTotallyDisconnected K) :
    IsTotallyDisconnected (h ⁻¹' K) := by
  have h1 : h.symm '' K = h ⁻¹' K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; simpa using hy
    · intro hx; exact ⟨h x, hx, h.symm_apply_apply x⟩
  rw [← h1]
  exact isTotallyDisconnected_image_homeomorph h.symm hK

/-- In a real inner product space of dimension `≥ 2`, a unit vector has an orthogonal unit
vector. -/
lemma exists_orthogonal_unit_vector_gen [FiniteDimensional ℝ E] (hrank : 2 ≤ Module.finrank ℝ E)
    {u : E} (hu : ‖u‖ = 1) : ∃ w : E, ‖w‖ = 1 ∧ ⟪u, w⟫_ℝ = 0 := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  have h1 : Module.finrank ℝ ↥(Submodule.span ℝ {u}) = 1 := finrank_span_singleton hu0
  have h2 := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (Submodule.span ℝ {u})
  have h3 : 0 < Module.finrank ℝ ↥((Submodule.span ℝ {u})ᗮ) := by omega
  haveI : Nontrivial ↥((Submodule.span ℝ {u})ᗮ) := Module.nontrivial_of_finrank_pos h3
  obtain ⟨b, hb⟩ : ∃ b : ↥((Submodule.span ℝ {u})ᗮ), b ≠ 0 := exists_ne 0
  have hbn : 0 < ‖(b : E)‖ := norm_pos_iff.mpr (by simpa using hb)
  have hu_mem : u ∈ (Submodule.span ℝ {u} : Submodule ℝ E) :=
    Submodule.subset_span (mem_singleton u)
  have horth : ⟪u, (b : E)⟫_ℝ = 0 := (Submodule.mem_orthogonal _ _).mp b.property u hu_mem
  refine ⟨‖(b : E)‖⁻¹ • (b : E), ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ (ne_of_gt hbn)]
  · rw [inner_smul_right, horth, mul_zero]

/-- The linear isometry `ℝ² → E` spanned by an orthonormal pair. -/
lemma exists_linearIsometry_pair_gen {u w : E} (hu : ‖u‖ = 1) (hw1 : ‖w‖ = 1)
    (hw2 : ⟪u, w⟫_ℝ = 0) :
    ∃ Φ : EuclideanSpace ℝ (Fin 2) →ₗᵢ[ℝ] E, ∀ p, Φ p = p 0 • u + p 1 • w := by
  let L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] E :=
    { toFun := fun p => p 0 • u + p 1 • w
      map_add' := by
        intro p q
        simp only [PiLp.add_apply, add_smul]
        abel
      map_smul' := by
        intro c p
        simp only [PiLp.smul_apply, smul_add, smul_smul, RingHom.id_apply]
        congr 1 <;> rw [mul_comm] }
  have hLn : ∀ p, ‖L p‖ = ‖p‖ := by
    intro p
    have hcross : ⟪p 0 • u, p 1 • w⟫_ℝ = 0 := by
      rw [inner_smul_left, inner_smul_right, hw2, mul_zero]
      simp
    have hx : ‖p 0 • u‖ = |p 0| := by rw [norm_smul, Real.norm_eq_abs, hu, mul_one]
    have hy : ‖p 1 • w‖ = |p 1| := by rw [norm_smul, Real.norm_eq_abs, hw1, mul_one]
    have hpn : ‖p‖ = Real.sqrt ((p 0) ^ 2 + (p 1) ^ 2) := by
      rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
      congr 1
      norm_num
    have hsq : ‖L p‖ ^ 2 = ‖p‖ ^ 2 := by
      have hpy : ‖L p‖ ^ 2 = ‖p 0 • u‖ ^ 2 + ‖p 1 • w‖ ^ 2 := by
        have hLp : L p = p 0 • u + p 1 • w := rfl
        rw [hLp, norm_add_sq_real, hcross]; ring
      rw [hpy, hx, hy, hpn]
      rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (p 0) ^ 2 + (p 1) ^ 2)]
      rw [sq_abs, sq_abs]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · have hz : ‖p‖ = 0 := by linarith [norm_nonneg p, norm_nonneg (L p)]
      have hL0 : ‖L p‖ = 0 := by rw [h, hz, neg_zero]
      rw [hL0, hz]
  exact ⟨LinearIsometry.mk L hLn, fun p => rfl⟩

/-- **(R1)-gen.**  A compact totally disconnected subset of a real inner product space of
dimension `≥ 2` does not separate two of its complement's points. -/
theorem joinedIn_compl_of_isCompact_isTotallyDisconnected_gen [FiniteDimensional ℝ E]
    (hrank : 2 ≤ Module.finrank ℝ E) {K : Set E} (hK : IsCompact K)
    (htd : IsTotallyDisconnected K) {x y : E} (hx : x ∉ K) (hy : y ∉ K) :
    JoinedIn (Kᶜ) x y := by
  classical
  rcases eq_or_ne x y with rfl | hxy
  · exact JoinedIn.refl hx
  have hd : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  set u : E := ‖y - x‖⁻¹ • (y - x) with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, Real.norm_of_nonneg (by positivity),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hd)]
  obtain ⟨w, hw1, hw2⟩ := exists_orthogonal_unit_vector_gen hrank hu
  obtain ⟨Φ, hΦ⟩ := exists_linearIsometry_pair_gen hu hw1 hw2
  set f : EuclideanSpace ℝ (Fin 2) → E := fun p => x + Φ p with hfdef
  have hfcont : Continuous f := continuous_const.add Φ.continuous
  have hLinj : Function.Injective Φ := by
    intro p q hpq
    have hsub : Φ (p - q) = 0 := by rw [map_sub, hpq, sub_self]
    have hz : ‖p - q‖ = 0 := by
      rw [← Φ.norm_map (p - q), hsub, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  set K' : Set (EuclideanSpace ℝ (Fin 2)) := f ⁻¹' K with hK'def
  have hf_inj : Function.Injective f := by
    intro p q hpq
    exact hLinj (add_left_cancel hpq)
  have hK'closed : IsClosed K' := hK.isClosed.preimage hfcont
  have hK'bdd : Bornology.IsBounded K' := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).mp hK.isBounded
    refine (isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 2))).mpr ⟨R + ‖x‖, ?_⟩
    intro p hp
    have hpK : x + Φ p ∈ K := hp
    have h2 := hR hpK
    rw [Metric.mem_closedBall, dist_zero_right] at h2 ⊢
    have h3 : ‖p‖ = ‖Φ p‖ := (Φ.norm_map p).symm
    calc ‖p‖ = ‖Φ p‖ := h3
      _ = ‖(x + Φ p) - x‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖x + Φ p‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ R + ‖x‖ := by linarith
  haveI : ProperSpace E := FiniteDimensional.proper ℝ E
  haveI : ProperSpace (EuclideanSpace ℝ (Fin 2)) := FiniteDimensional.proper ℝ _
  have hK'cpt : IsCompact K' := isCompact_iff_isClosed_bounded.mpr ⟨hK'closed, hK'bdd⟩
  have hK'td : IsTotallyDisconnected K' := by
    have hsub : f '' K' ⊆ K := by rintro z ⟨p, hp, rfl⟩; exact hp
    have himg : IsTotallyDisconnected (f '' K') := fun t ht htp => htd t (ht.trans hsub) htp
    exact isTotallyDisconnected_of_image hfcont.continuousOn hf_inj himg
  have h0 : (0 : EuclideanSpace ℝ (Fin 2)) ∉ K' := by
    intro h
    exact hx (by simpa [hK'def, hfdef, Set.mem_preimage, map_zero, add_zero] using h)
  have hp1 : (WithLp.toLp 2 ![‖y - x‖, 0] : EuclideanSpace ℝ (Fin 2)) ∉ K' := by
    intro h
    apply hy
    have hval : Φ (WithLp.toLp 2 ![‖y - x‖, 0] : EuclideanSpace ℝ (Fin 2)) = y - x := by
      rw [hΦ]
      simp [hudef, smul_smul]
      rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hd), one_smul]
    simpa [hK'def, hfdef, Set.mem_preimage, hval] using h
  have hJ := Grid.joinedIn_compl_of_isCompact_isTotallyDisconnected hK'cpt hK'td h0 hp1
  have hmap : JoinedIn (f '' (K'ᶜ)) (f 0)
      (f (WithLp.toLp 2 ![‖y - x‖, 0] : EuclideanSpace ℝ (Fin 2))) :=
    hJ.map hfcont.continuousOn
  have hsub : f '' (K'ᶜ) ⊆ Kᶜ := by
    rintro z ⟨p, hp, rfl⟩
    simpa [hfdef, Set.mem_compl_iff, hK'def, Set.mem_preimage] using hp
  have hres := hmap.mono hsub
  have e1 : f 0 = x := by simp [hfdef, map_zero, add_zero]
  have e2 : f (WithLp.toLp 2 ![‖y - x‖, 0] : EuclideanSpace ℝ (Fin 2)) = y := by
    have hval : Φ (WithLp.toLp 2 ![‖y - x‖, 0] : EuclideanSpace ℝ (Fin 2)) = y - x := by
      rw [hΦ]
      simp [hudef, smul_smul]
      rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr hd), one_smul]
    simp [hfdef, hval, add_sub_cancel]
  rw [e1, e2] at hres
  exact hres

/-- Some point lies outside a compact subset of a nontrivial normed space. -/
theorem exists_notMem_of_isCompact_of_nontrivial {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hnt : Nontrivial F) {K : Set F} (hK : IsCompact K) : ∃ z, z ∉ K := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : F)).mp hK.isBounded
  obtain ⟨w, hw⟩ : ∃ w : F, w ≠ 0 := by
    obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
    exact ⟨a - b, sub_ne_zero.mpr hab⟩
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  refine ⟨((|R| + 1) / ‖w‖) • w, ?_⟩
  intro hmem
  have h1 := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ (ne_of_gt hwn)] at h1
  have h2 := le_abs_self R
  linarith

/-- **(R1)-gen**, `IsPathConnected` form. -/
theorem compl_isCompact_isTotallyDisconnected_pathConnected_gen [FiniteDimensional ℝ E]
    (hrank : 2 ≤ Module.finrank ℝ E) {K : Set E} (hK : IsCompact K)
    (htd : IsTotallyDisconnected K) : IsPathConnected (Kᶜ) := by
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
  obtain ⟨z, hz⟩ := exists_notMem_of_isCompact_of_nontrivial (F := E) inferInstance hK
  exact ⟨z, hz, fun y hy =>
    joinedIn_compl_of_isCompact_isTotallyDisconnected_gen hrank hK htd hz hy⟩

end Work.Whitney.PathTools
