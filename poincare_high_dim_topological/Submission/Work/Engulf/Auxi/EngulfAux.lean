import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Auxi.SimplexCover
import Submission.Work.Engulf.Auxi.Carrier
import Submission.Work.Engulf.Auxi.SubdivCard
import Submission.Work.Cells.Connell.extOverDisc_of_homeomorph
import Submission.Work.Cells.Connell.meshLT_dist_lt

/-!
# A9 aux: elementary consequences of the A9 definitions (area for `E2`)

* uniform continuity on the space of a finite complex, and the resulting choice of subdivision;
* margins of a compact set from a disjoint closed set;
* transport of the ambient hypotheses `Amb` across a homeomorphism of the ambient space;
* a few cardinality consequences of the carrier lemma for faces of a subdivision.
-/

open Set Metric PL Finset

namespace Work.Engulf

variable {N : ℕ} {M : Type*} [MetricSpace M]

/-! ## Uniform continuity and fineness -/

/-- Uniform continuity of a continuous map on the space of a finite complex. -/
theorem exists_mesh_dist_lt {K : Cx N} (hfin : K.faces.Finite) {f : E N → M}
    (hf : ContinuousOn f K.space) {δ : ℝ} (hδ : 0 < δ) :
    ∃ δ' > 0, ∀ x ∈ K.space, ∀ y ∈ K.space, dist x y < δ' → dist (f x) (f y) < δ :=
  Metric.uniformContinuousOn_iff.1
    ((isCompact_space hfin).uniformContinuousOn_of_continuous hf) δ hδ

/-- The subdivision is fine enough that every face meeting `Z` is mapped into `V`. -/
theorem exists_subdiv_faces_map_into (S : SubdivTools N) {Γ : Cx N} (hfin : Γ.faces.Finite)
    {f : E N → M} (hf : ContinuousOn f Γ.space) {V : Set M} (hV : IsOpen V) {Z : Set (E N)}
    (hZc : IsCompact Z) (hZ : Z ⊆ Γ.space) (hZV : f '' Z ⊆ V) :
    ∃ r, ∀ r' ≥ r, ∀ s ∈ (S.sdIter r' Γ hfin).faces, (simp s ∩ Z).Nonempty → f '' simp s ⊆ V := by
  have hcomp : IsCompact (f '' Z) := hZc.image_of_continuousOn (hf.mono hZ)
  obtain ⟨δ, hδ, hδV⟩ := hcomp.exists_cthickening_subset_open hV hZV
  obtain ⟨δ', hδ', huc⟩ := exists_mesh_dist_lt hfin hf hδ
  obtain ⟨r, hr⟩ := S.fine Γ hfin δ' hδ'
  refine ⟨r, fun r' hr' s hs hmeet => ?_⟩
  rw [Set.image_subset_iff]
  obtain ⟨y, hy⟩ := hmeet
  have hyZ : y ∈ Z := hy.2
  have hyΓ : y ∈ Γ.space := (S.subdiv r' Γ hfin).1 ▸
    (Geometry.SimplicialComplex.convexHull_subset_space hs hy.1)
  intro x hx
  have hxΓ : x ∈ Γ.space := (S.subdiv r' Γ hfin).1 ▸
    (Geometry.SimplicialComplex.convexHull_subset_space hs hx)
  have hxy : dist x y < δ' :=
    Work.Cells.Connell.meshLT_dist_lt (hr r' hr') hs hx hy.1
  have hd : dist (f x) (f y) < δ := huc x hxΓ y hyΓ hxy
  have : f x ∈ Metric.cthickening δ (f '' Z) :=
    Metric.mem_cthickening_of_dist_le (f x) (f y) δ (f '' Z) ⟨y, hyZ, rfl⟩ (le_of_lt hd)
  exact hδV this

/-! ## Margins -/

/-- Positive distance between a compact set and a disjoint closed set. -/
theorem exists_pos_le_dist_of_isCompact_disjoint {K F : Set M} (hK : IsCompact K) (hF : IsClosed F)
    (hd : Disjoint K F) : ∃ ρ > 0, ∀ z ∈ K, ∀ y ∈ F, ρ ≤ dist z y := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hF.isOpen_compl (by
    intro x hx hxF; exact hd.le_bot ⟨hx, hxF⟩)
  refine ⟨δ, hδ, fun z hz y hy => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  exact hsub (Metric.mem_cthickening_of_dist_le y z δ K hz (by rw [dist_comm]; exact le_of_lt hcon)) hy

/-! ## Compactly supported homeomorphisms -/

theorem csupp_trans {h₁ h₂ : M ≃ₜ M} (H₁ : CSupp h₁ univ) (H₂ : CSupp h₂ univ) :
    CSupp (h₁.trans h₂) univ := by
  obtain ⟨C₁, hC₁, -, h₁id⟩ := H₁
  obtain ⟨C₂, hC₂, -, h₂id⟩ := H₂
  refine ⟨C₁ ∪ h₁.symm '' C₂, hC₁.union (hC₂.image h₁.symm.continuous), subset_univ _, ?_⟩
  intro x hx
  have hx1 : x ∉ C₁ := fun hc => hx (Or.inl hc)
  have hx2 : h₁ x ∉ C₂ := fun hc => hx (Or.inr ⟨h₁ x, hc, h₁.symm_apply_apply x⟩)
  rw [Homeomorph.trans_apply, h₂id _ hx2, h₁id _ hx1]

theorem image_trans_image (h₁ h₂ : M ≃ₜ M) (V : Set M) :
    (h₁.trans h₂) '' V = h₂ '' (h₁ '' V) := by
  ext x; constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨h₁ y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩

/-- The ambient hypotheses transport across a homeomorphism of the ambient space. -/
theorem Amb.image_homeomorph {n p : ℕ} {V : Set M} (h : M ≃ₜ M) (A : Amb n p M V) :
    Amb n p M (h '' V) where
  hp := A.hp
  loc := A.loc
  connM := A.connM
  Vo := h.isOpen_image.2 A.Vo
  Vne := A.Vne.image h
  connV := fun j hj =>
    Work.Cells.Connell.extOverDisc_of_homeomorph (h.image V) (A.connV j hj)

/-! ## Compactness of the intersection with a closed set -/

theorem isCompact_inter_preimage {Γ : Cx N} (hfin : Γ.faces.Finite) {f : E N → M}
    (hf : ContinuousOn f Γ.space) {H : Set (E N)} (hH : IsCompact H) (hHsub : H ⊆ Γ.space)
    {X : Set M} (hX : IsClosed X) : IsCompact (H ∩ f ⁻¹' X) := by
  have h1 : IsClosed (Γ.space ∩ f ⁻¹' X) :=
    hf.preimage_isClosed_of_isClosed (isClosed_space hfin) hX
  have h2 : H ∩ f ⁻¹' X = H ∩ (Γ.space ∩ f ⁻¹' X) := by
    ext x; constructor
    · intro hx; exact ⟨hx.1, hHsub hx.1, hx.2⟩
    · intro hx; exact ⟨hx.1, hx.2.2⟩
  rw [h2]
  exact hH.inter_right h1

/-! ## Cardinality of faces of a subdivision -/

/-- Faces of a subdivision contained in `H` have at most `d + 1` vertices if the coarse faces inside
`H` do. -/
theorem card_le_of_isSubSp (S : SubdivTools N) {r : ℕ} {K : Cx N} {hK : K.faces.Finite}
    {H : Set (E N)} {d : ℕ} (hH : IsSubSp K H)
    (hdim : ∀ σ ∈ K.faces, simp σ ⊆ H → σ.card ≤ d + 1)
    {s : Finset (E N)} (hs : s ∈ (S.sdIter r K hK).faces) (hsH : simp s ⊆ H) :
    s.card ≤ d + 1 := by
  obtain ⟨τ, hτK, hτH, hτs⟩ := exists_coarse_face_of_simp_subset S hH hs hsH
  exact le_trans (card_le_of_simp_subset S hs hτK hτs) (hdim τ hτK hτH)

/-- Faces of a subdivision contained in `H` whose image is not contained in `V` have at most `k + 1`
vertices if the same is true for the coarse faces. -/
theorem card_le_of_not_maps (S : SubdivTools N) {r : ℕ} {K : Cx N} {hK : K.faces.Finite}
    {H : Set (E N)} {f : E N → M} {V : Set M} {k : ℕ} (hH : IsSubSp K H)
    (hBad : BadCard K H f V (k + 1)) {s : Finset (E N)} (hs : s ∈ (S.sdIter r K hK).faces)
    (hsH : simp s ⊆ H) (hsV : ¬ (f '' simp s ⊆ V)) : s.card ≤ k + 1 := by
  obtain ⟨τ, hτK, hτH, hτs⟩ := exists_coarse_face_of_simp_subset S hH hs hsH
  have hτV : ¬ (f '' simp τ ⊆ V) := fun h => hsV (Subset.trans (Set.image_mono hτs) h)
  exact le_trans (card_le_of_simp_subset S hs hτK hτs) (hBad τ hτK hτH hτV)

/-- `OvCtl` is monotone in the engulfed part. -/
theorem OvCtl.mono {V X : Set M} {H H' L : Set (E N)} {f : E N → M} (hHH : H' ⊆ H)
    (h : OvCtl V X H L f) : OvCtl V X H' L f := by
  obtain ⟨C, hC, hCV, h1, h2⟩ := h
  exact ⟨C, hC, hCV, fun x hx y hy => h1 x ⟨hHH hx.1, hx.2⟩ y ⟨hHH hy.1, hy.2⟩,
    fun x hx => h2 x ⟨hHH hx.1, hx.2⟩⟩

end Work.Engulf
