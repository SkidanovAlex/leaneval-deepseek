import Mathlib
import Submission.Work.Surgery.Gluing
import Submission.Work.Surgery.Boundary
import Submission.Work.Surgery.GluingPointSet

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold Topology ContDiff
open Function Set

namespace Work.Surgery

noncomputable section

variable {n : ℕ}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace (n + 1)) N]

namespace GlueData

/-- `U ⊆ M` and `V ⊆ N` have the same trace on the two boundaries under the gluing
homeomorphism, i.e. `Sum.inl '' U ∪ Sum.inr '' V` is saturated for the gluing relation. -/
def Match (D : GlueData n M N) (U : Set M) (V : Set N) : Prop :=
  (∀ x : (𝓡∂ (n + 1)).boundary M, x.1 ∈ U → (D.φ x).1 ∈ V) ∧
  (∀ y : (𝓡∂ (n + 1)).boundary N, y.1 ∈ V →
    ∃ x : (𝓡∂ (n + 1)).boundary M, x.1 ∈ U ∧ (D.φ x).1 = y.1)

theorem match_empty (D : GlueData n M N) {U : Set M}
    (hU : ∀ x ∈ U, x ∉ (𝓡∂ (n + 1)).boundary M) : D.Match U ∅ :=
  ⟨fun x hx => absurd x.2 (hU x.1 hx), fun y hy => absurd hy (Set.notMem_empty y.1)⟩

theorem match_empty_right (D : GlueData n M N) {V : Set N}
    (hV : ∀ y ∈ V, y ∉ (𝓡∂ (n + 1)).boundary N) : D.Match ∅ V :=
  ⟨fun x hx => absurd hx (Set.notMem_empty x.1),
    fun y hy => absurd y.2 (hV y.1 hy)⟩

/-- For an open `U ⊆ M` there is an open `V ⊆ N` with `Match D U V`, namely a thickening of
`φ (U ∩ ∂M)`. -/
theorem exists_match (D : GlueData n M N) {U : Set M} (hU : IsOpen U) :
    ∃ V : Set N, IsOpen V ∧ D.Match U V := by
  obtain ⟨V, hVo, hVkey⟩ := exists_isOpen_inter_boundary (n := n) (X := N)
    (D.φ '' (Subtype.val ⁻¹' U)) (D.φ.isOpenMap _ (hU.preimage continuous_subtype_val))
  exact ⟨V, hVo, (fun x hx => (hVkey (D.φ x)).mpr ⟨x, hx, rfl⟩),
    (fun y hy => by
      obtain ⟨x, hx, hxy⟩ := (hVkey y).mp hy
      exact ⟨x, hx, congrArg Subtype.val hxy⟩)⟩

/-- The image in the glued space of a saturated open set is open. -/
theorem isOpen_gluing (D : GlueData n M N) {U : Set M} {V : Set N}
    (hU : IsOpen U) (hV : IsOpen V) (hm : D.Match U V) :
    IsOpen (D.q '' (Sum.inl '' U ∪ Sum.inr '' V)) := by
  rw [isOpen_coinduced]
  change IsOpen (D.q ⁻¹' (D.q '' (Sum.inl '' U ∪ Sum.inr '' V)))
  rw [D.preimage_image_eq hm.1 hm.2]
  exact (Topology.IsOpenEmbedding.inl.isOpenMap U hU).union
    (Topology.IsOpenEmbedding.inr.isOpenMap V hV)

/-- Two disjoint matching pairs of open sets give two disjoint open subsets of the glued space
containing the images of the given points. -/
theorem exists_sep_of_data (D : GlueData n M N) {U1 U2 : Set M} {V1 V2 : Set N}
    (hU1 : IsOpen U1) (hU2 : IsOpen U2) (hV1 : IsOpen V1) (hV2 : IsOpen V2)
    (hm1 : D.Match U1 V1) (hm2 : D.Match U2 V2)
    (hdM : Disjoint U1 U2) (hdN : Disjoint V1 V2)
    {a1 a2 : M ⊕ N}
    (ha1 : a1 ∈ Sum.inl '' U1 ∪ Sum.inr '' V1)
    (ha2 : a2 ∈ Sum.inl '' U2 ∪ Sum.inr '' V2) :
    ∃ G1 G2 : Set D.Glued, IsOpen G1 ∧ IsOpen G2 ∧ D.q a1 ∈ G1 ∧ D.q a2 ∈ G2 ∧
      Disjoint G1 G2 := by
  have hs2 : D.q ⁻¹' (D.q '' (Sum.inl '' U2 ∪ Sum.inr '' V2))
      = Sum.inl '' U2 ∪ Sum.inr '' V2 := D.preimage_image_eq hm2.1 hm2.2
  have hdisj : Disjoint (Sum.inl '' U1 ∪ Sum.inr '' V1) (Sum.inl '' U2 ∪ Sum.inr '' V2) := by
    rw [Set.disjoint_left]
    rintro z (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) (⟨b, hb, h⟩ | ⟨b, hb, h⟩)
    · exact (Set.disjoint_left.mp hdM) ha (Sum.inl.inj h ▸ hb)
    · exact absurd h Sum.inr_ne_inl
    · exact absurd h Sum.inl_ne_inr
    · exact (Set.disjoint_left.mp hdN) ha (Sum.inr.inj h ▸ hb)
  refine ⟨_, _, D.isOpen_gluing hU1 hV1 hm1, D.isOpen_gluing hU2 hV2 hm2,
    ⟨a1, ha1, rfl⟩, ⟨a2, ha2, rfl⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro z ⟨b1, hb1, rfl⟩ ⟨b2, hb2, hb2eq⟩
  have hb1' : b1 ∈ Sum.inl '' U2 ∪ Sum.inr '' V2 := by
    rw [← hs2]
    exact ⟨b2, hb2, hb2eq⟩
  exact (Set.disjoint_left.mp hdisj) hb1 hb1'

/-- Swap the two open sets in the conclusion. -/
theorem sep_symm (D : GlueData n M N) {A B : D.Glued}
    (h : ∃ G1 G2 : Set D.Glued, IsOpen G1 ∧ IsOpen G2 ∧ A ∈ G1 ∧ B ∈ G2 ∧
      Disjoint G1 G2) :
    ∃ G1 G2 : Set D.Glued, IsOpen G1 ∧ IsOpen G2 ∧ B ∈ G1 ∧ A ∈ G2 ∧
      Disjoint G1 G2 := by
  obtain ⟨G1, G2, h1, h2, hA, hB, hd⟩ := h
  exact ⟨G2, G1, h2, h1, hB, hA, hd.symm⟩

/-- The seam point corresponding to `y : ∂N`, represented on the `M` side. -/
theorem iotaM_phi_symm (D : GlueData n M N) (y : (𝓡∂ (n + 1)).boundary N) :
    D.ιM (D.φ.symm y).1 = D.ιN y.1 := by
  rw [D.ιM_eq_ιN (D.φ.symm y), congrArg Subtype.val (D.φ.apply_symm_apply y)]

end GlueData

section Helpers

variable [IsManifold (halfModel (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
variable [IsManifold (halfModel (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) N] [T2Space N]
variable (D : GlueData n M N)

/-- Two interior points of `M`. -/
theorem GlueData.sep_M_M {x1 x2 : M}
    (hx1 : x1 ∉ (𝓡∂ (n + 1)).boundary M) (hx2 : x2 ∉ (𝓡∂ (n + 1)).boundary M)
    (h : x1 ≠ x2) :
    ∃ G1 G2 : Set D.Glued, IsOpen G1 ∧ IsOpen G2 ∧
      D.ιM x1 ∈ G1 ∧ D.ιM x2 ∈ G2 ∧ Disjoint G1 G2 := by
  have hcM : IsClosed ((𝓡∂ (n + 1)).boundary M) := isClosed_bnd (n := n + 1) (M := M)
  obtain ⟨U1, U2, hU1, hU2, hx1U, hx2U, hdU⟩ := t2_separation h
  exact D.exists_sep_of_data (U1 := U1 ∩ ((𝓡∂ (n + 1)).boundary M)ᶜ)
    (U2 := U2 ∩ ((𝓡∂ (n + 1)).boundary M)ᶜ) (V1 := ∅) (V2 := ∅)
    (hU1.inter hcM.isOpen_compl) (hU2.inter hcM.isOpen_compl) isOpen_empty isOpen_empty
    (D.match_empty (fun z hz => hz.2)) (D.match_empty (fun z hz => hz.2))
    (Disjoint.mono inter_subset_left inter_subset_left hdU)
    (by rw [Set.disjoint_left]; rintro z hz; exact absurd hz (Set.notMem_empty z))
    (Or.inl ⟨x1, ⟨hx1U, hx1⟩, rfl⟩) (Or.inl ⟨x2, ⟨hx2U, hx2⟩, rfl⟩)

/-- Two interior points of `N`. -/
theorem GlueData.sep_N_N {y1 y2 : N}
    (hy1 : y1 ∉ (𝓡∂ (n + 1)).boundary N) (hy2 : y2 ∉ (𝓡∂ (n + 1)).boundary N)
    (h : y1 ≠ y2) :
    ∃ G1 G2 : Set D.Glued, IsOpen G1 ∧ IsOpen G2 ∧
      D.ιN y1 ∈ G1 ∧ D.ιN y2 ∈ G2 ∧ Disjoint G1 G2 := by
  have hcN : IsClosed ((𝓡∂ (n + 1)).boundary N) := isClosed_bnd (n := n + 1) (M := N)
  obtain ⟨V1, V2, hV1, hV2, hy1V, hy2V, hdV⟩ := t2_separation h
  exact D.exists_sep_of_data (U1 := ∅) (U2 := ∅)
    (V1 := V1 ∩ ((𝓡∂ (n + 1)).boundary N)ᶜ) (V2 := V2 ∩ ((𝓡∂ (n + 1)).boundary N)ᶜ)
    isOpen_empty isOpen_empty (hV1.inter hcN.isOpen_compl) (hV2.inter hcN.isOpen_compl)
    (D.match_empty_right (fun z hz => hz.2)) (D.match_empty_right (fun z hz => hz.2))
    (by rw [Set.disjoint_left]; rintro z hz; exact absurd hz (Set.notMem_empty z))
    (Disjoint.mono inter_subset_left inter_subset_left hdV)
    (Or.inr ⟨y1, ⟨hy1V, hy1⟩, rfl⟩) (Or.inr ⟨y2, ⟨hy2V, hy2⟩, rfl⟩)

/-- An interior point of `M` and an interior point of `N`. -/
theorem GlueData.sep_M_N {x : M} (hx : x ∉ (𝓡∂ (n + 1)).boundary M)
    {y : N} (hy : y ∉ (𝓡∂ (n + 1)).boundary N) :
    ∃ G1 G2 : Set D.Glued, IsOpen G1 ∧ IsOpen G2 ∧
      D.ιM x ∈ G1 ∧ D.ιN y ∈ G2 ∧ Disjoint G1 G2 := by
  have hcM : IsClosed ((𝓡∂ (n + 1)).boundary M) := isClosed_bnd (n := n + 1) (M := M)
  have hcN : IsClosed ((𝓡∂ (n + 1)).boundary N) := isClosed_bnd (n := n + 1) (M := N)
  exact D.exists_sep_of_data (U1 := ((𝓡∂ (n + 1)).boundary M)ᶜ) (U2 := ∅)
    (V1 := ∅) (V2 := ((𝓡∂ (n + 1)).boundary N)ᶜ)
    hcM.isOpen_compl isOpen_empty isOpen_empty hcN.isOpen_compl
    (D.match_empty (fun z hz => hz)) (D.match_empty_right (fun z hz => hz))
    (by rw [Set.disjoint_left]; rintro z hz; exact Set.notMem_empty z)
    (by rw [Set.disjoint_left]; rintro z hz; exact absurd hz (Set.notMem_empty z))
    (Or.inl ⟨x, hx, rfl⟩) (Or.inr ⟨y, hy, rfl⟩)

/-- An interior point of `M` and a seam point (given on the `M`-side). -/
theorem GlueData.sep_M_seam {x : M}
    (hx : x ∉ (𝓡∂ (n + 1)).boundary M) (p : (𝓡∂ (n + 1)).boundary M) :
    ∃ G1 G2 : Set D.Glued, IsOpen G1 ∧ IsOpen G2 ∧
      D.ιM x ∈ G1 ∧ D.ιM p.1 ∈ G2 ∧ Disjoint G1 G2 := by
  have hcM : IsClosed ((𝓡∂ (n + 1)).boundary M) := isClosed_bnd (n := n + 1) (M := M)
  have hxp : x ≠ p.1 := fun h => hx (h ▸ p.2)
  obtain ⟨U1, U2, hU1, hU2, hxU1, hpU2, hdU⟩ := t2_separation hxp
  obtain ⟨V2, hV2, hm2⟩ := D.exists_match hU2
  exact D.exists_sep_of_data (U1 := U1 ∩ ((𝓡∂ (n + 1)).boundary M)ᶜ) (U2 := U2)
    (V1 := ∅) (V2 := V2)
    (hU1.inter hcM.isOpen_compl) hU2 isOpen_empty hV2
    (D.match_empty (fun z hz => hz.2)) hm2
    (Disjoint.mono inter_subset_left le_rfl hdU)
    (by rw [Set.disjoint_left]; rintro z hz; exact absurd hz (Set.notMem_empty z))
    (Or.inl ⟨x, ⟨hxU1, hx⟩, rfl⟩) (Or.inl ⟨p.1, hpU2, rfl⟩)

/-- An interior point of `N` and a seam point (given on the `M`-side). -/
theorem GlueData.sep_N_seam {y : N}
    (hy : y ∉ (𝓡∂ (n + 1)).boundary N) (p : (𝓡∂ (n + 1)).boundary M) :
    ∃ G1 G2 : Set D.Glued, IsOpen G1 ∧ IsOpen G2 ∧
      D.ιN y ∈ G1 ∧ D.ιM p.1 ∈ G2 ∧ Disjoint G1 G2 := by
  have hcN : IsClosed ((𝓡∂ (n + 1)).boundary N) := isClosed_bnd (n := n + 1) (M := N)
  have hyφp : y ≠ (D.φ p).1 := fun h => hy (h ▸ (D.φ p).2)
  obtain ⟨V1, W, hV1, hW, hyV1, hφpW, hdW⟩ := t2_separation hyφp
  have hs : IsOpen (Subtype.val ⁻¹' W : Set ((𝓡∂ (n + 1)).boundary N)) :=
    hW.preimage continuous_subtype_val
  have hs' : IsOpen (D.φ.symm '' (Subtype.val ⁻¹' W) : Set ((𝓡∂ (n + 1)).boundary M)) :=
    D.φ.symm.isOpenMap _ hs
  obtain ⟨U2, hU2, hU2key⟩ := exists_isOpen_inter_boundary (n := n) (X := M)
    (D.φ.symm '' (Subtype.val ⁻¹' W)) hs'
  obtain ⟨V2', hV2', hV2'key⟩ := exists_isOpen_inter_boundary (n := n) (X := N)
    (D.φ '' (Subtype.val ⁻¹' U2)) (D.φ.isOpenMap _ (hU2.preimage continuous_subtype_val))
  have hm2 : D.Match U2 (V2' ∩ W) := by
    constructor
    · intro x hx
      refine ⟨(hV2'key (D.φ x)).mpr ⟨x, hx, rfl⟩, ?_⟩
      obtain ⟨z, hz, hzx⟩ := (hU2key x).mp hx
      have hφxz : D.φ x = z := by rw [← hzx, D.φ.apply_symm_apply]
      rw [hφxz]; exact hz
    · intro y' hy'
      obtain ⟨x, hx, hxy⟩ := (hV2'key y').mp hy'.1
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
  exact D.exists_sep_of_data (U1 := ∅) (U2 := U2)
    (V1 := V1 ∩ ((𝓡∂ (n + 1)).boundary N)ᶜ) (V2 := V2' ∩ W)
    isOpen_empty hU2 (hV1.inter hcN.isOpen_compl) (hV2'.inter hW)
    (D.match_empty_right (fun z hz => hz.2)) hm2
    (by rw [Set.disjoint_left]; rintro z hz; exact absurd hz (Set.notMem_empty z))
    (Disjoint.mono inter_subset_left inter_subset_right hdW)
    (Or.inr ⟨y, ⟨hyV1, hy⟩, rfl⟩)
    (Or.inl ⟨p.1, (hU2key p).mpr ⟨D.φ p, hφpW, D.φ.symm_apply_apply p⟩, rfl⟩)

/-- Two seam points. -/
theorem GlueData.sep_seam_seam {p1 p2 : (𝓡∂ (n + 1)).boundary M} (h : p1 ≠ p2) :
    ∃ G1 G2 : Set D.Glued, IsOpen G1 ∧ IsOpen G2 ∧
      D.ιM p1.1 ∈ G1 ∧ D.ιM p2.1 ∈ G2 ∧ Disjoint G1 G2 := by
  haveI : LocallyCompactSpace ((𝓡∂ (n + 1)).boundary M) :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary M)
  obtain ⟨u1, u2, hu1, hu2, hc1, hc2, hdu⟩ :=
    t2_separation_compact_nhds (X := (𝓡∂ (n + 1)).boundary M) h
  -- separation of the corresponding parts of `M`
  have hM1c : IsCompact (Subtype.val '' u1 : Set M) := hc1.image continuous_subtype_val
  have hM2c : IsCompact (Subtype.val '' u2 : Set M) := hc2.image continuous_subtype_val
  have hMdisj : Disjoint (Subtype.val '' u1 : Set M) (Subtype.val '' u2) := by
    rw [Set.disjoint_left]
    rintro z ⟨a, ha, haz⟩ ⟨b, hb, hbz⟩
    have hab : a = b := Subtype.val_injective (haz.trans hbz.symm)
    exact (Set.disjoint_left.mp hdu) ha (hab.symm ▸ hb)
  obtain ⟨P1, P2, hP1, hP2, hMP1, hMP2, hPd⟩ :=
    SeparatedNhds.of_isCompact_isCompact_isClosed hM1c hM2c hM2c.isClosed hMdisj
  obtain ⟨U1', hU1', hU1'key⟩ := exists_isOpen_inter_boundary (n := n) (X := M)
    (interior u1) isOpen_interior
  obtain ⟨U2', hU2', hU2'key⟩ := exists_isOpen_inter_boundary (n := n) (X := M)
    (interior u2) isOpen_interior
  -- separation on the `N` side
  have hK1c : IsCompact (Subtype.val '' (D.φ '' u1) : Set N) :=
    (hc1.image D.φ.continuous).image continuous_subtype_val
  have hK2c : IsCompact (Subtype.val '' (D.φ '' u2) : Set N) :=
    (hc2.image D.φ.continuous).image continuous_subtype_val
  have hKdisj : Disjoint (Subtype.val '' (D.φ '' u1) : Set N)
      (Subtype.val '' (D.φ '' u2)) := by
    rw [Set.disjoint_left]
    rintro z ⟨a, ⟨x, hx, hxa⟩, haz⟩ ⟨b, ⟨x', hx', hxb⟩, hbz⟩
    have hφ : D.φ x = D.φ x' := by
      refine Subtype.ext ?_
      rw [show (D.φ x).1 = a.1 from congrArg Subtype.val hxa, haz, ← hbz,
        ← congrArg Subtype.val hxb]
    have hxx : x = x' := D.φ.injective hφ
    exact (Set.disjoint_left.mp hdu) (hxx ▸ hx) hx'
  have hW1 : (Subtype.val '' (D.φ '' interior u1) : Set N) ⊆ Subtype.val '' (D.φ '' u1) :=
    Set.image_mono (Set.image_mono interior_subset)
  have hW2 : (Subtype.val '' (D.φ '' interior u2) : Set N) ⊆ Subtype.val '' (D.φ '' u2) :=
    Set.image_mono (Set.image_mono interior_subset)
  have hW1c : IsCompact (closure (Subtype.val '' (D.φ '' interior u1) : Set N)) :=
    hK1c.closure_of_subset hW1
  have hW2c : IsCompact (closure (Subtype.val '' (D.φ '' interior u2) : Set N)) :=
    hK2c.closure_of_subset hW2
  have hWdisj : Disjoint (closure (Subtype.val '' (D.φ '' interior u1) : Set N))
      (closure (Subtype.val '' (D.φ '' interior u2) : Set N)) :=
    Disjoint.mono (closure_minimal hW1 hK1c.isClosed) (closure_minimal hW2 hK2c.isClosed) hKdisj
  obtain ⟨O1, O2, hO1, hO2, hWO1, hWO2, hOd⟩ :=
    SeparatedNhds.of_isCompact_isCompact_isClosed hW1c hW2c isClosed_closure hWdisj
  obtain ⟨V1', hV1', hV1'key⟩ := exists_isOpen_inter_boundary (n := n) (X := N)
    (D.φ '' (interior u1)) (D.φ.isOpenMap _ isOpen_interior)
  obtain ⟨V2', hV2', hV2'key⟩ := exists_isOpen_inter_boundary (n := n) (X := N)
    (D.φ '' (interior u2)) (D.φ.isOpenMap _ isOpen_interior)
  have hm1 : D.Match (U1' ∩ P1) (V1' ∩ O1) := by
    constructor
    · intro x hx
      refine ⟨(hV1'key (D.φ x)).mpr ⟨x, (hU1'key x).mp hx.1, rfl⟩, ?_⟩
      exact hWO1 (subset_closure ⟨D.φ x, ⟨x, (hU1'key x).mp hx.1, rfl⟩, rfl⟩)
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := (hV1'key y).mp hy.1
      exact ⟨x, ⟨(hU1'key x).mpr hx, hMP1 ⟨x, interior_subset hx, rfl⟩⟩, congrArg Subtype.val hxy⟩
  have hm2 : D.Match (U2' ∩ P2) (V2' ∩ O2) := by
    constructor
    · intro x hx
      refine ⟨(hV2'key (D.φ x)).mpr ⟨x, (hU2'key x).mp hx.1, rfl⟩, ?_⟩
      exact hWO2 (subset_closure ⟨D.φ x, ⟨x, (hU2'key x).mp hx.1, rfl⟩, rfl⟩)
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := (hV2'key y).mp hy.1
      exact ⟨x, ⟨(hU2'key x).mpr hx, hMP2 ⟨x, interior_subset hx, rfl⟩⟩, congrArg Subtype.val hxy⟩
  have hp1int : p1 ∈ interior u1 := mem_interior_iff_mem_nhds.mpr hu1
  have hp2int : p2 ∈ interior u2 := mem_interior_iff_mem_nhds.mpr hu2
  exact D.exists_sep_of_data (U1 := U1' ∩ P1) (U2 := U2' ∩ P2)
    (V1 := V1' ∩ O1) (V2 := V2' ∩ O2)
    (hU1'.inter hP1) (hU2'.inter hP2) (hV1'.inter hO1) (hV2'.inter hO2)
    hm1 hm2 (Disjoint.mono inter_subset_right inter_subset_right hPd)
    (Disjoint.mono inter_subset_right inter_subset_right hOd)
    (Or.inl ⟨p1.1, ⟨(hU1'key p1).mpr hp1int, hMP1 ⟨p1, interior_subset hp1int, rfl⟩⟩, rfl⟩)
    (Or.inl ⟨p2.1, ⟨(hU2'key p2).mpr hp2int, hMP2 ⟨p2, interior_subset hp2int, rfl⟩⟩, rfl⟩)

/-- Separation of the images of two distinct points of `M ⊕ N`. -/
theorem GlueData.exists_sep_reps {a1 a2 : M ⊕ N} (h : D.q a1 ≠ D.q a2) :
    ∃ G1 G2 : Set D.Glued, IsOpen G1 ∧ IsOpen G2 ∧ D.q a1 ∈ G1 ∧ D.q a2 ∈ G2 ∧
      Disjoint G1 G2 := by
  rcases a1 with x1 | y1 <;> rcases a2 with x2 | y2 <;>
    simp only [q_inl, q_inr] at h ⊢
  · by_cases hx1 : x1 ∈ (𝓡∂ (n + 1)).boundary M
    · by_cases hx2 : x2 ∈ (𝓡∂ (n + 1)).boundary M
      · have hp : (⟨x1, hx1⟩ : (𝓡∂ (n + 1)).boundary M) ≠ ⟨x2, hx2⟩ :=
          fun hh => h (by
            have h12 : x1 = x2 := Subtype.ext_iff.mp hh
            rw [h12])
        exact D.sep_seam_seam hp
      · exact D.sep_symm (D.sep_M_seam hx2 ⟨x1, hx1⟩)
    · by_cases hx2 : x2 ∈ (𝓡∂ (n + 1)).boundary M
      · exact D.sep_M_seam hx1 ⟨x2, hx2⟩
      · exact D.sep_M_M hx1 hx2 (fun hh => h (by rw [hh]))
  · by_cases hx1 : x1 ∈ (𝓡∂ (n + 1)).boundary M
    · by_cases hy2 : y2 ∈ (𝓡∂ (n + 1)).boundary N
      · have hp : (⟨x1, hx1⟩ : (𝓡∂ (n + 1)).boundary M) ≠ D.φ.symm ⟨y2, hy2⟩ :=
          fun hh => h (by
            have h12 : x1 = (D.φ.symm ⟨y2, hy2⟩).1 := Subtype.ext_iff.mp hh
            rw [h12, D.iotaM_phi_symm ⟨y2, hy2⟩])
        obtain ⟨G1, G2, h1, h2, hq1, hq2, hd⟩ := D.sep_seam_seam hp
        exact ⟨G1, G2, h1, h2, hq1, D.iotaM_phi_symm ⟨y2, hy2⟩ ▸ hq2, hd⟩
      · exact D.sep_symm (D.sep_N_seam hy2 ⟨x1, hx1⟩)
    · by_cases hy2 : y2 ∈ (𝓡∂ (n + 1)).boundary N
      · obtain ⟨G1, G2, h1, h2, hq1, hq2, hd⟩ := D.sep_M_seam hx1 (D.φ.symm ⟨y2, hy2⟩)
        exact ⟨G1, G2, h1, h2, hq1, D.iotaM_phi_symm ⟨y2, hy2⟩ ▸ hq2, hd⟩
      · exact D.sep_M_N hx1 hy2
  · by_cases hy1 : y1 ∈ (𝓡∂ (n + 1)).boundary N
    · by_cases hx2 : x2 ∈ (𝓡∂ (n + 1)).boundary M
      · have hp : D.φ.symm (⟨y1, hy1⟩ : (𝓡∂ (n + 1)).boundary N) ≠ ⟨x2, hx2⟩ :=
          fun hh => h (by rw [← D.iotaM_phi_symm ⟨y1, hy1⟩, Subtype.ext_iff.mp hh])
        obtain ⟨G1, G2, h1, h2, hq1, hq2, hd⟩ := D.sep_seam_seam hp
        exact ⟨G1, G2, h1, h2, D.iotaM_phi_symm ⟨y1, hy1⟩ ▸ hq1, hq2, hd⟩
      · obtain ⟨G1, G2, h1, h2, hq1, hq2, hd⟩ := D.sep_M_seam hx2 (D.φ.symm ⟨y1, hy1⟩)
        exact ⟨G2, G1, h2, h1, D.iotaM_phi_symm ⟨y1, hy1⟩ ▸ hq2, hq1, hd.symm⟩
    · by_cases hx2 : x2 ∈ (𝓡∂ (n + 1)).boundary M
      · exact D.sep_N_seam hy1 ⟨x2, hx2⟩
      · exact D.sep_symm (D.sep_M_N hx2 hy1)
  · by_cases hy1 : y1 ∈ (𝓡∂ (n + 1)).boundary N
    · by_cases hy2 : y2 ∈ (𝓡∂ (n + 1)).boundary N
      · have hp : D.φ.symm (⟨y1, hy1⟩ : (𝓡∂ (n + 1)).boundary N) ≠ D.φ.symm ⟨y2, hy2⟩ := by
          intro hh
          refine h ?_
          rw [← D.iotaM_phi_symm ⟨y1, hy1⟩, congrArg (fun p => D.ιM p.1) hh,
            D.iotaM_phi_symm ⟨y2, hy2⟩]
        obtain ⟨G1, G2, h1, h2, hq1, hq2, hd⟩ := D.sep_seam_seam hp
        exact ⟨G1, G2, h1, h2, D.iotaM_phi_symm ⟨y1, hy1⟩ ▸ hq1,
          D.iotaM_phi_symm ⟨y2, hy2⟩ ▸ hq2, hd⟩
      · obtain ⟨G1, G2, h1, h2, hq1, hq2, hd⟩ := D.sep_N_seam hy2 (D.φ.symm ⟨y1, hy1⟩)
        exact ⟨G2, G1, h2, h1, D.iotaM_phi_symm ⟨y1, hy1⟩ ▸ hq2, hq1, hd.symm⟩
    · by_cases hy2 : y2 ∈ (𝓡∂ (n + 1)).boundary N
      · obtain ⟨G1, G2, h1, h2, hq1, hq2, hd⟩ := D.sep_N_seam hy1 (D.φ.symm ⟨y2, hy2⟩)
        exact ⟨G1, G2, h1, h2, hq1, D.iotaM_phi_symm ⟨y2, hy2⟩ ▸ hq2, hd⟩
      · exact D.sep_N_N hy1 hy2 (fun hh => h (by rw [hh]))

end Helpers

/-- **The glued space is Hausdorff** when both pieces are.  The smooth-manifold hypothesis is used
only to know that the boundary is closed in `M` and in `N` (`Work.Surgery.isClosed_bnd`); without it
the statement is false (the "line with two origins").  The proof uses the *local flatness* of the
boundary, i.e. chart-based neighbourhoods of the seam; `Work.Surgery.isEmbedding_ιM`,
`Work.Surgery.isEmbedding_ιN`, `Work.Surgery.GlueData.isOpenMap_interior_ιM`,
`GlueData.isOpenMap_interior_ιN` and `Work.Surgery.exists_isOpen_inter_boundary` (all in
`Submission/Work/Surgery/GluingPointSet.lean`) are available and are exactly the tools for the
saturated-neighbourhood argument. -/
theorem glue_t2Space (n : ℕ) {M N : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (halfModel (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace (n + 1)) N]
    [IsManifold (halfModel (n + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) N] [T2Space N]
    (D : GlueData n M N) : T2Space D.Glued := by
  rw [t2Space_iff]
  intro z1 z2 hne
  obtain ⟨a1, rfl⟩ := Quotient.exists_rep z1
  obtain ⟨a2, rfl⟩ := Quotient.exists_rep z2
  exact GlueData.exists_sep_reps D hne

end

end Work.Surgery
